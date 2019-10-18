package tool

// to remove
case class Param(typ: Type, name: String) extends beaver.Symbol {
  override def toString = typ + " " + name
}

trait Expression extends beaver.Symbol {

  def getVariables: Set[Id]

  def free: Set[Var]
  def subst(su: Subst): Expression

  // "existentially quantify" (substitute with fresh variables) all variables that aren't in restricted
  def restrict(restricted: Set[Id]): Expression = {
    // get variables that aren't in restricted
    val toSubst = for (v <- getVariables if !restricted.contains(v))
      yield v

    // if no variables need to be bound then predicate stays the same
    if (toSubst.isEmpty) {
      this
    } else {
      // create mapping from variables to be substituted with their fresh versions
      val toSubstFresh: Subst = (toSubst map (x => x.toVar -> Var.fresh(x.name))).toMap
      this.subst(toSubstFresh)
    }
  }

}


case class Lit(arg: Any) extends Expression {
  def free = Set()
  override def toString = arg.toString
  override def getVariables: Set[Id] = Set()
  override def subst(su: Subst) = this
}

case class Id(name: String) extends Expression {
  override def toString = name
  override def getVariables: Set[Id] = Set(this)
  override def subst(su: Subst) = this // maybe throw error here as this shouldn't happen
  def toVar = Var(name, None)
  def free = Set() // maybe throw error here
}

object Id {
  val result = Id("result")
  val main = Id("main")
}

// logical variable for use in P
case class Var(name: String, index: Option[Int] = None) extends Expression {
  def this(name: String) = this(name, None)

  def ident = Id(name)
  def free = Set(this)

  def fresh = Var.fresh(name)

  // replaces the Var with the value it is to be substituted with, if there is one
  def subst(su: Subst) = su.getOrElse(this, this)

  override def getVariables: Set[Id] = this match {
    case Var(name, Some(index)) =>
      Set()
    case Var(name, None) =>
      Set(ident)
  }

  // adjust?
  override def toString = name __ index
}

object Var {
  var index = 0
  // maybe rework so each ID has separate index? not important but might make debugging easier later
  def fresh(name: String) = {
    index += 1
    Var(name, Some(index))
  }
}

case class PreOp(op: String, arg: Expression) extends Expression {
  override def toString = "(" + op + " " + arg + ")"
  override def getVariables: Set[Id] = arg.getVariables
  def free = arg.free
  def subst(su: Subst) =  PreOp(op, arg.subst(su))

}

case class PostOp(op: String, arg: Expression) extends Expression {
  override def toString = "(" + arg + " " + op + ")"
  override def getVariables: Set[Id] = arg.getVariables
  def free = arg.free
  def subst(su: Subst) = PostOp(op, arg.subst(su))
}

case class BinOp(op: String, arg1: Expression, arg2: Expression) extends Expression {
  override def toString = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def getVariables: Set[Id] = arg1.getVariables ++ arg2.getVariables
  def free = arg1.free ++ arg2.free
  def subst(su: Subst) = BinOp(op, arg1.subst(su), arg2.subst(su))
}
