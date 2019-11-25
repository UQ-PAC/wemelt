package tool

trait Expression extends beaver.Symbol {

  def variables: Set[Id]
  def subst(su: Subst): Expression
  def arrays: Set[Access]

  // existentially quantify (substitute with fresh variables) all variables that aren't in restricted
  def restrict(restricted: Set[Id]): Expression = {
    // get variables that aren't in restricted
    val toSubst = for (v <- variables if !restricted.contains(v))
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
  override def toString = arg.toString
  override def variables: Set[Id] = Set()
  override def arrays = Set()
  override def subst(su: Subst): Lit = this
}

// id parsed from input - need to convert to Var before use in predicates etc.
case class Id(name: String) extends Expression {
  //override def toString = "ID_" + name
  override def toString = name
  override def variables: Set[Id] = Set(this)
  override def subst(su: Subst): Expression = su.getOrElse(this, this)
  def toVar = Var(name, None)
  override def arrays = Set()
}

// array access parsed from input
case class Access(name: Id, index: Expression) extends Expression {
  def this (name: String, index: Expression) = this(Id(name), index)
  def variables: Set[Id] = name.variables ++ index.variables
  def subst(su: Subst) = Access(name, index.subst(su))
  override def toString = name + "[" + index + "]"
  override def arrays = Set(this)
}

// array access with Var for use in logical predicates
case class VarAccess(name: Var, index: Expression) extends Expression {
  def variables: Set[Id] = name.variables ++ index.variables
  def subst(su: Subst) = VarAccess(name, index.subst(su))
  override def toString = name + "[" + index + "]"
  override def arrays = Set()
}

// logical variable for use in predicates
case class Var(name: String, index: Option[Int] = None) extends Expression {
  def this(name: String) = this(name, None)

  def ident = Id(name)

  def fresh = Var.fresh(name)

  // replaces the Var with the value it is to be substituted with, if there is one
  override def subst(su: Subst): Var = su.getOrElse(this, this)

  // only return free variables
  override def variables: Set[Id] = this match {
    case Var(name, Some(index)) =>
      Set()
    case Var(name, None) =>
      Set(ident)
  }

  override def toString = name __ index
  //override def toString = "VAR_" + name __ index

  override def arrays = Set()
}

object Var {
  var index = 0
  def fresh(name: String) = {
    index += 1
    Var(name, Some(index))
  }
}

case class IdArray(name: Id, array: IndexedSeq[Id])

object IdArray {
  def apply(name: Id, size: Int): IdArray = {
    val array = for (i <- 0 until size)
      yield Id(name.toString.arrayIndex(i))
    this(name, array)
  }
}


// switching logical variable for CNF format
case class Switch(index: Int) extends Expression {
  def variables: Set[Id] = Set()
  def subst(su: Subst): Expression = this
  override def arrays = Set()
}

object Switch {
  var index = 0
  def fresh = {
    index += 1
    Switch(index)
  }
}

case class PreOp(op: String, arg: Expression) extends Expression {
  override def toString = "(" + op + " " + arg + ")"
  override def variables: Set[Id] = arg.variables
  def subst(su: Subst) =  PreOp(op, arg.subst(su))
  override def arrays = arg.arrays

}

case class PostOp(op: String, arg: Expression) extends Expression {
  override def toString = "(" + arg + " " + op + ")"
  override def variables: Set[Id] = arg.variables
  def subst(su: Subst) = PostOp(op, arg.subst(su))
  override def arrays = arg.arrays
}

case class BinOp(op: String, arg1: Expression, arg2: Expression) extends Expression {
  override def toString = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def variables: Set[Id] = arg1.variables ++ arg2.variables
  def subst(su: Subst) = BinOp(op, arg1.subst(su), arg2.subst(su))
  override def arrays = arg1.arrays ++ arg2.arrays
}

object Const {
  object _true extends Const("True")
  object _false extends Const("False")
}

case class Const(name: String) extends Expression {
  override def toString = name.toString
  override def variables: Set[Id] = Set()
  override def subst(su: Subst): Const = this
  override def arrays = Set()
}