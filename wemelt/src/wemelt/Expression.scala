package wemelt

trait Expression extends beaver.Symbol {

  def variables: Set[Var] // returns all variables in the expression, does NOT include array indices
  def subst(su: Subst): Expression
  //def subst(su: Subst, num: Int): Expression
  //def arrays: Set[Access] // returns all array accesses in the expression

  // existentially quantify (substitute with fresh variables) all variables that aren't in restricted
  def restrict(restricted: Set[Var]): Expression = {
    // get variables that aren't in restricted
    val toSubst = for (v <- variables if !restricted.contains(v))
      yield v

    // if no variables need to be bound then predicate stays the same
    if (toSubst.isEmpty) {
      this
    } else {
      // create mapping from variables to be substituted with their fresh versions
      val toSubstFresh: Subst = (toSubst map (x => x -> Var.fresh(x.name, x.size))).toMap
      this.subst(toSubstFresh)
    }
  }

}

trait BoolExpression extends Expression {
  def subst(su: Subst): BoolExpression
  //def subst(su: Subst, num: Int): BoolExpression
}

case class Lit(arg: Int) extends Expression {
  override def toString: String = arg.toString
  override def variables: Set[Var] = Set()
  //override def arrays = Set()
  override def subst(su: Subst): Lit = this
  //override def subst(su: Subst, num: Int): Lit = this.subst(su)
}

/*
// id parsed from input - need to convert to Var before use in predicates etc.
case class Id(name: String) extends Expression {
  //override def toString = "ID_" + name
  override def toString: String = name
  override def variables: Set[Id] = Set(this)
  override def subst(su: Subst): Expression = su.getOrElse(this, this)
  //override def subst(su: Subst, num: Int): Expression = this.subst(su)
  def toVar: Var = Var(name, None)
  //override def arrays = Set()
  def prime: Id = Id(name + "'")
}
*/

object CFence extends Var("cfence", 0)
/*
// array access parsed from input
case class Access(name: Id, index: Expression) extends Expression {
  def this (name: String, index: Expression) = this(Id(name), index)
  def variables: Set[Id] = index.variables
  def subst(su: Subst): Expression = su.getOrElse(name, name) match {
    case v: Var =>
      VarAccess(v, index.subst(su))
    case _ =>
      Access(name, index.subst(su))
  }
  def subst(su: Subst, num: Int): Expression = su.getOrElse(name, name) match {
    case v: Var =>
      VarAccess(v, index.subst(su))
    case _ =>
      Access(name, index.subst(su))
  }
  override def toString: String = name + "[" + index + "]"
  override def arrays = Set(this)
}
 */

// array access with Var for use in logical predicates
/*
case class VarAccess(name: Var, index: Expression) extends Expression {
  def variables: Set[Id] = index.variables
  def subst(su: Subst): Expression = if (su.keySet.contains(this)) {
    su.getOrElse(this, this)
  } else {
    VarAccess(name.subst(su), index.subst(su))
  }

  // don't substitute in the case that the index expression is an integer but not the one specified
  override def subst(su: Subst, num: Int): VarAccess = index match {
    case Lit(n) if n != num =>
      VarAccess(name, index)
    case _ =>
      VarAccess(name.subst(su), index.subst(su))
  }
  //override def toString = name + "[" + index + "]"
  override def arrays: Set[Access] = this.name match {
    case Var(_, Some(index)) =>
      Set()
    case Var(_, None) =>
      Set(Access(name.ident, index))
  }
}
 */

case class Id(id: String) extends Var(id, 0, None) {
  override def subst(su: Subst): Expression = su.getOrElse(this, this)
  override def variables: Set[Var] = Set()
}

// logical variable for use in predicates
case class Var(name: String, size: Int, index: Option[Int] = None) extends Expression {
  def this(name: String, size: Int) = this(name, size, None)

  def fresh: Var = Var.fresh(name, size)

  def prime: Var = Var(name.prime, size, index)

  // replaces the Var with the value it is to be substituted with, if there is one
  override def subst(su: Subst): Expression = su.getOrElse(this, this)
  //override def subst(su: Subst, num: Int): Expression = su.getOrElse(this, this)

  // only return free variables
  override def variables: Set[Var] = this match {
    case Var(_, _, Some(_)) =>
      Set()
    case Var(_, _, None) =>
      Set(this)
  }

  override def toString: String = name __ index
  //override def toString = "VAR_" + name __ index

  //override def arrays = Set()
}

object Var {
  var index = 0
  def fresh(name: String, size: Int):Var = {
    index += 1
    Var(name, size, Some(index))
  }
}

// switching logical variable for CNF format
case class Switch(index: Int) extends BoolExpression {
  def variables: Set[Var] = Set()
  def subst(su: Subst): BoolExpression = this
  //def subst(su: Subst, num: Int): BoolExpression = this
  //override def arrays = Set()
}

object Switch {
  var index = 1
  def fresh: Switch = {
    index += 1
    Switch(index)
  }
}

case class MultiSwitch(index: Int) extends Expression {
  def variables: Set[Var] = Set()
  def subst(su: Subst): Expression = this
  //def subst(su: Subst, num: Int): Expression = this
  //override def arrays = Set()
}

object MultiSwitch {
  var index = 0
  def fresh:MultiSwitch = {
    index += 1
    MultiSwitch(index)
  }
}

/*
case class not(arg: BoolExpression) extends BoolExpression {
  override def toString = "(! " + arg + ")"
  override def variables: Set[Id] = arg.variables
  def subst(su: Subst) = not(arg.subst(su))
  def subst(su: Subst, num: Int) =  not(arg.subst(su, num))
  override def arrays = arg.arrays
}

case class and(arg1: BoolExpression, arg2: BoolExpression) extends BoolExpression {
  override def toString = "(" + arg1 + " && " + arg2 + ")"
  override def variables: Set[Id] = arg1.variables ++ arg2.variables
  def subst(su: Subst) = and(arg1.subst(su), arg2.subst(su))
  def subst(su: Subst, num: Int) = and(arg1.subst(su, num), arg2.subst(su, num))
  override def arrays = arg1.arrays ++ arg2.arrays
}

case class or(arg1: BoolExpression, arg2: BoolExpression) extends BoolExpression {
  override def toString = "(" + arg1 + " && " + arg2 + ")"
  override def variables: Set[Id] = arg1.variables ++ arg2.variables
  def subst(su: Subst) = or(arg1.subst(su), arg2.subst(su))
  def subst(su: Subst, num: Int) = or(arg1.subst(su, num), arg2.subst(su, num))
  override def arrays = arg1.arrays ++ arg2.arrays
}

case class eq(arg1: Expression, arg2: Expression) extends BoolExpression {
  override def toString = "(" + arg1 + " && " + arg2 + ")"
  override def variables: Set[Id] = arg1.variables ++ arg2.variables
  def subst(su: Subst) = eq(arg1.subst(su), arg2.subst(su))
  def subst(su: Subst, num: Int) = eq(arg1.subst(su, num), arg2.subst(su, num))
  override def arrays = arg1.arrays ++ arg2.arrays
}
 */

case class PreOp(op: String, arg: Expression) extends Expression {
  override def toString: String = "(" + op + " " + arg + ")"
  override def variables: Set[Var] = arg.variables
  def subst(su: Subst) =  PreOp(op, arg.subst(su))
  //def subst(su: Subst, num: Int) =  PreOp(op, arg.subst(su, num))
  //override def arrays: Set[Access] = arg.arrays
}

case class PostOp(op: String, arg: Expression) extends Expression {
  override def toString: String = "(" + arg + " " + op + ")"
  override def variables: Set[Var] = arg.variables
  def subst(su: Subst) = PostOp(op, arg.subst(su))
  //def subst(su: Subst, num: Int) =  PostOp(op, arg.subst(su, num))
  //override def arrays: Set[Access] = arg.arrays
}

case class BinOp(op: String, arg1: Expression, arg2: Expression) extends Expression {
  override def toString: String = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def variables: Set[Var] = arg1.variables ++ arg2.variables
  def subst(su: Subst) = BinOp(op, arg1.subst(su), arg2.subst(su))
  //def subst(su: Subst, num: Int) = BinOp(op, arg1.subst(su, num), arg2.subst(su, num))
  //override def arrays: Set[Access] = arg1.arrays ++ arg2.arrays
}

case class Question(test: Expression, left: Expression, right: Expression) extends Expression {
  override def toString: String = "(" + test + " ? " + left + " : " + right + ")"
  override def variables: Set[Var] = test.variables ++ left.variables ++ right.variables
  def subst(su: Subst) = Question(test.subst(su), left.subst(su), right.subst(su))
  //def subst(su: Subst, num: Int) = Question(test.subst(su, num), left.subst(su, num), right.subst(su, num))
  //override def arrays: Set[Access] = test.arrays ++ left.arrays ++ right.arrays
}

case class ForAll(bound: Set[_ <: Expression], body: Expression) extends BoolExpression {
  override def variables: Set[Var]  = body.variables -- (bound collect {case x: Var => x})
  def subst(su: Subst) = ForAll(bound map (b => b.subst(su)), body.subst(su))
  //def subst(su: Subst, num: Int) = ForAll(bound, body.subst(su, num))
  //override def arrays: Set[Access] = body.arrays
}

case class Exists(bound: Set[_ <: Expression], body: Expression) extends BoolExpression {
  override def variables: Set[Var] = body.variables -- (bound collect {case x: Var => x})
  def subst(su: Subst) = Exists(bound map (b => b.subst(su)), body.subst(su))
  //def subst(su: Subst, num: Int) = Exists(bound, body.subst(su, num))
  //override def arrays: Set[Access] = body.arrays
}

object Const {
  object _true extends Const("True")
  object _false extends Const("False")
}

case class Const(name: String) extends Expression {
  override def variables: Set[Var] = Set()
  override def subst(su: Subst): Const = this
  //override def subst(su: Subst, num: Int): Const = this
  override def toString: String = this.name
  //override def arrays = Set()
}

case class ExtLow(n: Int, e: Expression) extends Expression {
  override def subst(su: Subst): ExtLow = ExtLow(n, e.subst(su))
  override def variables: Set[Var] = e.variables
}

case class ExtHigh(n: Int, e: Expression) extends Expression {
  override def subst(su: Subst): ExtHigh = ExtHigh(n, e.subst(su))
  override def variables: Set[Var] = e.variables
}

case class ExtSigned(n: Int, e: Expression) extends Expression {
  override def subst(su: Subst): ExtSigned = ExtSigned(n, e.subst(su))
  override def variables: Set[Var] = e.variables
}

case class ExtUnsigned(n: Int, e: Expression) extends Expression {
  override def subst(su: Subst): ExtUnsigned = ExtUnsigned(n, e.subst(su))
  override def variables: Set[Var] = e.variables
}
