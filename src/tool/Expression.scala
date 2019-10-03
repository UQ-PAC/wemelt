package tool

case class Field(typ: Type, name: String) extends beaver.Symbol {
  override def toString = typ + " " + name
}

case class Param(typ: Type, name: String) extends beaver.Symbol {
  def toId = Id(name)
  def toVar = Var(name, None)
  override def toString = typ + " " + name
}

trait Expression extends beaver.Symbol {
}

case class Id(name: String) extends Expression with Loc {
  def free = Set()
  //def norm(st: Stack) = this
  //def subst(su: Subst) = this
  def toVar = Var(name, None)
  override def toString = "" + name
}

case class PreOp(op: String, arg: Expression) extends Expression {
  override def toString = "(" + op + " " + arg + ")"
}

case class PostOp(op: String, arg: Expression) extends Expression {
  override def toString = "(" + arg + " " + op + ")"
}

case class BinOp(op: String, arg1: Expression, arg2: Expression) extends Expression {
  override def toString = "(" + arg1 + " " + op + " " + arg2 + ")"
}

case class Question(test: Expression, left: Expression, right: Expression) extends Expression {
  override def toString = "(" + test + " ? " + left + " : " + right + ")"
}

/*
case class SizeOfType(typ: Type) extends Expression
case class SizeOfExpression(expression: Expression) extends Expression
case class Cast(typ: Type, expression: Expression) extends Expression

case class Arrow(expression: Expression, field: String) extends Expression {
  override def toString = expression + "->" + field
}
 */

case class FunCall(fun: Id, args: List[Expression]) extends Expression { // no function pointers
  def this(name: String, args: Array[Expression]) = this(Id(name), args.toList)
  override def toString = fun + args.mkString("(", ", ", ")")
}

case class Init(values: List[(Option[String], Expression)]) extends Expression // { .field = value } or { value }