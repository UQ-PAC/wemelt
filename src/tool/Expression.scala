package tool

case class Field(typ: Type, name: String) extends beaver.Symbol {
  override def toString = typ + " " + name
}

case class Param(typ: Type, name: String) extends beaver.Symbol {
  override def toString = typ + " " + name
}

trait Expression extends beaver.Symbol {
    def getVariables: Set[Id]
}

case class Lit(arg: Any) extends Expression {
  override def toString = arg.toString
  override def getVariables: Set[Id] = Set()
}

case class Id(name: String) extends Expression {
  override def toString = name
  override def getVariables: Set[Id] = Set(this)
}

object Id {
  val result = Id("result")
  val main = Id("main")
}

case class PreOp(op: String, arg: Expression) extends Expression {
  override def toString = "(" + op + " " + arg + ")"
  override def getVariables: Set[Id] = arg.getVariables
}

case class PostOp(op: String, arg: Expression) extends Expression {
  override def toString = "(" + arg + " " + op + ")"
  override def getVariables: Set[Id] = arg.getVariables
}

case class BinOp(op: String, arg1: Expression, arg2: Expression) extends Expression {
  override def toString = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def getVariables: Set[Id] = arg1.getVariables ++ arg2.getVariables
}

case class Question(test: Expression, left: Expression, right: Expression) extends Expression {
  override def toString = "(" + test + " ? " + left + " : " + right + ")"
  override def getVariables: Set[Id] = test.getVariables ++ left.getVariables ++ right.getVariables
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

  override def getVariables: Set[Id] = Set()
}

case class Init(values: List[(Option[String], Expression)]) extends Expression { // { .field = value } or { value }
  override def getVariables: Set[Id] = Set()
}

/*

} */