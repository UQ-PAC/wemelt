package tool

object Block {
  def empty = Block(Nil)
}

sealed trait Statement extends beaver.Symbol {

}

case object Malformed extends Statement {
  def self = this
}

case class Block(statements: List[Statement]) extends Statement {
  def this(statements: Array[Statement]) = this(statements.toList)
}

case class Atomic(expression: Expression) extends Statement {
}

case class Assignment(lhs: Id, expression: Expression) extends Statement {
  def this(lhs: String, expression: Expression) = this(Id(lhs), expression)
}

/*
case object Break extends Statement {
  def self = this
}

case object Continue extends Statement {
  def self = this
}

case class Return(expression: Option[Expression]) extends Statement {
  def this(expression: Expression) = this(Some(expression))
}

object Return extends (Option[Expression] => Return) {
  val none = Return(None)
}
 */

case object Fence extends Statement {
  def self = this
}

case class If(test: Expression, left: Statement, right: Option[Statement]) extends Statement {
  def this(test: Expression, left: Statement) = this(test, left, None)
  def this(test: Expression, left: Statement, right: Statement) = this(test, left, Some(right))
}

case class While(test: Expression, invariant: List[Expression], gamma: List[Expression], body: Statement) extends Statement {
  def this(test: Expression, invariant: Array[Expression], gamma: Array[Expression], body: Statement) = this(test, invariant.toList, gamma.toList, body)
}