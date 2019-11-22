package tool

object Block {
  def empty = Block(Nil)
}

sealed trait Statement extends beaver.Symbol {
  def line: Int = beaver.Symbol.getLine(this.getStart())
}

case object Malformed extends Statement {
  def self = this
}

case class Block(statements: List[Statement]) extends Statement {
  def this(statements: Array[Statement]) = this(statements.toList)
}

case class Assignment(lhs: Id, expression: Expression) extends Statement {
  def this(lhs: String, expression: Expression) = this(Id(lhs), expression)
  override def toString = lhs + " = " + expression
}

case class ArrayAssignment(lhs: Id, index: Expression, expression: Expression) extends Statement {
  override def toString = lhs + "[" + index + "]" + " = " + expression
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

case class While(test: Expression, invariant: List[Expression], gamma: List[GammaMapping], nonblocking: Option[Id], body: Statement) extends Statement {
  def this(test: Expression, invariant: Array[Expression], gamma: Array[GammaMapping], body: Statement) = this(test, invariant.toList, gamma.toList, None, body)
  def this(test: Expression, invariant: Array[Expression], gamma: Array[GammaMapping], nonblocking: String, body: Statement) = this(test, invariant.toList, gamma.toList, Some(Id(nonblocking)), body)
}

case class DoWhile(test: Expression, invariant: List[Expression], gamma: List[GammaMapping], nonblocking: Option[Id], body: Statement) extends Statement {
  def this(test: Expression, invariant: Array[Expression], gamma: Array[GammaMapping], body: Statement) = this(test, invariant.toList, gamma.toList, None, body)
  def this(test: Expression, invariant: Array[Expression], gamma: Array[GammaMapping], nonblocking: String, body: Statement) = this(test, invariant.toList, gamma.toList, Some(Id(nonblocking)), body)
}