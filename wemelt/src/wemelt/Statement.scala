package wemelt

object Block {
  def empty: Block = Block(Nil)
}

sealed trait Statement extends beaver.Symbol {
  def line: Int = beaver.Symbol.getLine(this.getStart)
}

case object Malformed extends Statement {
  def self = this
}

case class Block(statements: List[Statement]) extends Statement {
  def this(statements: Array[Statement]) = this(statements.toList)
}

case class Assignment(lhs: Expression, expression: Expression) extends Statement {
  def this(name: String, expression: Expression) = this(Id(name), expression)
  def this(name: String, size: Int, expression: Expression) = this(Var(name, size, None), expression)
  override def toString: String = lhs + " = " + expression
}

case class Store(index: Expression, rhs: Expression, size: Int) extends Statement {
  def this(index: Expression, rhs: Expression, size: Nat) = this(index, rhs, size match {
    case U32 => 32
    case U64 => 64
    case S32 => 32
    case S64 => 64
  })
  override def toString: String = "mem[" + index + "] = " + rhs
}

/*
case class ArrayAssignment(name: Var, index: Expression, expression: Expression) extends Statement {
  def this(name: String, index: Expression, expression: Expression) = this(Var(name, None, size), index, expression)
  override def toString: String = name + "[" + index + "]" + " = " + expression
}

case class CompareAndSwap(result: Var, toCompare: Var, oldValue: Expression, newValue: Expression) extends Statement {
  def this(result: String, toCompare: String, oldValue: Expression, newValue: Expression) = this(Var(result), Var(toCompare), oldValue, newValue)
  override def toString: String = result + " = " + "CAS(" + toCompare + ", " + oldValue + ", " + newValue + ")"
}
 */

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


 */
case object Return extends Statement {
  val self = this
}


case object Fence extends Statement {
  def self = this
}

case object ControlFence extends Statement {
  def self = this
}

case class If(test: Expression, left: Statement, right: Option[Statement]) extends Statement {
  def this(test: Expression, left: Statement) = this(test, left, None)
  def this(test: Expression, left: Statement, right: Statement) = this(test, left, Some(right))
}

case class While(test: Expression, invariant: List[Expression], gamma: List[GammaMapping], body: Statement) extends Statement {
  def this(test: Expression, invariant: Array[Expression], gamma: Array[GammaMapping], body: Statement) = this(test, invariant.toList, gamma.toList, body)
}

case class DoWhile(test: Expression, invariant: List[Expression], gamma: List[GammaMapping], body: Statement) extends Statement {
  def this(test: Expression, invariant: Array[Expression], gamma: Array[GammaMapping], body: Statement) = this(test, invariant.toList, gamma.toList, body)
}
