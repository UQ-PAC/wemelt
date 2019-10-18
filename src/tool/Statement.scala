package tool

object Block {
  def empty = Block(Nil)
}

sealed trait Statement extends beaver.Symbol {

}

sealed trait Global extends Statement {

}

sealed trait Def extends Global {
}

case object Malformed extends Statement {
  def self = this
}

case class Block(statements: List[Statement]) extends Statement {
  def this(statements: Array[Statement]) = this(statements.toList)
}

case class Atomic(expression: Expression) extends Statement {
}

case object Break extends Statement {
  def self = this
}

case object Continue extends Statement {
  def self = this
}

case object Fence extends Statement {
  def self = this
}

case class Return(expression: Option[Expression]) extends Statement {
  def this(expression: Expression) = this(Some(expression))
}

object Return extends (Option[Expression] => Return) {
  val none = Return(None)
}

case class If(test: Expression, left: Statement, right: Option[Statement]) extends Statement {
  def this(test: Expression, left: Statement) = this(test, left, None)
  def this(test: Expression, left: Statement, right: Statement) = this(test, left, Some(right))
}

case class While(test: Expression, body: Statement) extends Statement {
}

/*
case class TypeDef(typ: Type, name: String) extends Def

case class StructDef(name: String, fields: List[Field]) extends Def {
  def this(name: String, fields: Array[Field]) = this(name, fields.toList)
}

case class UnionDef(name: String, fields: List[Field]) extends Def {
  def this(name: String, fields: Array[Field]) = this(name, fields.toList)
}

case class EnumDef(name: Option[String], cases: List[String]) extends Def {
  def this(cases: Array[String]) = this(None, cases.toList)
  def this(name: String, cases: Array[String]) = this(Some(name), cases.toList)
}

case class StructDecl(name: String) extends Def
case class UnionDecl(name: String) extends Def
case class EnumDecl(name: String) extends Def
 */

case class VarDef(typ: Type, name: Id, init: Option[Expression]) extends Global {
  def this(typ: Type, name: String) = this(typ, Id(name), None)
  def this(typ: Type, name: String, init: Expression) = this(typ, Id(name), Some(init))
}

case class FunDef(ret: Type, name: Id, params: List[Param], body: Option[Statement]) extends Global {
  def this(ret: Type, name: String) = {
    this(ret, Id(name), Nil, None)
  }

  def this(ret: Type, name: String, body: Statement) = {
    this(ret, Id(name), Nil, Some(body))
  }

  def this(ret: Type, name: String, params: Array[Param]) = {
    this(ret, Id(name), params.toList, None)
  }

  def this(ret: Type, name: String, params: Array[Param], body: Statement) = {
    this(ret, Id(name), params.toList, Some(body))
  }
}