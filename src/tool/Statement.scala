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

/*
case class Ghost(aux: Aux) extends Statement {
}
 */

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

case class DoWhile(body: Statement, test: Expression) extends Statement {
}

case class For(init: Expression, test: Expression, inc: Expression, body: Statement) extends Statement {
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

case class VarDef(typ: Type, name: Id, init: Option[Expression], pred: Predicate, mode: Mode) extends Global {
  def this(typ: Type, name: String, pred: Predicate, mode: Mode) = this(typ, Id(name), None, pred, mode)
  def this(typ: Type, name: String, init: Expression, pred: Predicate, mode: Mode) = this(typ, Id(name), Some(init), pred, mode)
  def this(typ: Type, name: String, mode: Mode) = this(typ, Id(name), None, Predicate(Lit("True")), mode)
  def this(typ: Type, name: String, init: Expression, mode: Mode) = this(typ, Id(name), Some(init), Predicate(Lit("True")), mode)
  def this(typ: Type, name: String, pred: Predicate) = this(typ, Id(name), None, pred, Mode("Reg"))
  def this(typ: Type, name: String, init: Expression, pred: Predicate) = this(typ, Id(name), Some(init), pred, Mode("Reg"))
  def this(typ: Type, name: String) = this(typ, Id(name), None, Predicate(Lit("False")), Mode("Reg"))
  def this(typ: Type, name: String, init: Expression) = this(typ, Id(name), Some(init), Predicate(Lit("False")), Mode("Reg"))

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

object Syntax {
  def modifies(expression: Expression): Set[Id] = expression match {
    case _: Id => Set()
    case _: Lit => Set()
    case PreOp("++", id: Id) => Set(id)
    case PreOp("--", id: Id) => Set(id)
    case PostOp("++", id: Id) => Set(id)
    case PostOp("--", id: Id) => Set(id)
    case BinOp("=", id: Id, arg) => Set(id) ++ modifies(arg)
    case PreOp(op, arg) => modifies(arg)
    case PostOp(op, arg) => modifies(arg)
    case BinOp(op, arg1, arg2) => modifies(arg1) ++ modifies(arg2)
    case Question(test, left, right) => modifies(test) ++ modifies(left) ++ modifies(right)
    //case Cast(typ, expression) => modifies(expression)
    //case SizeOfExpression(expression) => Set() // compile time
    //case SizeOfType(typ) => Set()
    //case Arrow(expression, field) => modifies(expression)
    //    case Dot(expression, field) => modifies(expression)
    //    case Index(expression, index) => modifies(expression) ++ modifies(index)
    case FunCall(name, args) => Set() ++ (args flatMap modifies)
    case Init(values) => Set() ++ (values flatMap { case (_, expression) => modifies(expression) })
  }

  def hasEffects(expression: Expression): Boolean = expression match {
    case _: Id => false
    case _: Lit => false
    case PreOp("++", arg) => true
    case PreOp("--", arg) => true
    case PostOp("++", arg) => true
    case PostOp("--", arg) => true
    case BinOp("=", arg1, arg2) => true
    case PreOp(op, arg) => hasEffects(arg)
    case PostOp(op, arg) => hasEffects(arg)
    case BinOp(op, arg1, arg2) => hasEffects(arg1) || hasEffects(arg2)
    case Question(test, left, right) => hasEffects(test) || hasEffects(left) || hasEffects(right)
    //case Cast(typ, expression) => hasEffects(expression)
    //case SizeOfExpression(expression) => false // compile time
    //case SizeOfType(typ) => false
    //case Arrow(expression, field) => hasEffects(expression)
    //    case Dot(expression, field) => hasEffects(expression)
    //    case Index(expression, index) => hasEffects(expression) || hasEffects(index)
    case FunCall(name, args) => true // XXX: approximation
    case Init(values) => (values exists { case (_, expression) => hasEffects(expression) })
  }

  def modifies(statement: Statement): Set[Id] = statement match {
    case _: VarDef => Set()
    case Malformed => Set()
    case Atomic(expression) => modifies(expression)
    case Return(None) => Set()
    case Return(Some(expression)) => modifies(expression)
    case Break | Continue | Fence => Set()
    case If(test, left, None) => modifies(test) ++ modifies(left)
    case If(test, left, Some(right)) => modifies(test) ++ modifies(left) ++ modifies(right)
    case While(test, body) => modifies(test) ++ modifies(body)
    case DoWhile(body, test) => modifies(test) ++ modifies(body)
    case For(init, test, inc, body) => modifies(init) ++ modifies(test) ++ modifies(inc) ++ modifies(body)
    case Block(statements) => Set() ++ (statements flatMap modifies)
  }
}