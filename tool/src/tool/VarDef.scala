package tool

case class Global(variables: Set[VarDef], P_0: Option[List[Expression]], gamma_0: Option[List[Expression]], statements: List[Statement]) extends beaver.Symbol {
  def this(variables: Array[VarDef], P_0: Array[Expression], gamma_0: Array[Expression], statements: Array[Statement]) = this(variables.toSet, Some(P_0.toList), Some(gamma_0.toList), statements.toList)
  //def this(variables: Array[VarDef], P_0: Array[Expression], None, statements: Array[Statement]) = this(variables.toSet, Some(P_0.toList), None, statements.toList)
  //def this(variables: Array[VarDef], P_0: Array[Expression], gamma_0: Array[Expression], statements: Array[Statement]) = this(variables.toSet, None, Some(gamma_0.toList), statements.toList)
  def this(variables: Array[VarDef], statements: Array[Statement]) = this(variables.toSet, None, None, statements.toList)
}

trait Spec extends beaver.Symbol

case class Mode(mode: String) extends beaver.Symbol

case class VarDef(name: Id, pred: Expression, mode: Mode) extends Spec {
  def this(name: String, pred: Expression, mode: Mode) = this(Id(name), pred, mode)
  def this(name: String, mode: Mode) = this(Id(name), Const._true, mode)
  def this(name: String, pred: Expression) = this(Id(name), pred, Mode("Reg"))
  def this(name: String) = this(Id(name), Const._true, Mode("Reg"))

  override def toString: String = name.toString
}