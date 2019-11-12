package tool

case class Global(variables: Set[VarDef], P_0: Option[List[Expression]], gamma_0: Option[List[GammaMapping]], statements: List[Statement]) extends beaver.Symbol {
  def this(variables: Array[VarDef], P_0: Array[Expression],  gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, Some(P_0.toList), Some(gamma_0.toList), statements.toList)
  def this(variables: Array[VarDef], P_0: Array[Expression], statements: Array[Statement]) = this( variables.toSet, Some(P_0.toList), None, statements.toList)
  def this(variables: Array[VarDef], gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, None, Some(gamma_0.toList), statements.toList)
  def this(variables: Array[VarDef], statements: Array[Statement]) = this( variables.toSet, None, None, statements.toList)
}

sealed trait Mode extends beaver.Symbol
case object Reg extends Mode {
  def instance = this
}
case object NoW extends Mode {
  def instance = this
}
case object NoRW extends Mode {
  def instance = this
}
case object RW extends Mode {
  def instance = this
}

sealed trait Security extends beaver.Symbol
case object High extends Security {
  def instance = this
}
case object Low extends Security {
  def instance = this
}

case class VarDef(name: Id, pred: Expression, mode: Mode) extends beaver.Symbol {
  def this(name: String, pred: Expression, mode: Mode) = this(Id(name), pred, mode)
  def this(name: String, mode: Mode) = this(Id(name), Const._true, mode)
  def this(name: String, pred: Expression) = this(Id(name), pred, Reg)
  def this(name: String) = this(Id(name), Const._true, Reg)

  override def toString: String = name.toString
}

case class GammaMapping(variable: Id, security: Security) extends beaver.Symbol {
  def this(variable: String, security: Security) = this(Id(variable), security)
}