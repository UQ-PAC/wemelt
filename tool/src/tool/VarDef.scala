package tool

case class Global(P_0: Option[List[Expression]], variables: Set[VarDef], gamma_0: Option[List[Expression]], statements: List[Statement]) extends beaver.Symbol {
  def this(P_0: Array[Expression], variables: Array[VarDef],  gamma_0: Array[Expression], statements: Array[Statement]) = this(Some(P_0.toList), variables.toSet, Some(gamma_0.toList), statements.toList)
  def this(P_0: Array[Expression], variables: Array[VarDef],  statements: Array[Statement]) = this(Some(P_0.toList), variables.toSet, None, statements.toList)
  def this(variables: Array[VarDef], gamma_0: Array[Expression], statements: Array[Statement]) = this(None, variables.toSet, Some(gamma_0.toList), statements.toList)
  def this(variables: Array[VarDef], statements: Array[Statement]) = this(None, variables.toSet, None, statements.toList)
}

case class Mode(mode: String) extends beaver.Symbol

case class VarDef(name: Id, pred: Expression, mode: Mode) extends beaver.Symbol {
  def this(name: String, pred: Expression, mode: Mode) = this(Id(name), pred, mode)
  def this(name: String, mode: Mode) = this(Id(name), Const._true, mode)
  def this(name: String, pred: Expression) = this(Id(name), pred, Mode("Reg"))
  def this(name: String) = this(Id(name), Const._true, Mode("Reg"))

  override def toString: String = name.toString
}