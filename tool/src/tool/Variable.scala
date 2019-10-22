package tool

case class Mode(mode: String) extends beaver.Symbol

case class Variable(name: Id, pred: Expression, mode: Mode) {
  def this(name: String, pred: Expression, mode: Mode) = this(Id(name), pred, mode)
  def this(name: String, mode: Mode) = this(Id(name), Const._true, mode)
  def this(name: String, pred: Expression) = this(Id(name), pred, Mode("Reg"))
  def this(name: String) = this(Id(name), Const._true, Mode("Reg"))

  override def toString: String = name.toString
}
