package tool

case class Variable(name:Id, pred: Predicate, mode: Mode) {
  def this(name: String, pred: Predicate, mode: Mode) = this(Id(name), pred, mode)
  def this(name: String, mode: Mode) = this(Id(name), Predicate(Lit("True")), mode)
  def this(name: String, pred: Predicate) = this(Id(name), pred, Mode("Reg"))
  def this(name: String) = this(Id(name), Predicate(Lit("True")), Mode("Reg"))

  var controlled: Set[Variable] = Set() // CLed(name)

  override def toString: String = name.toString
}
