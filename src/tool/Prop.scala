package tool

trait Prop extends beaver.Symbol {
  def unary_!(): Prop
  def ||(that: Prop): Prop = Prop.or(this, that)
  def &&(that: Prop): Prop = Prop.and(this, that)

  def free: Set[Var]
  def subst(su: Subst): Prop

  def isRelational: Boolean
}

case class Exists(bound: Typing, body: Prop) extends Prop {
  def this(bound: List[Param], body: Prop) = this(Typing(bound), body)

  // maybe need to edit ??
  def unary_!() = Prop.not(this)


  def ex = bound
  def free = body.free -- bound

  def isRelational = body.isRelational

  /** Rename some bound variables [[xs]] to fresh ones. */
  def refresh(xs: Set[Var]) = {
    val (newbound, su) = Subst.refresh(bound, xs)
    Exists(newbound, body subst su)
  }

  /** Apply a substitution checked, refusing to introduce variable clashes. */
  def replace(su: Subst) = {
    assert((ex & su.keySet).isEmpty)
    assert((ex & Subst.free(su)).isEmpty)
    Exists(bound, body subst su)
  }

  /** Apply a substitution safely, renaming variables as needed. */
  def subst(su: Subst) = {
    val sw = su -- ex
    val vs = ex & Subst.free(sw)
    (this refresh vs) replace sw
  }
}

case class Sec(expr: Pure, sec: Pure) extends Prop {
  def unary_! = Prop.not(this)
  def free = expr.free ++ sec.free
  def subst(su: Subst) = Sec(expr subst su, sec subst su)
  def isRelational = true
  override def toString = expr + " :: " + sec
}

object Prop {
  def and(props: List[Prop]): Prop = props match {
    case Nil => Const._true
    case List(prop) => prop
    case _ => props reduce (_ && _)
  }

  case class not(prop: Prop) extends Prop {
    def unary_! = prop
    def free = prop.free
    def subst(su: Subst) = not(prop subst su)
    def isRelational = prop.isRelational
  }

  case class and(left: Prop, right: Prop) extends Prop {
    def unary_! = !left || !right
    def free = left.free ++ right.free
    def subst(su: Subst) = and(left subst su, right subst su)
    def isRelational = left.isRelational || right.isRelational
  }

  case class or(left: Prop, right: Prop) extends Prop {
    def unary_! = !left && !right
    def free = left.free ++ right.free
    def subst(su: Subst) = or(left subst su, right subst su)
    def isRelational = left.isRelational || right.isRelational
  }

}

