package tool

trait Prop extends beaver.Symbol {
  def unary_!(): Prop
  def ||(that: Prop): Prop = Prop.or(this, that)
  def &&(that: Prop): Prop = Prop.and(this, that)
  /*
  def ==>(that: Prop): Prop = Prop.imp(this, that)
  def <=>(that: Prop): Prop = Prop.eqv(this, that)
  def ==>(that: Assert): Assert = Assert.imp(this, that)
   */

  def free: Set[Var]
  //def eval(st: Stack): Prop
  //def subst(su: Subst): Prop

  def isRelational: Boolean
}

sealed trait Quant
case object All extends Quant
case object Ex extends Quant

/*
case class Bind(q: Quant, bound: Typing, body: Prop) extends Prop {
  def this(q: Quant, bound: List[Param], body: Prop) = this(q, Typing(bound), body)

  def unary_!() = q match {
    case Ex => Bind(All, bound, !body)
    case All => Bind(Ex, bound, !body)
  }


  def ex = bound.keySet
  def free = body.free -- bound.keySet

  def eval(st: Stack) = {
    val xs = ex & Stack.free(st)
    if (xs.isEmpty) {
      Bind(q, bound, body eval st)
    } else {
      this refresh xs eval st
    }
  }


  def isRelational = body.isRelational

  /*
  /** Rename some bound variables [[xs]] to fresh ones. */
  def refresh(xs: Set[Var]) = {
    val (newbound, su) = Subst.refresh(bound, xs)
    Bind(q, newbound, body subst su)
  }

  /** Apply a substitution checked, refusing to introduce variable clashes. */
  def replace(su: Subst) = {
    assert((ex & su.keySet).isEmpty)
    assert((ex & Subst.free(su)).isEmpty)
    Bind(q, bound, body subst su)
  }

  /** Apply a substitution safely, renaming variables as needed. */
  def subst(su: Subst) = {
    val sw = su -- ex
    val vs = ex & Subst.free(sw)
    (this refresh vs) replace sw
  }
   */
}

 */

/*
case class Sec(expr: Pure, sec: Pure) extends Prop {
  def unary_! = Prop.not(this)
  def free = expr.free ++ sec.free
  def eval(st: Stack) = Sec(expr eval st, sec eval st)
  def subst(su: Subst) = Sec(expr subst su, sec subst su)
  def isRelational = true
  override def toString = expr + " :: " + sec
  }
 */

object Prop {
  def and(props: List[Prop]): Prop = props match {
    case Nil => Const._true
    case List(prop) => prop
    case _ => props reduce (_ && _)
  }

  case class not(prop: Prop) extends Prop {
    def unary_! = prop
    def free = prop.free
    //def eval(st: Stack) = not(prop eval st)
   // def subst(su: Subst) = not(prop subst su)
    def isRelational = prop.isRelational
  }

  case class and(left: Prop, right: Prop) extends Prop {
    def unary_! = !left || !right
    def free = left.free ++ right.free
    //def eval(st: Stack) = and(left eval st, right eval st)
    //def subst(su: Subst) = and(left subst su, right subst su)
    def isRelational = left.isRelational || right.isRelational
  }

  case class or(left: Prop, right: Prop) extends Prop {
    def unary_! = !left && !right
    def free = left.free ++ right.free
    //def eval(st: Stack) = or(left eval st, right eval st)
    //def subst(su: Subst) = or(left subst su, right subst su)
    def isRelational = left.isRelational || right.isRelational
  }

  /*
  case class imp(left: Prop, right: Prop) extends Prop {
    def unary_! = left && !right
    def free = left.free ++ right.free
    def eval(st: Stack) = imp(left eval st, right eval st)
    def subst(su: Subst) = imp(left subst su, right subst su)
    def isRelational = left.isRelational || right.isRelational
  }

  case class eqv(left: Prop, right: Prop) extends Prop {
    def unary_! = !left <=> right
    def free = left.free ++ right.free
    def eval(st: Stack) = eqv(left eval st, right eval st)
    def subst(su: Subst) = eqv(left subst su, right subst su)
    def isRelational = left.isRelational || right.isRelational
  }
  */
}
