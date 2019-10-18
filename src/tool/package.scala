package object tool {
  object error {

    abstract class Error extends Exception {
      def info: Seq[Any]

      override def toString = info.mkString(" ")
    }

    case class InvalidControlVariables(info: Any*) extends Error
    case class InvalidProgram(info: Any*) extends Error
    case class SecurityError(info: Any*) extends Error

  }

  type Rename = Map[Var, Var]
  type Subst = Map[Var, Expression]

  object Subst {
    val empty: Subst = Map()

    def apply(xs: (Var, Expression)*): Subst = {
      xs.toMap
    }

    def apply(ps: List[Id], as: List[Expression]): Subst = {
      val xs = ps map (_.toVar)
      apply(xs zip as: _*)
    }

    def fresh(xs: Set[Var]): Rename = {
      xs.map(x => (x, x.fresh)).toMap
    }

    def refresh(bound: Set[Var], xs: Set[Var]): (Set[Var], Rename) = {
      assert(xs subsetOf bound)
      val su = Subst.fresh(xs)
      val ty = xs map (x => su(x))
      (bound -- xs ++ ty, su)
    }

    def free(env: Subst): Set[Var] = {
      Set() ++ (env.values flatMap (_.free))
    }
  }

  val sub = "₀₁₂₃₄₅₆₇₈₉"
  implicit class StringOps(self: String) {
    def prime = self + "'"

    def __(index: Int): String = {
      self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None => self
      case Some(index) => this __ index
    }
  }

}
