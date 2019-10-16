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

  type Typing = Set[Var]
  type Rename = Map[Var, Var]
  type Subst = Map[Var, Pure]

  object Typing {
    val empty: Typing = Set()

    def apply(xs: List[Param]): Typing = {
      xs.map(x => (x.toVar, x.typ)).toMap
    }
  }

  object Subst {
    val empty: Subst = Map()

    def apply(xs: (Var, Pure)*): Subst = {
      xs.toMap
    }

    def apply(ps: List[Param], as: List[Pure]): Subst = {
      val xs = ps map (_.toVar)
      apply(xs zip as: _*)
    }

    def fresh(xs: Set[Var]): Rename = {
      xs.map(x => (x, x.fresh)).toMap
    }

    def refresh(bound: Typing, xs: Set[Var]): (Typing, Rename) = {
      assert(xs subsetOf bound)
      val su = Subst.fresh(xs)
      val ty = xs map (x => su(x) -> bound(x))
      (bound -- xs ++ ty, su)
    }

    def free(env: Subst): Set[Var] = {
      Set() ++ (env.values flatMap (_.free))
    }
  }
}
