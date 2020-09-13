package wemelt

case class Predicate(predicates: List[Expression], exists: Set[Var] = Set(), forall: Set[Var] = Set()) {

  def add(expression: Expression): Predicate = {
    copy(predicates = expression :: predicates)
  }

  def add(expressions: List[Expression]): Predicate = {
    copy(predicates = predicates ++ expressions)
  }

  // P1 AND P2
  def combine(other: Predicate): Predicate = {
    copy(predicates = predicates ++ other.predicates, exists = exists ++ other.exists, forall = forall ++ other.forall)
  }

  def addExists(toAdd: Set[Var]): Predicate = {
    copy(exists = (predicates.flatMap (p => p.bound)).toSet & (exists ++ toAdd))
  }

  def addForAll(toAdd: Set[Var]): Predicate = {
    copy(forall = (predicates.flatMap (p => p.bound)).toSet & (forall ++ toAdd))
  }

  def ++(other: Predicate): Predicate = combine(other)
  def :::(other: Predicate): Predicate = combine(other)

  def subst(toSubst: Subst): Predicate = {
    copy(predicates = predicates map (p => p.subst(toSubst)))
  }

  // existentially quantify (substitute with fresh variables) all variables in toBind
  def bindExists(toBind: Set[Var]): Predicate = {
    var bound: Set[Var] = Set()
    val toSubst: Subst = {for (r <- toBind) yield {
      val fresh = r.fresh
      bound += fresh
      r -> fresh
    }}.toMap
    val predicatesPrime = predicates map (p => p.subst(toSubst))
    val existsPrime = (exists ++ bound) & (predicatesPrime flatMap (p => p.bound)).toSet
    copy(predicates = predicatesPrime, exists = existsPrime)
  }

  // universally quantify all variables in toBind
  def bindForAll(toBind: Set[Var]): Predicate = {
    var bound: Set[Var] = Set()
    val toSubst: Subst = {for (r <- toBind) yield {
      val fresh = r.fresh
      bound += fresh
      r -> fresh
    }}.toMap
    val predicatesPrime = predicates map (p => p.subst(toSubst))
    val forallPrime = (forall ++ bound) & (predicatesPrime flatMap (p => p.bound)).toSet
    copy(predicates = predicatesPrime, forall = forallPrime)
  }

  override def toString: String = {
     val existsStr = if (exists.nonEmpty) {
       "exists " + exists.mkString(", ") + " :: ("
    } else {
      ""
    }
    val existsClose = if (exists.nonEmpty) {")"} else {""}
    val forallStr = if (forall.nonEmpty) {
      "forall " + forall.mkString(", ") + " :: ("
    } else {
      ""
    }
    val forallClose = if (forall.nonEmpty) {")"} else {""}
    existsStr ++ forallStr ++ predicates.mkString(" &&" + newline + "   ") ++ forallClose ++ existsClose
  }

  def toAnd: Expression = {
    if (predicates == List(Const._true)) {
      Const._true
    } else if (predicates == List(Const._false)) {
      Const._false
    } else if (exists.isEmpty && forall.isEmpty) {
      State.andPredicates(predicates)
    } else if (exists.isEmpty && forall.nonEmpty) {
      ForAll(forall, State.andPredicates(predicates))
    } else if (exists.nonEmpty && forall.isEmpty) {
      Exists(exists, State.andPredicates(predicates))
    } else {
      ForAll(forall, Exists(exists, State.andPredicates(predicates)))
    }
  }

  // https://www.cs.jhu.edu/~jason/tutorials/convert-to-CNF.html
  // P1 OR P2 converted to CNF, using switching variable to keep converted formula small
  def merge(P2: Predicate): Predicate = {
    if (predicates.isEmpty) {
      return P2
    }
    if (P2.predicates.isEmpty) {
      return this
    }
    val common = predicates.intersect(P2.predicates) // common elements don't need switching variable
    val switch = Switch.fresh
    val p1List: List[Expression] = for (p1 <- predicates if !common.contains(p1)) yield {
      BinOp("||", PreOp("!", switch), p1)
    }
    val p2List: List[Expression] = for (p2 <- P2.predicates if !common.contains(p2)) yield {
      BinOp("||", switch, p2)
    }
    Predicate(common ++ p1List ++ p2List, exists ++ P2.exists, forall ++ P2.forall)
  }

  def isConstTrue: Boolean = {
    if (predicates == List(Const._true)) true else false
  }
}

case class State(
  gamma: Map[Var, Predicate],
  D: DType, // W_w, W_r, R_w, R_r
  P: Predicate,
  P_inv: Predicate,
  R_var: Map[Var, List[(Expression, Expression)]],
  R: Predicate,
  G: Predicate,
  G_var: Map[Var, List[(Expression, Expression)]],

  L_R: Map[Var, Expression],
  L_G: Map[Var, Expression],
  L: Map[Var, Expression],

  globals: Set[Var],
  locals: Set[Var],
  labels: Map[Id, Var],
  definedLocals: Map[Id, Var],

  controls: Set[Var],
  controlled: Set[Var],
  controlledBy: Map[Var, Set[Var]], // CLed(name)

  variables: Set[Var],
  primed: Subst,

  read: Set[Var],
  written: Set[Var],
  indirect: Set[Var],
  used: Set[Var],

  memSize: Int,
  memory: Map[Id, Int],
  globalOffsetTable: Map[Id, Int],
  indexToGlobal: Map[Int, Var],
  //arrayIndices: Set[Var],
  //arrays: Map[Var, VarArray],

  toLog: Boolean,
  debug: Boolean,
  noInfeasible: Boolean) {

  def W_w(v: Var): Set[Var] = D(v)._1
  def W_r(v: Var): Set[Var] = D(v)._2
  def R_w(v: Var): Set[Var] = D(v)._3
  def R_r(v: Var): Set[Var] = D(v)._4
  def I_w(v: Var): Set[Var] = D(v)._5
  def I_r(v: Var): Set[Var] = D(v)._6
  def U_w(v: Var): Set[Var] = D(v)._7
  def U_r(v: Var): Set[Var] = D(v)._8

  def log: Unit = {
    if (toLog) {
      println("Gamma: " + gamma.gammaStr)
      println("P: " + P)
      println("D: " + D.DStr)
    }
  }

  // update P after assignment
  def assignUpdateP(v: Var, arg: Expression): (State, Subst, Set[Var]) = {
    val PRestrictInd = restrictPInd(arg.variables + v)

    val fresh = Var.fresh(v.name, v.size)
    // create mapping from variable to fresh variable
    val toSubst: Subst = Map(v -> fresh)

    // substitute variable in P for fresh variable
    val PReplace = PRestrictInd.subst(toSubst)

    // substitute variable in expression for fresh variable
    val argReplace = arg.subst(toSubst)

    // add new assignment statement to P
    val PPrime = PReplace.add(BinOp("==", v, argReplace)).addExists(Set(fresh))

    // calculate new_var
    val varE = arg.variables
    val varLY: Set[Var] = {
      for (y <- varE -- gamma.keySet)
        yield L(y).variables
    }.flatten
    val new_var: Set[Var] = Set(v) ++ varE ++ varLY


    // calculate weaker
    val toSubstC: Subst = Map(v -> arg) // for c[e/x]
    var weaker: Set[Var] = Set()
    for (y <- R_var.keySet) {
      // check !(P && c ==> c[e/x])
      var yAdded = false
      for ((c, r) <- R_var(y) if !yAdded && c != Const._true) {
        if (!SMT.proveImplies(PPrime.add(c), c.subst(toSubstC), debug)) {
          weaker +=y
          yAdded = true
        }
      }
    }

    // calculate equals
    // possible improvement:
    // separate method for identity relation? check all identity relations at the start?
    val equals: Set[Var] = {
      for (y <- R_var.keySet)
        yield {
          // check P ==> c && r is identity relation
          for ((c, r) <- R_var(y) if (r == BinOp("==", y, y.prime) || r == BinOp("==", y.prime, y))
            && (c == Const._true || SMT.proveImplies(PPrime ::: P_inv, c, debug)))
            yield y
        }
    }.flatten

    val domM = new_var ++ weaker -- equals

    var exists: Set[Var] = Set() // set of newly created variables to bind
    // map all of domM to fresh temporary variables - probably change to different fresh allocator
    val m: Subst = {
      for (v <- domM)
        yield {
          val newFresh = v.fresh
          exists += newFresh
          v -> newFresh
        }
    }.toMap

    val mPlusMPrime: Subst = m ++ {
      for (v <- domM)
        yield v.prime -> v
    }.toMap

    val PPlus = PPrime.subst(m).addExists(exists)

    if (debug) {
      println("dom R_var: " + R_var.keySet)
      println("dom m: " + domM)
    }
    val RPlus: List[Expression] = {for (y <- R_var.keySet & domM) yield {
      for ((c, r) <- R_var(y))
        yield if (c == Const._true) {
          r.subst(mPlusMPrime)
        } else {
          BinOp("==>", ForAll(indirect, c), r.subst(mPlusMPrime))
        }
    }
    }.flatten.toList

    if (debug) {
      println("P +: " + PPlus)
      println("+ R: " + RPlus)
    }

    val PPlusR = PPlus.add(RPlus)

    if (debug) {
      println("assigning " + arg + " to " + v + ":")
      println("P: " + P)
      println("P': " + PPrime)
      println("P + R: " + PPlusR)
    }
    (copy(P = PPlusR), m, exists)
  }

  def assignUpdateGamma(id: Var, t: Predicate, m: Subst, exists: Set[Var]): State = {
    val domGamma = low_or_eq(P)
    val gammaPrime = if (domGamma.contains(id)) {
      gamma + (id -> t.bindForAll(indirect & (t.predicates flatMap (p => p.variables)).toSet))
    } else {
      gamma
    }
    val gammaPrimeRestrict = gammaPrime -- (gammaPrime.keySet -- domGamma)
    val gammaPlusR: Map[Var, Predicate] = {
      for (g <- gammaPrimeRestrict.keySet)
        yield g -> gammaPrimeRestrict(g).subst(m).addExists(exists)
    }.toMap
    if (debug) {
      println("Gamma + R: " + gammaPlusR.gammaStr)
    }
    copy(gamma = gammaPlusR)
  }

  // update P and Gamma with loop/if guard
  def guardUpdateP(guard: Expression): (State, Subst, Set[Var]) = {
    val vars = guard.variables
    val PRestrictInd = restrictPInd(vars)

    // add guard to P
    val PPrime = PRestrictInd.add(guard)

    // calculate new_var
    val new_var: Set[Var] = vars

    // calculate equals - this can be improved too
    // separate method for identity relation? check all identity relations at the start?
    val equals: Set[Var] = {
      for (y <- R_var.keySet)
        yield {
          // check P ==> c && r is identity relation
          for ((c, r) <- R_var(y) if (r == BinOp("==", y, y.prime) || r == BinOp("==", y.prime, y))
            && (c == Const._true || SMT.proveImplies(PPrime ::: P_inv, c, debug)))
            yield y
        }
    }.flatten

    val domM = new_var -- equals

    var exists: Set[Var] = Set() // set of newly created variables to bind
    // map all of domM to fresh temporary variables - probably change to different fresh allocator
    val m: Subst = {
      for (v <- domM)
        yield {
          val newFresh = v.fresh
          exists += newFresh
          v -> newFresh
        }
    }.toMap

    val mPlusMPrime: Subst = m ++ {
      for (v <- domM)
        yield v.prime -> v
    }.toMap

    val PPlus = PPrime.subst(m).addExists(exists)

    if (debug) {
      println("dom R_var: " + R_var.keySet)
      println("dom m: " + domM)
    }
    val RPlus: List[Expression] = {for (y <- R_var.keySet & domM) yield {
      for ((c, r) <- R_var(y))
        yield if (c == Const._true) {
          r.subst(mPlusMPrime)
        } else {
          BinOp("==>", ForAll(indirect map (i => i), c), r.subst(mPlusMPrime))
        }
    }
    }.flatten.toList

    if (debug) {
      println("P +: " + PPlus)
      println("+ R: " + RPlus)
    }

    val PPlusR = PPlus.add(RPlus)

    if (debug) {
      println("updating P and Gamma with guard " + guard)
      println("P: " + P)
      println("P': " + PPrime)
      println("P + R: " + PPlusR)

    }
    (copy(P = PPlusR), m, exists)
  }

  def guardUpdateGamma(m: Subst, exists: Set[Var]): State = {
    val domGamma = low_or_eq(P)
    val gammaPrimeRestrict = gamma -- (gamma.keySet -- domGamma)
    val gammaPlusR: Map[Var, Predicate] = {
      for (g <- gammaPrimeRestrict.keySet)
        yield g -> gammaPrimeRestrict(g).subst(m).addExists(exists)
    }.toMap

    if (debug) {
      println("Gamma + R: " + gammaPlusR.gammaStr)
    }
    copy(gamma = gammaPlusR)
  }

  def PPlusRUpdate(v: Var, arg: Expression): Predicate = {
    // create mapping from variable to fresh variable
    val fresh = Var.fresh(v.name, v.size)
    val toSubst: Subst = Map(v -> fresh)

    // substitute variable in P for fresh variable
    val PReplace = P.subst(toSubst)

    // substitute variable in expression for fresh variable
    val argReplace = arg.subst(toSubst)

    // add new assignment statement to P
    val PPrime = PReplace.add(BinOp("==", v, argReplace)).addExists(Set(fresh))

    // calculate new_var
    val varE = arg.variables
    val varLY: Set[Var] = {
      for (y <- varE -- gamma.keySet)
        yield L(y).variables
    }.flatten
    val new_var: Set[Var] = Set(v) ++ varE ++ varLY


    // calculate weaker
    val toSubstC: Subst = Map(v -> arg) // for c[e/x]

    var weaker: Set[Var] = Set()
    for (y <- R_var.keySet) {
      // check !(P && c ==> c[e/x])
      var yAdded = false
      for ((c, r) <- R_var(y) if !yAdded && c != Const._true) {
        if (!SMT.proveImplies(PPrime.add(c), c.subst(toSubstC), debug)) {
          weaker +=y
          yAdded = true
        }
      }
    }

    // calculate equals
    // possible improvement:
    // separate method for identity relation? check all identity relations at the start?
    val equals: Set[Var] = {
      for (y <- R_var.keySet)
        yield {
          // check P ==> c && r is identity relation
          for ((c, r) <- R_var(y) if (r == BinOp("==", y, y.prime) || r == BinOp("==", y.prime, y))
            && (c == Const._true || SMT.proveImplies(PPrime ::: P_inv, c, debug)))
            yield y
        }
    }.flatten

    val domM = new_var ++ weaker -- equals

    var exists: Set[Var] = Set() // set of newly created variables to bind
    // map all of domM to fresh temporary variables - probably change to different fresh allocator
    val m: Subst = {
      for (v <- domM)
        yield {
          val newFresh = v.fresh
          exists += newFresh
          v -> newFresh
        }
    }.toMap

    val mPlusMPrime: Subst = m ++ {
      for (v <- domM)
        yield v.prime -> v
    }.toMap

    val PPlus = PPrime.subst(m).addExists(exists)

    if (debug) {
      println("dom R_var: " + R_var.keySet)
      println("dom m: " + domM)
    }
    val RPlus: List[Expression] = {for (y <- R_var.keySet & domM) yield {
      for ((c, r) <- R_var(y))
        yield if (c == Const._true) {
          r.subst(mPlusMPrime)
        } else {
          BinOp("==>", ForAll(indirect, c), r.subst(mPlusMPrime))
        }
    }
    }.flatten.toList

    if (debug) {
      println("P +: " + PPlus)
      println("+ R: " + RPlus)
    }

    PPlus.add(RPlus)
  }

  // update P after memory store
  def storeUpdate(access: Access, arg: Expression, possible: Seq[Int], t: Predicate): State = {
    val POut = if (possible.size == 1) {
      val (st1, m, exists) = storeUpdateP(access, arg, possible.head)
      val st2 = st1.storeUpdateGamma(access, possible.head, t, m, exists)
      st2.updateDArrayAssign(access, possible, arg)
    } else {
      val states: Seq[State] = for (i <- possible) yield {
        val (st1, m, exists) = storeUpdateP(access, arg, i)
        st1.storeUpdateGamma(access, possible.head, t, m, exists)
      }
      val st2: State = mergeStates(access, possible, states)
      st2.updateDArrayAssign(access, possible, arg)
    }
    POut
  }

  def storeUpdateP(access: Access, arg: Expression, index: Int): (State, Subst, Set[Var]) = {
    val PRestrictInd = restrictPInd(arg.variables ++ access.index.variables)

    val fresh = Access.fresh(access.index, access.size)
    val freshIndex = fresh.freshIndex
    // create mapping from variable to fresh variable
    val accesses: Set[Access] = arg.arrays - access
    val accessesSubst: Subst = {for (a <- accesses) yield {
      a.index match {
        case Lit(n) if n != index =>
          a -> a
        case Lit(n) if n == index =>
          a -> fresh
        case _ =>
          a -> IfThenElse(BinOp("==", access.index, a.index), Access(a.index, a.size, freshIndex), a)
      }
    }
    }.toMap
    val toSubst: Subst = accessesSubst ++ Map(access -> fresh)

    // substitute variable in P for fresh variable
    val PReplace = PRestrictInd.subst(toSubst)

    // substitute variable in expression for fresh variable
    val argReplace = arg.subst(toSubst)
    // don't need to replace index as can't have nested accesses here

    // add new assignment statement to P
    val PPrime = PReplace.add(BinOp("==", access, argReplace)).addExists(Set(fresh))

    val v = getMemoryVar(index, access.size)
    // calculate new_var
    val varE = arg.variables
    val varLY: Set[Var] = {
      for (y <- varE -- gamma.keySet)
        yield L(y).variables
    }.flatten
    val new_var: Set[Var] = Set(v) ++ varE ++ varLY

    // calculate weaker
    val accessesSubstC: Subst = {for (a <- accesses) yield
      a -> IfThenElse(BinOp("==", access.index, a.index), arg, a)
    }.toMap
    val toSubstC: Subst = accessesSubstC ++ Map(access -> arg) // for c[e/x]
    var weaker: Set[Var] = Set()
    for (y <- R_var.keySet) {
      // check !(P && c ==> c[e/x])
      var yAdded = false
      for ((c, r) <- R_var(y) if !yAdded && c != Const._true) {
        if (!SMT.proveImplies(PPrime.add(c), c.subst(toSubstC), debug)) {
          weaker +=y
          yAdded = true
        }
      }
    }

    // calculate equals
    // possible improvement:
    // separate method for identity relation? check all identity relations at the start?
    val equals: Set[Var] = {
      for (y <- R_var.keySet)
        yield {
          // check P ==> c && r is identity relation
          for ((c, r) <- R_var(y) if (r == BinOp("==", y, y.prime) || r == BinOp("==", y.prime, y))
            && (c == Const._true || SMT.proveImplies(PPrime ::: P_inv, c, debug)))
            yield y
        }
    }.flatten

    val domM = new_var ++ weaker -- equals

    var exists: Set[Var] = Set() // set of newly created variables to bind
    // map all of domM to fresh temporary variables
    val m: Subst = {
      for (v <- domM)
        yield {
          val newFresh = v.fresh
          exists += newFresh
          v -> newFresh
        }
    }.toMap

    val mPlusMPrime: Subst = m ++ {
      for (v <- domM)
        yield v.prime -> v
    }.toMap

    val PPlus = PPrime.subst(m).addExists(exists)

    if (debug) {
      println("dom R_var: " + R_var.keySet)
      println("dom m: " + domM)
    }
    val RPlus: List[Expression] = {for (y <- R_var.keySet & domM) yield {
      for ((c, r) <- R_var(y))
        yield if (c == Const._true) {
          r.subst(mPlusMPrime)
        } else {
          BinOp("==>", ForAll(indirect, c), r.subst(mPlusMPrime))
        }
    }
    }.flatten.toList

    if (debug) {
      println("P +: " + PPlus)
      println("+ R: " + RPlus)
    }

    val PPlusR = PPlus.add(RPlus)

    if (debug) {
      println("assigning " + arg + " to mem[" + access.index + "]:")
      println("P: " + P)
      println("P': " + PPrime)
      println("P + R: " + PPlusR)
    }
    (copy(P = PPlusR), m, exists)
  }

  def storeUpdateGamma(access: Access, index: Int, t: Predicate, m: Subst, exists: Set[Var]): State = {
    val domGamma = low_or_eq(P)
    val v = getMemoryVar(index, access.size)
    val gammaPrime = if (domGamma.contains(v)) {
      gamma + (v -> t.bindForAll(indirect & (t.predicates flatMap (p => p.variables)).toSet))
    } else {
      gamma
    }
    val gammaPrimeRestrict = gammaPrime -- (gammaPrime.keySet -- domGamma)
    val gammaPlusR: Map[Var, Predicate] = {
      for (g <- gammaPrimeRestrict.keySet)
        yield g -> gammaPrimeRestrict(g).subst(m).addExists(exists)
    }.toMap
    if (debug) {
      println("Gamma + R: " + gammaPlusR.gammaStr)
    }
    copy(gamma = gammaPlusR)
  }

  def assignUpdateGamma(v: Var, t: Predicate, m: Subst, exists: Set[Var]): State = {
    val domGamma = low_or_eq(P)
    val gammaPrime = if (domGamma.contains(v)) {
      gamma + (v -> t.bindForAll(indirect & (t.predicates flatMap (p => p.variables)).toSet))
    } else {
      gamma
    }
    val gammaPrimeRestrict = gammaPrime -- (gammaPrime.keySet -- domGamma)
    val gammaPlusR: Map[Var, Predicate] = {
      for (g <- gammaPrimeRestrict.keySet)
        yield g -> gammaPrimeRestrict(g).subst(m).addExists(exists)
    }.toMap
    if (debug) {
      println("Gamma + R: " + gammaPlusR.gammaStr)
    }
    copy(gamma = gammaPlusR)
  }


  // redo this so instead of just keeping one common and branching
  // have like if index == 1 then (1 specific predicates) else (the non-1 version of those predicates)
  // if index == 2 then (
  // and so on?
  def mergeStates(access: Access, indices: Seq[Int], states: Seq[State]): State = {
    var common: List[Expression] = states.head.P.predicates
    for (s <- states) {
      common = common.intersect(s.P.predicates)
    }
    val predicates: List[List[Expression]] = {
      for (s <- states) yield
        for (p <- s.P.predicates if !common.contains(p)) yield p
    }.toList

    val preds = List(mergePs(access.index, predicates, indices)) ::: common
    val exists = (states flatMap {s => s.P.exists}).toSet
    val forall = (states flatMap {s => s.P.forall}).toSet
    val PPrime: Predicate = Predicate(preds, exists, forall)


    val gammaPrime: Map[Var, Predicate] =
      //
    copy(P = PPrime, gamma = gammaPrime)
  }

  def mergePs(accessIndex: Expression, predicates: List[List[Expression]], indices: Seq[Int]): Expression = {
    if (indices.isEmpty) {
      Const._true
    } else if (indices.length == 1) {
      IfThenElse(BinOp("==", accessIndex, Lit(indices.head)), State.andPredicates(predicates.head), Const._false)
    } else {
      IfThenElse(BinOp("==", accessIndex, Lit(indices.head)), State.andPredicates(predicates.head), mergePs(accessIndex, predicates.drop(1), indices.drop(1)))
    }
  }

  /*
  def assignCAS(lhs: Var, x: Var, r1: Expression, r2: Expression): State = {
    val _lhs = lhs
    val _x = x

    // create mapping from variables to fresh variables
    val toSubst: Subst = Map(_lhs -> Var.fresh(_lhs.name), _x -> Var.fresh(_x.name))

    // substitute variables in P for fresh variables
    val PReplace = P map (p => p.subst(toSubst))

    // substitute variables in expressions for fresh variables
    val _r1 = r1.subst(toSubst)
    val _r2 = r2.subst(toSubst)
    val __x = _x.subst(toSubst)

    // add assignments to P
    val PPrime = BinOp("==", _lhs, Question(BinOp("==", __x, _r1), Lit(1), Lit(0))) ::
      BinOp("==", _x, Question(BinOp("==", __x, _r1), _r2, __x)) :: PReplace

    // restrict PPrime to stable variables
    val PPrimeRestrict = State.restrictP(PPrime, stable)

    if (debug) {
      println("updating P for " + lhs + " = CAS(" + x + ", " + r1 + ", " + r2 + ")")
      println("P: " + P.PStr)
      println("P': " + PPrimeRestrict.PStr)
    }
    copy(P = PPrimeRestrict)
  }

  // update P with strongest post-condition after array assignment
  def arrayAssign(a: Var, index: Expression, arg: Expression, possible: Seq[Int]): State = {
    val v = a
    // create mapping from variable to fresh variable
    val toSubst: Subst = Map(v -> Var.fresh(a.name))

    val POut = if (possible.size == 1) {
      // unambiguous access case
      val PReplace = P map (p => p.subst(toSubst, possible.head))
      // substitute variable in expression for fresh variable
      val argReplace = arg.subst(toSubst, possible.head)

      val indexToSubst: Subst = {
        for (j <- index.variables)
          yield j -> j
        }.toMap ++ toSubst

      val indexSubst = index.subst(indexToSubst, possible.head)

      // add new assignment statement to P
      val PPrime = BinOp("==", VarAccess(v, indexSubst), argReplace) :: PReplace

      // restrict PPrime to stable variables
      State.restrictP(PPrime, stable)
    } else {
      // ambiguous access case - merge states
      val possiblePs: List[List[Expression]] = {for (i <- possible) yield {
        val PReplace = P map (p => p.subst(toSubst, i))
        // substitute variable in expression for fresh variable
        val argReplace = arg.subst(toSubst, i)

        val indexToSubst: Subst = {
          for (j <- index.variables)
            yield j -> j
          }.toMap ++ toSubst

        val indexSubst = index.subst(indexToSubst, i)

        // add new assignment statement to P
        val PPrime = BinOp("==", VarAccess(v, indexSubst), argReplace) :: BinOp("==", indexSubst, Lit(i)) :: PReplace

        // restrict PPrime to stable variables
        State.restrictP(PPrime, stable)
      }}.toList
      mergePs(possiblePs)
    }

    if (debug) {
      println("assigning " + arg + " to " + a + "[" + index + "]" + ":")
      println("P: " + P.PStr)
      println("P': " + POut.PStr)
    }
    copy(P = POut)
  }
   */

  def resetReadWrite(): State = {
    copy(read = Set(), written = Set(), indirect = Set(), used = Set())
  }

  def updateRead(id: Var): State = {
    if (debug)
      println("updating read (" + read + ") with " + id)
    copy(read = read + id)
  }

  def updateRead(id: Set[Var]): State = {
    if (debug)
      println("updating read (" + read + ") with " + id)
    copy(read = read ++ id)
  }

  def updateWritten(id: Var): State = {
    if (debug)
      println("updating written (" + written + ") with " + id)
    copy(written = written + id)
  }

  def updateWritten(id: Set[Var]): State = {
    if (debug)
      println("updating written (" + written + ") with " + id)
    copy(written = written ++ id)
  }

  /*
  def updateWritten(array: VarArray): State = {
    val ids: Set[Var] = {for (i <- array.array.indices)
      yield array.array(i)}.toSet
    if (debug)
      println("updating written (" + written + ") with " + ids)
    copy(written = written ++ ids)
  }

  def updateRead(array: VarArray): State = {
    val ids: Set[Var] = {for (i <- array.array.indices)
      yield array.array(i)}.toSet
    if (debug)
      println("updating read (" + read + ") with " + ids)
    copy(read = read ++ ids)
  } */


  def knownW: Set[Var] = {
    if (debug) {
      println("calculating knownW")
      println("wr: " + written)
      println("rd: " + read)
    }
    val w = for (v <- written) yield {
      W_w(v)
    }
    val r = for (v <- read) yield {
      W_r(v)
    }
    w.flatten ++ r.flatten
  }

  def knownR: Set[Var] = {
    if (debug) {
      println("calculating knownR")
      println("wr: " + written)
      println("rd: " + read)
    }
    val r = for (v <- read) yield {
      R_r(v)
    }
    val w = for (v <- written) yield {
      R_w(v)
    }
    r.flatten ++ w.flatten
  }

  def knownI: Set[Var] = {
    if (debug) {
      println("calculating knownI")
      println("wr: " + written)
      println("rd: " + read)
    }
    val r = for (v <- read) yield {
      I_r(v)
    }
    val w = for (v <- written) yield {
      I_w(v)
    }
    r.flatten ++ w.flatten
  }

  def knownU: Set[Var] = {
    if (debug) {
      println("calculating knownU")
      println("wr: " + written)
      println("rd: " + read)
    }
    val r = for (v <- read) yield {
      U_r(v)
    }
    val w = for (v <- written) yield {
      U_w(v)
    }
    r.flatten ++ w.flatten
  }

  def updateD(laterW: Set[Var], laterR: Set[Var]): DType = {
    val knownw = knownW
    val knownr = knownR
    val knowni = knownI
    val knownu = knownU
    if (debug) {
      println("knownW: " + knownw)
      println("knownR: " + knownr)
      println("knownI: " + knowni)
      println("knownU: " + knownu)
    }
    for (i <- variables) yield {
      val w_w = if (laterW.contains(i)) {
        W_w(i) ++ knownw
      } else {
        W_w(i) -- written
      }
      val w_r = if (laterR.contains(i)) {
        W_r(i) ++ knownw
      } else {
        W_r(i) -- written
      }
      val r_w = if (laterW.contains(i)) {
        R_w(i) ++ knownr
      } else {
        R_w(i) -- read
      }
      val r_r = if (laterR.contains(i)) {
        R_r(i) ++ knownr
      } else {
        R_r(i) -- read
      }
      val i_w = if (laterW.contains(i)) {
        I_w(i) ++ knowni
      } else {
        I_w(i) -- indirect
      }
      val i_r = if (laterR.contains(i)) {
        I_r(i) ++ knowni
      } else {
        I_r(i) -- indirect
      }
      val u_w = if (laterW.contains(i)) {
        U_w(i) ++ knownu
      } else {
        U_w(i) -- used
      }
      val u_r = if (laterR.contains(i)) {
        U_r(i) ++ knownu
      } else {
        U_r(i) -- used
      }
      i -> (w_w, w_r, r_w, r_r, i_w, i_r, u_w, u_r)
    }
  }.toMap

  def updateDAssign(x: Var, e: Expression) : State = {
    val varE = e.variables // var(e)
    val canForward = varE.intersect(globals).isEmpty
    val laterW: Set[Var] = Set(x) ++ varE
    val laterR: Set[Var] = if (!canForward) {
      Set(x) ++ varE.intersect(globals)
    } else {
      Set()
    }
    if (debug) {
      println("laterW: " + laterW)
      println("laterR: " + laterR)
      println("rd: " + read)
      println("wr: " + written)
    }
    val DPrime: DType = updateD(laterW, laterR)

    // updated forwarding
    val DPrimePrime = if (canForward) {
      val w_r = {for (v <- read)
        yield W_r(v)
        }.flatten -- written
      val r_r = {for (v <- read)
        yield R_r(v)
        }.flatten -- read
      DPrime + (x -> (DPrime(x)._1, w_r, DPrime(x)._3, r_r, DPrime(x)._5, DPrime(x)._6, DPrime(x)._7, DPrime(x)._8))
    } else {
      DPrime
    }
    /*
    if (toLog) {
      println("D: " + DPrimePrime.DStr)
    } */
    copy(D = DPrimePrime, read = Set(), written = Set(), indirect = Set(), used = Set())
  }

  def updateDArrayAssign(a: Access, indices: Seq[Int], e: Expression) : State = {
    val varE = e.variables // var(e)
    val canForward = varE.intersect(globals).isEmpty
    val laterW: Set[Var] = varE
    val laterR: Set[Var] = if (!canForward) {
      varE.intersect(globals)
    } else {
      Set()
    }
    if (debug) {
      println("laterW: " + laterW)
      println("laterR: " + laterR)
      println("rd: " + read)
      println("wr: " + written)
    }
    val DPrime: DType = updateD(laterW, laterR)

    // updated forwarding
    val DPrimePrime = if (canForward) {
      val toUpdate = for (i <- indices) yield {
        val w_r = {
          for (v <- read)
            yield W_r(v)
        }.flatten -- written
        val r_r = {
          for (v <- read)
            yield R_r(v)
        }.flatten -- read
        val x = getMemoryVar(i, a.size)
        x -> (DPrime(x)._1, w_r, DPrime(x)._3, r_r, DPrime(x)._5, DPrime(x)._6, DPrime(x)._7, DPrime(x)._8)
      }
      DPrime ++ toUpdate
    } else {
      DPrime
    }
    /*
    if (toLog) {
      println("D: " + DPrimePrime.DStr)
    } */
    copy(D = DPrimePrime, read = Set(), written = Set(), indirect = Set(), used = Set())
  }


  /*
  def updateDArrayAssign(x: Var, e: Expression) : State = {
    val varE = e.variables // var(e)
    val laterW: Set[Var] = varE
    val laterR: Set[Var] = varE.intersect(globals)
    if (debug) {
      println("laterW: " + laterW)
      println("laterR: " + laterR)
      println("rd: " + read)
      println("wr: " + written)
    }
    val DPrime: DType = updateD(laterW, laterR)

    // updated forwarding
    val DPrimePrime = if (varE.intersect(globals).isEmpty) {
      val toUpdate = for (i <- arrays(x).array) yield {
        val w_r = {for (v <- read)
          yield W_r(v)
          }.flatten -- written
        val r_r = {for (v <- read)
          yield R_r(v)
          }.flatten -- read
        i -> (DPrime(i)._1, w_r, DPrime(i)._3, r_r)
      }
      DPrime ++ toUpdate
    } else {
      DPrime
    }

    copy(D = DPrimePrime, read = Set(), written = Set())
  }
   */

  /*
  def updateDCAS(r3: Var, x: Var, r1: Expression, r2: Expression) : State = {
    val varR1 = r1.variables
    val varR2 = r2.variables
    val laterW: Set[Var] = Set(x, r3) ++ varR1 ++ varR2
    val laterR: Set[Var] = Set(r3, x) ++ ((varR1 ++ varR2) & globals)
    if (debug) {
      println("laterW: " + laterW)
      println("laterR: " + laterR)
      println("rd: " + read)
      println("wr: " + written)
    }
    val DPrime: DType = updateD(laterW, laterR)

    copy(D = DPrime, read = Set(), written = Set())
  }
  */

  def updateDGuard(b: Expression) : State = {
    val varB = b.variables // var(b)
    val laterW: Set[Var] = globals ++ varB + CFence
    val laterR: Set[Var] = globals & varB

    val DPrime: DType = updateD(laterW, laterR)

    copy(D = DPrime, read = Set(), written = Set(), indirect = Set(), used = Set())
  }

  def updateDFence: State = {
    val DPrime: DType = {
      for (v <- variables)
        yield v -> (variables, variables, variables, variables, variables, variables, variables, variables)
    }.toMap

    copy(D = DPrime, read = Set(), written = Set(), indirect = Set(), used = Set())
  }

  def updateDCFence: State = {
    val laterW: Set[Var] = Set()
    val laterR: Set[Var] = globals
    val DPrime: DType = updateD(laterW, laterR)
    copy(D = DPrime, read = Set(), written = Set(), indirect = Set(), used = Set())
  }

  /*
  // !L(A[0]) || !L(A[1]) || ... to array.size
  def multiHighP(array: VarArray, indices: Seq[Int], p: List[Expression]): Boolean = {
    val list = {for (i <- indices)
      yield PreOp("!", L(array.array(i)))}.toList
    val Ls = orPredicates(list)
    val res = SMT.prove(Ls, p, debug)
    res
  }

  // security for array access
  def security(a: Var, index: Expression, p: List[Expression]): Security = {
    if (debug)
      println("checking array security for " + a + "[" + index + "]")

    val array = arrays(a)

    index match {
      // index is an int so access is unambiguous
      case Lit(n) =>
        if (debug)
          println("array access is unambiguous")
        val arrayVar = array.array(n)
        if (gamma.contains(arrayVar)) {
          gamma(arrayVar)
        } else if (lowP(arrayVar, p)) {
          Low
        } else {
          High
        }
      // index must be evaluated for possible indices
      case _ =>
        // check bounds - High if not provably in bounds
        // index >= 0 && index < array size
        if (!SMT.prove(BinOp("&&", BinOp(">=", index, Lit(0)), BinOp("<", index, Lit(array.array.size))), p, debug)) {
          if (debug) {
            println("array access not provably in bounds so High security: " + a + "[" + index + "]")
          }
          High
        } else {

          // check indices where array access is in domain of gamma
          val it = array.array.indices.toIterator
          var sec: Security = Low
          while (it.hasNext) {
            val i = it.next
            if (gamma.contains(array.array(i))) {
              // check SMT to prove access is possible only if gamma is High to avoid unnecessary SMT call
              if (debug) {
                println("checking array access possibility for value in gamma " + array.array(i))
              }
              if (gamma(array.array(i)) == High && SMT.proveSat(BinOp("==", index, Lit(i)), p, debug)) {
                sec = High
              }
            }
          }

          // check if any array indices not in gamma are provably High
          if (sec == Low) {
            val gammaArray: Seq[Boolean] = array.array map {a => gamma.contains(a)}
            val notInGamma = gammaArray.indices collect {case i if !gammaArray(i) => i}
            if (notInGamma.nonEmpty) {
              if (debug) {
                println("checking array access possibility for values not in gamma " + notInGamma)
              }
              if (SMT.prove(arrayAccessCheck(array, notInGamma, index), p, debug)) {
                Low
              } else {
                High
              }
            } else {
              Low
            }
          } else {
            High
          }
        }
    }
  }

  // ((index == 0) && (L(A[0]))) || ((index == 1) && (L(A[1]))) || ... to array.size
  def arrayAccessCheck(array: VarArray, indices: Seq[Int], index: Expression): Expression = {
    val list: List[Expression] = {for (i <- indices)
      yield BinOp("&&", BinOp("==", index, Lit(i)), L(array.array(i)))}.toList
    orPredicates(list)
  }
   */

  // gamma mapping
  def security(x: Var): Predicate = {
    if (debug)
      println("checking Gamma<> of " + x)
    var gammaOut: Predicate = Predicate(List(Const._true))
    if (gamma.contains(x)) {
      gammaOut = gamma(x)
    } else if (globals.contains(x)) {
      gammaOut = Predicate(List(L(x)))
    }
    if (debug)
      println("Gamma<" + x + "> is " + gammaOut)
    gammaOut
  }

  def accessSecurity(a: Access, P: Predicate): Predicate = {
    a.index match {
      case Lit(n) =>
        security(getMemoryVar(n, a.size))
      case _ =>
        // if index possibly out of bounds, return False (high security)
        if (!SMT.prove(BinOp("&&", BinOp(">=", a.index, Lit(0)), BinOp("<=", a.index, Lit(memSize))), P, debug)) {
          Predicate(List(Const._false), Set(), Set())
        } else {
          // calculate possible indices
          val possibleIndices: Seq[Int] = a.index match {
            case Lit(value) =>
              Seq(value)
            case _ =>
              for (i <- 0 to memSize by 4 if SMT.proveSat(BinOp("==", a.index, Lit(i)), P, debug))
                yield i
          }

          val securities = for (i <- possibleIndices) yield {
            val indexSecurity = security(getMemoryVar(i, a.size))
            val predicate = BinOp("==>", BinOp("==", a.index, Lit(i)), State.andPredicates(indexSecurity.predicates))
            Predicate(List(predicate), indexSecurity.exists, indexSecurity.forall)
          }
          val preds = (securities flatMap {p => p.predicates}).toList
          val exists: Set[Var] = (securities flatMap {p => p.exists}).toSet
          val forall: Set[Var] = (securities flatMap {p => p.forall}).toSet
          Predicate(preds, exists, forall)
        }
    }
  }

  // e is expression to get security of, returns predicate t
  def security(e: Expression, P: Predicate): Predicate = {
    if (debug)
      println("checking classification of " + e)
    val varE = e.variables
    val accesses = e.arrays

    val t = e match {
      case l: Lit =>
        Predicate(List(Const._true), Set(), Set())

      case _ =>
        val tList: List[Predicate] = {for (x <- varE)
          yield security(x)
        }.toList ++ {for (a <- accesses)
          yield accessSecurity(a, P)
        }.toList

        val preds = tList flatMap {p => p.predicates}
        val exists: Set[Var] = (tList flatMap {p => p.exists}).toSet
        val forall: Set[Var] = (tList flatMap {p => p.forall}).toSet

        Predicate(preds, exists, forall)
    }

    if (debug)
      println(e + " classification is " + t)
    t
  }

  def mergeIf(state2: State): State = {
    val state1 = this

    // gamma'(x) = gamma_1(x) && gamma_2(x)
    val gammaPrime: Map[Var, Predicate] = {
      for (v <- state1.gamma.keySet & state2.gamma.keySet)
        yield v -> Predicate(state1.gamma(v).predicates ++ state2.gamma(v).predicates, state1.gamma(v).exists ++ state2.gamma(v).exists, state1.gamma(v).forall ++ state2.gamma(v).forall)
    }.toMap ++ {
      for (v <- state1.gamma.keySet -- state2.gamma.keySet)
        yield v -> Predicate(L(v) :: state1.gamma(v).predicates, state1.gamma(v).exists, state1.gamma(v).forall)
    } ++ {
      for (v <- state2.gamma.keySet -- state1.gamma.keySet)
        yield v -> Predicate(L(v) :: state2.gamma(v).predicates, state2.gamma(v).exists, state2.gamma(v).forall)
    }
    val DPrime = this.mergeD(state2)

    // P1 OR P2 converted to CNF
    val PPrime = state1.P.merge(state2.P)

    copy(gamma = gammaPrime, P = PPrime, D = DPrime)
  }


  // D' = D1 intersect D2
  def mergeD(state2: State): DType = {
    State.mergeD(this.D, state2.D)
  }



    /*
  def mergePs(ps: List[List[Expression]]): List[Expression] = {
    if (ps.size == 2) {
      ps.head.merge(ps(1))
    } else if (ps.size == 1) {
      ps.head
    } else if (ps.isEmpty) {
      Predicate(List(Const._true))
    } else {
      // common is intersection of all lists
      // slightly inefficient but will do for now?
      var common = ps.head.predicates
      for (p <- ps) {
        common = common.intersect(p.predicates)
      }
      val switch = MultiSwitch.fresh

      var forallOut: Set[Var] = Set()
      var existsOut: Set[Var] = Set()
      val it = ps.indices.toIterator
      val out: List[Expression] = {
        for (p <- ps) yield {
          forallOut = forallOut ++ p.forall
          existsOut = existsOut ++ p.exists
          val i = it.next
          for (e <- p.predicates if !common.contains(e)) yield {
            BinOp("||", PreOp("!", BinOp("==", switch, Lit(i))), e)
          }
        }
      }.flatten

      Predicate(BinOp(">=", switch, Lit(0)) :: BinOp("<", switch, Lit(ps.size)) :: common ++ out, existsOut, forallOut)
    }
  }
 */

/* old mergePs implementation that decreases readability of P for merging multiple states (for array assignments)
   but is slightly smaller in size
  def mergePs(ps: List[List[Expression]]): List[Expression] = ps match {
    case Nil =>
      List()
    case p :: rest =>
      mergeP(p, mergePs(rest))
  }
*/

  def PStable(P: Predicate): Boolean = {
    val PPrime = P.subst(primed)
    if (debug) {
      println("checking " + P + " is stable")
    }
    SMT.proveImplies(P ++ R, PPrime, debug)
  }

  // for all x in dom gamma,
  //  P && R ==> Gamma(x) == Gamma'(x)
  def gammaStable(gamma: Map[Var, Predicate], P: Predicate): Boolean = {
    val gammaEqualsGammaPrime: List[Expression] = {
      for (g <- globals if gamma.contains(g))
        yield BinOp("==", gamma(g).toAnd, gamma(g).subst(primed).toAnd)
    }.toList
    if (debug) {
      println("checking Gamma: " + gamma.gammaStr + " is stable")
    }
    SMT.proveImplies(P ++ R, gammaEqualsGammaPrime, debug)
  }

  def low_or_eq(P: Predicate): Set[Var] = {
    val PAnd = P.toAnd
    val PPlusRAnd = (P ++ R).toAnd
    val lowOrEqTest = for (g <- globals)
      yield g -> BinOp("||", BinOp("==>", PAnd, L_R(g)), BinOp("==>", PPlusRAnd, BinOp("==", g, g.prime)))

    val globalLowOrEq = for ((g, pred) <- lowOrEqTest if SMT.proveExpression(pred, debug))
      yield g

    locals ++ globalLowOrEq
  }

  def restrictP(restricted: Set[Var]): Predicate = {
    val PAndPInv = P ::: P_inv
    PAndPInv.bindExists(globals -- restricted)
  }

  def restrictPInd(vars: Set[Var]): Predicate = {
    P.bindExists(vars -- knownI -- locals)
  }

  def DSubsetOf(state1: State): Boolean = {
    for (v <- variables) {
      if (!((W_r(v) subsetOf state1.W_r(v)) && (W_w(v) subsetOf state1.W_w(v))
        && (R_r(v) subsetOf state1.R_r(v)) && (R_w(v) subsetOf state1.R_w(v))
        && (I_r(v) subsetOf state1.I_r(v)) && (I_w(v) subsetOf state1.I_w(v))
        && (U_r(v) subsetOf state1.U_r(v)) && (U_w(v) subsetOf state1.U_w(v)))) {
        return false
      }
    }
    true
  }

  // update u and i
  def calculateIndirectUsed: State = {
    // all fresh variables in P
    val PVar: Set[Var] = {for (p <- P.predicates) yield p.variables}.flatten.toSet
    val known_W = knownW
    val known_R = knownR
    val indirectPrime = variables -- (PVar -- (known_W & known_R))
    val usedPrime = PVar & known_W & known_R

    copy(indirect = indirectPrime, used = usedPrime)
  }

  def getMemoryVar(index: Int, size: Int): Var = {
    if (indexToGlobal.contains(index)) {
      indexToGlobal(index)
    } else {
      Var("mem[" + index + "]", size)
    }
  }

}

object State {
  def init(definitions: Set[Definition], P_0: Option[List[Expression]], gamma_0: Option[List[GammaMapping]],
           P_invIn: List[Expression], memSize: Int, toLog: Boolean, debug: Boolean, noInfeasible: Boolean): State = {
    val globalDefs: Set[GlobalVarDef] = definitions collect {case g: GlobalVarDef => g}
    val localDefs: Set[LocalVarDef] = definitions collect {case l: LocalVarDef => l}
    val globals: Set[Var] = globalDefs map {g => g.variable}
    val labels: Map[Id, Var] = (globals map {g => (Id(g.name), g)}).toMap
    val definedLocals: Map[Id, Var] = {localDefs map {l => Id(l.variable.name) -> l.variable}}.toMap
    var memory: Map[Id, Int] = Map()
    var indexToGlobal: Map[Int, Var] = Map()
    var lastIndex = 0
    for (g <- globals) {
      memory += (Id(g.name) -> lastIndex)
      indexToGlobal += (lastIndex -> g)
      if (g.size == 32) {
        lastIndex += 4
      } else if (g.size == 64) {
        lastIndex += 8
      } else {
        throw error.InvalidProgram("global variable " + g.name + " has invalid size " + g.size)
      }
    }

    var globalOffsetTable: Map[Id, Int] = Map()
    for (g <- globals) {
      globalOffsetTable += (Id(g.name) -> lastIndex)
      lastIndex += 8
    }

    val locals: Set[Var] = (localDefs map {l => l.variable}) ++ {{
      for (i <- 0 to 30)
        yield Var("w" + i, 32)
    } ++ {
      for (i <- 0 to 30)
        yield Var("x" + i, 64)
    } ++ {
      for (i <- lastIndex to memSize by 4)
        yield Var("mem[" + i + "]", 32)
    } ++ {
      for (i <- lastIndex to memSize by 4)
        yield Var("mem[" + i + "]", 64)
    }}.toSet ++ Set(Var("sp", 64),Var("wsp", 32), Var("wzr", 32), Var("xzr", 64),
      Var("Z", 1), Var("N", 1), Var("C", 1), Var("V", 1))

    var controls: Set[Var] = Set()
    var controlled: Set[Var] = Set()
    var controlledBy: Map[Var, Set[Var]] = Map()

    if (debug) {
      //println(variables)
    }

    val ids: Set[Var] = globals ++ locals // ++ Set(CFence)

      /*
      val controllingArrays: Set[Var] = {
        for (i <- v.pred.arrays) yield {
          i.index match {
            case Lit(n) =>
              Set(arrays(i.name).array(n))
            case _ =>
              arrays(i.name).array.toSet
          }
        }
        }.flatten */
    for (g <- globalDefs) {
      val controlling: Set[Var] = g.lpredr.variables ++ g.lpredg.variables //++ controllingArrays

      if (controlling.nonEmpty) {
        controlled += g.variable
      }
      for (i <- controlling) {
        if (controlledBy.contains(i))
          controlledBy += (i -> (controlledBy(i) + g.variable))
        else
          controlledBy += (i -> Set(g.variable))
        controls += i
      }
    }

    val controlAndControlled = controls & controlled
    if (controlAndControlled.nonEmpty) {
      throw error.InvalidProgram("the following variables are both control and controlled variables: "
        + controlAndControlled.mkString(", "))
    }


    // init D - every variable maps to Var
    val D: DType = {
      for (i <- ids)
        yield i -> (ids, ids, ids, ids, ids, ids, ids, ids)
    }.toMap


    if (debug) {
      println("variables: " + ids)
      //println("array indices: " + arrayIndices)
      //println("arrays: " + arrays.keySet)
      println("globals: " + globals)
      println("locals: " + locals)
      println("controls: " + controls)
      println("controlled: " + controlled)
      println("controlled by: " + controlledBy)
    }

    // for replacing labels in predicates with variables
    val toSubst: Subst = {
      for (g <- globals)
        yield Id(g.name) -> g
    }.toMap

    val primed: Subst = {
      for (v <- ids)
        yield v -> v.prime
    }.toMap

    val initMem: List[Expression] = {for ((v, i) <- memory) yield {
      BinOp("==", Access(Lit(i), labels(v).size), labels(v))
    }}.toList ++ {for ((v, i) <- globalOffsetTable) yield {
      BinOp("==", Access(Lit(i), 64), Lit(memory(v)))
    }}.toList

    // initialise R & G
    val P_inv = Predicate(P_invIn map {i => i.subst(toSubst)}).add(initMem)

    var R_var: Map[Var, List[(Expression, Expression)]] = Map()
    for (g <- globalDefs) {
      g.rvar match {
        case Some(rvars) =>
          R_var += (g.variable -> (rvars map {rvar => (rvar.condition.subst(toSubst), rvar.relation.subst(toSubst))}))
        case None =>
      }
    }

    val R_var_pred: List[Expression] = {
      for (g <- R_var.keys) yield {
        for ((c, r) <- R_var(g))
          yield if (c == Const._true) {
           r
          } else {
            BinOp("==>", c, r)
          }
      }
    }.flatten.toList
    val P_invAnd = P_inv.toAnd

    val R_loc: List[Expression] = {
      for (l <- locals) yield
        BinOp("==", l, l.prime)
    }.toList

    // R == P_inv ==> primed(P_inv) && R_var
    val R = Predicate(BinOp("==>", P_invAnd, P_invAnd.subst(primed)) :: R_var_pred ++ R_loc)

    var G_var: Map[Var, List[(Expression, Expression)]] = Map()
    for (g <- globalDefs) {
      g.gvar match {
        case Some(gvars) =>
          G_var += (g.variable -> (gvars map {gvar => (gvar.condition.subst(toSubst), gvar.relation.subst(toSubst))}))
        case None =>
      }
    }

    val G_var_pred: List[Expression] = {
      for (g <- G_var.keys) yield {
        for ((c, r) <- G_var(g))
          yield if (c == Const._true) {
            r
          } else {
            BinOp("==>", c, r)
          }
      }
    }.flatten.toList

    val G = Predicate(BinOp("==>", P_invAnd, P_invAnd.subst(primed)) :: G_var_pred)

    //val G = Predicate(guarantee map {i => i.subst(idToVar)})

    // initialise P - true by default
    val P: Predicate = P_0 match {
      case None =>
        Predicate(List(Const._true))

      case Some(p) =>
        Predicate(p map {i => i.subst(toSubst)})
    }

    // check P_0 is stable
    val PPrime = P.subst(primed)
    if (!SMT.proveImplies(P ++ R, PPrime, debug)) {
      throw error.InvalidProgram("P_0 is not stable")
    }

    // init L - map variables to their L predicates
    val L_R: Map[Var, Expression] = {
      for (v <- globalDefs) yield {
        v.variable -> v.lpredr.subst(toSubst)
      }
    }.toMap
    val L_G: Map[Var, Expression] = {
      for (v <- globalDefs) yield {
        v.variable -> v.lpredg.subst(toSubst)
      }
    }.toMap

    // L == L_R && L_G
    val L: Map[Var, Expression] = {
      for (g <- globals) yield {
        val lR = L_R(g)
        val lG = L_G(g)
        if (lR == lG) {
          g -> lR
        } else {
          g -> BinOp("&&", lR, lG)
        }
      }
    }.toMap

    val PAnd = P.toAnd
    val PPlusRAnd = (P ++ R).toAnd
    val lowOrEqTest = for (g <- globals)
      yield g -> BinOp("||", BinOp("==>", PAnd, L_R(g)), BinOp("==>", PPlusRAnd, BinOp("==", g, g.prime)))

    val globalLowOrEq = for ((g, pred) <- lowOrEqTest if SMT.proveExpression(pred, debug))
      yield g
    val low_or_eq: Set[Var] = locals ++ globalLowOrEq

    // init Gamma
    val gamma: Map[Var, Predicate] = gamma_0 match {
      // all locals low by default
      case None => (locals map {l => l -> Predicate(List(Const._false))}).toMap
      // user provided
      case Some(gs) => {
        //gs flatMap {g => g.toPair(arrays)}
        gs map {g => labels(g.label) -> Predicate(List(g.security.subst(toSubst)))}
      }.toMap
    }

    // check gamma domain is correct
    if (!(gamma.keySet subsetOf low_or_eq))
      throw error.InvalidProgram("provided gamma has invalid domain (" + gamma.keySet.mkString(", ")
        + "), as domain is not " + low_or_eq.mkString(", "))

    val gammaEqualsGammaPrime: List[Expression] = {for (g <- globals if gamma.contains(g))
      yield BinOp("==", gamma(g).toAnd, gamma(g).subst(primed).toAnd)
    }.toList
    if (!SMT.proveImplies(P ++ R, gammaEqualsGammaPrime, debug)) {
      throw error.InvalidProgram("Gamma is not stable")
    }

    if (debug) {
      println("L_R: " + L_R)
      println("L_G: " + L_G)
      println("L: " + L)
      println("R: " + R)
      println("R_var: " + R_var)
      println("P_inv: " + P_inv)
      println("G: " + G)
    }
    if (toLog) {
      println("Gamma: " + gamma.gammaStr)
      println("P: " + P)
      println("D: " + D.DStr)
    }

    State(
      gamma = gamma,
      D = D,
      P = P,
      P_inv = P_inv,
      R_var = R_var,
      R = R,
      G = G,
      G_var = G_var,
      L_R = L_R,
      L_G = L_G,
      L = L,
      globals = globals,
      locals = locals,
      labels = labels,
      definedLocals = definedLocals,
      controls = controls,
      controlled = controlled,
      controlledBy = controlledBy,
      variables = ids,
      primed = primed,
      read = Set(),
      written = Set(),
      indirect = Set(),
      used = Set(),
      //arrayIndices = arrayIndices,
      //arrays = arrays,
      toLog = toLog,
      debug = debug,
      noInfeasible = noInfeasible,
      memSize = memSize,
      memory = memory,
      globalOffsetTable = globalOffsetTable,
      indexToGlobal = indexToGlobal
    )
  }

  def orPredicates(exprs: List[Expression]): Expression = {
    if (exprs.size == 1) {
      exprs.head
    } else {
      exprs match {
        case Nil =>
          Const._false
        case expr :: rest =>
          val xs = orPredicates(rest)
          val x =  BinOp("||", expr, xs)
          x
      }
    }
  }

  def andPredicates(exprs: List[Expression]): Expression = {
    if (exprs.size == 1) {
      exprs.head
    } else {
      exprs match {
        case Nil =>
          Const._true

        case expr :: rest =>
          val xs = andPredicates(rest)
          val x =  BinOp("&&", expr, xs)
          x
      }
    }
  }

  def mergeD(D1: DType,
             D2: DType): DType = {
    for (v <- D1.keySet) yield {
      v -> ((D1(v)._1 intersect D2(v)._1,
        D1(v)._2 intersect D2(v)._2,
        D1(v)._3 intersect D2(v)._3,
        D1(v)._4 intersect D2(v)._4,
        D1(v)._5 intersect D2(v)._5,
        D1(v)._6 intersect D2(v)._6,
        D1(v)._7 intersect D2(v)._7,
        D1(v)._8 intersect D2(v)._8))
    }
    }.toMap

}