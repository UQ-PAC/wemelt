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
    copy(exists = exists ++ toAdd)
  }

  def addForall(toAdd: Set[Var]): Predicate = {
    copy(forall = forall ++ toAdd)
  }

  def ++(other: Predicate): Predicate = combine(other)
  def :::(other: Predicate): Predicate = combine(other)

  def subst(toSubst: Subst): Predicate = {
    copy(predicates = predicates map (p => p.subst(toSubst)))
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
}

case class State(
  gamma: Map[Id, Predicate],
  //D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])], // W_w, W_r, R_w, R_r
  P: Predicate,
  P_inv: Predicate,
  R_var: Map[Id, List[(Expression, Expression)]],
  R: Predicate,
  G: Predicate,

  L_R: Map[Id, Expression],
  L_G: Map[Id, Expression],
  L: Map[Id, Expression],

  globals: Set[Id],
  locals: Set[Id],

  controls: Set[Id],
  controlled: Set[Id],
  controlledBy: Map[Id, Set[Id]], // CLed(name)

  variables: Set[Id],
  primed: Subst,

  //read: Set[Id],
  //written: Set[Id],

  //arrayIndices: Set[Id],
  //arrays: Map[Id, IdArray],

  toLog: Boolean,
  debug: Boolean,
  noInfeasible: Boolean) {

  //def W_w(v: Id): Set[Id] = D(v)._1
  //def W_r(v: Id): Set[Id] = D(v)._2
  //def R_w(v: Id): Set[Id] = D(v)._3
  //def R_r(v: Id): Set[Id] = D(v)._4

  def log(): Unit = {
    if (toLog) {
      println("gamma: " + gamma.gammaStr)
      println("P: " + P)
      //println("D: " + D.DStr)
    }
  }

  // update P and Gamma after assignment
  def assignUpdate(id: Id, arg: Expression, t: Predicate): State = {
    val v = id.toVar

    // create mapping from variable to fresh variable
    val fresh = Var.fresh(id.name)
    val toSubst: Subst = Map(v -> fresh)

    // substitute variable in P for fresh variable
    val PReplace = P.subst(toSubst)

    // substitute variable in expression for fresh variable
    val argReplace = arg.subst(toSubst)

    // add new assignment statement to P
    val PPrime = PReplace.add(BinOp("==", v, argReplace)).addExists(Set(fresh))

    // calculate new_var
    val varE = arg.variables
    val varLY: Set[Id] = {
      for (y <- varE -- gamma.keySet)
        yield L(y).variables
    }.flatten
    val new_var: Set[Id] = Set(id) ++ varE ++ varLY

    // calculate weaker
    val toSubstC: Subst = Map(v -> arg) // for c[e/x]
    var weaker: Set[Id] = Set()
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

    // calculate equals - this can be improved too
    // separate method for identity relation? check all identity relations at the start?
    val equals: Set[Id] = {
      for (y <- R_var.keySet)
        yield {
          // check P ==> c && r is identity relation
          for ((c, r) <- R_var(y) if (r == BinOp("==", y.toVar, y.toVar.prime) || r == BinOp("==", y.toVar.prime, y.toVar))
            && (c == Const._true || SMT.proveImplies(PPrime ++ P_inv, c, debug)))
            yield y
        }
    }.flatten

    val domM = new_var ++ weaker -- equals

    var exists: Set[Var] = Set() // set of newly created variables to bind
    // map all of domM to fresh temporary variables - probably change to different fresh allocator
    val m: Subst = {
      for (v <- domM)
        yield {
          val newFresh = v.toVar.fresh
          exists += newFresh
          v.toVar -> newFresh
        }
    }.toMap

    val mPlusMPrime: Subst = m ++ {
      for (v <- domM)
        yield v.toVar.prime -> v.toVar
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
          BinOp("==>", c, r.subst(mPlusMPrime))
        }
    }
    }.flatten.toList

    if (debug) {
      println("P +: " + PPlus)
      println("+ R: " + RPlus)
    }

    val PPlusR = PPlus.add(RPlus)

    val domGamma = low_or_eq(PPlusR)
    val gammaPrime = if (domGamma.contains(id)) {
      gamma + (id -> t)
    } else {
      gamma
    }

    val gammaPrimeRestrict = gammaPrime -- (gammaPrime.keySet -- domGamma)
    val gammaPlusR: Map[Id, Predicate] = {
      for (g <- gammaPrimeRestrict.keySet)
        yield g -> gammaPrimeRestrict(g).subst(m).addExists(exists)
    }.toMap

    if (debug) {
      println("assigning " + arg + " to " + id + ":")
      println("P: " + P)
      println("P': " + PPrime)
      println("P + R: " + PPlusR)
      println("Gamma + R: " + gammaPlusR.gammaStr)
    }
    copy(P = PPlusR, gamma = gammaPlusR)
  }

  // update P and Gamma with loop/if guard
  def guardUpdate(guard: Expression): State = {
    // add guard to P
    val PPrime = P.add(guard)

    // calculate new_var
    val new_var: Set[Id] = guard.variables

    // calculate equals - this can be improved too
    // separate method for identity relation? check all identity relations at the start?
    val equals: Set[Id] = {
      for (y <- R_var.keySet)
        yield {
          // check P ==> c && r is identity relation
          for ((c, r) <- R_var(y) if (r == BinOp("==", y.toVar, y.toVar.prime) || r == BinOp("==", y.toVar.prime, y.toVar))
            && (c == Const._true || SMT.proveImplies(PPrime ++ P_inv, c, debug)))
            yield y
        }
    }.flatten

    val domM = new_var -- equals

    var exists: Set[Var] = Set() // set of newly created variables to bind
    // map all of domM to fresh temporary variables - probably change to different fresh allocator
    val m: Subst = {
      for (v <- domM)
        yield {
          val newFresh = v.toVar.fresh
          exists += newFresh
          v.toVar -> newFresh
        }
    }.toMap

    val mPlusMPrime: Subst = m ++ {
      for (v <- domM)
        yield v.toVar.prime -> v.toVar
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
          BinOp("==>", c, r.subst(mPlusMPrime))
        }
    }
    }.flatten.toList

    if (debug) {
      println("P +: " + PPlus)
      println("+ R: " + RPlus)
    }

    val PPlusR = PPlus.add(RPlus)

    val domGamma = low_or_eq(PPlusR)
    val gammaPrimeRestrict = gamma -- (gamma.keySet -- domGamma)
    val gammaPlusR: Map[Id, Predicate] = {
      for (g <- gammaPrimeRestrict.keySet)
        yield g -> gammaPrimeRestrict(g).subst(m).addExists(exists)
    }.toMap

    if (debug) {
      println("updating P and Gamma with guard " + guard)
      println("P: " + P)
      println("P': " + PPrime)
      println("P + R: " + PPlusR)
      println("Gamma + R: " + gammaPlusR.gammaStr)
    }
    copy(P = PPlusR, gamma = gammaPlusR)
  }

  /*
  def assignCAS(lhs: Id, x: Id, r1: Expression, r2: Expression): State = {
    val _lhs = lhs.toVar
    val _x = x.toVar

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
  def arrayAssign(a: Id, index: Expression, arg: Expression, possible: Seq[Int]): State = {
    val v = a.toVar
    // create mapping from variable to fresh variable
    val toSubst: Subst = Map(v -> Var.fresh(a.name))

    val POut = if (possible.size == 1) {
      // unambiguous access case
      val PReplace = P map (p => p.subst(toSubst, possible.head))
      // substitute variable in expression for fresh variable
      val argReplace = arg.subst(toSubst, possible.head)

      val indexToSubst: Subst = {
        for (j <- index.variables)
          yield j -> j.toVar
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
            yield j -> j.toVar
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
  /*
  def resetReadWrite(): State = {
    copy(read = Set(), written = Set())
  }

  def updateRead(id: Id): State = {
    if (debug)
      println("updating read (" + read + ") with " + id)
    copy(read = read + id)
  }

  def updateRead(id: Set[Id]): State = {
    if (debug)
      println("updating read (" + read + ") with " + id)
    copy(read = read ++ id)
  }

  def updateWritten(id: Id): State = {
    if (debug)
      println("updating written (" + written + ") with " + id)
    copy(written = written + id)
  }

  def updateWritten(id: Set[Id]): State = {
    if (debug)
      println("updating written (" + written + ") with " + id)
    copy(written = written ++ id)
  }
   */

  /*
  def updateWritten(array: IdArray): State = {
    val ids: Set[Id] = {for (i <- array.array.indices)
      yield array.array(i)}.toSet
    if (debug)
      println("updating written (" + written + ") with " + ids)
    copy(written = written ++ ids)
  }

  def updateRead(array: IdArray): State = {
    val ids: Set[Id] = {for (i <- array.array.indices)
      yield array.array(i)}.toSet
    if (debug)
      println("updating read (" + read + ") with " + ids)
    copy(read = read ++ ids)
  } */

  /*
  def knownW: Set[Id] = {
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

  def knownR: Set[Id] = {
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

  def updateD(laterW: Set[Id], laterR: Set[Id]): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    val knownw = knownW
    val knownr = knownR
    if (debug) {
      println("knownW: " + knownw)
      println("knownR: " + knownr)
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
      i -> (w_w, w_r, r_w, r_r)
    }
  }.toMap

  def updateDAssign(x: Id, e: Expression) : State = {
    val varE = e.variables // var(e)
    val canForward = varE.intersect(globals).isEmpty
    val laterW: Set[Id] = Set(x) ++ varE
    val laterR: Set[Id] = if (!canForward) {
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
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = updateD(laterW, laterR)

    // updated forwarding
    val DPrimePrime = if (canForward) {
      val w_r = {for (v <- read)
        yield W_r(v)
        }.flatten -- written
      val r_r = {for (v <- read)
        yield R_r(v)
        }.flatten -- read
      DPrime + (x -> (DPrime(x)._1, w_r, DPrime(x)._3, r_r))
    } else {
      DPrime
    }

    copy(D = DPrimePrime, read = Set(), written = Set())
  }
   */

  /*
  def updateDArrayAssign(x: Id, e: Expression) : State = {
    val varE = e.variables // var(e)
    val laterW: Set[Id] = varE
    val laterR: Set[Id] = varE.intersect(globals)
    if (debug) {
      println("laterW: " + laterW)
      println("laterR: " + laterR)
      println("rd: " + read)
      println("wr: " + written)
    }
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = updateD(laterW, laterR)

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
  def updateDCAS(r3: Id, x: Id, r1: Expression, r2: Expression) : State = {
    val varR1 = r1.variables
    val varR2 = r2.variables
    val laterW: Set[Id] = Set(x, r3) ++ varR1 ++ varR2
    val laterR: Set[Id] = Set(r3, x) ++ ((varR1 ++ varR2) & globals)
    if (debug) {
      println("laterW: " + laterW)
      println("laterR: " + laterR)
      println("rd: " + read)
      println("wr: " + written)
    }
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = updateD(laterW, laterR)

    copy(D = DPrime, read = Set(), written = Set())
  }

  def updateDGuard(b: Expression) : State = {
    val varB = b.variables // var(b)
    val laterW: Set[Id] = globals ++ varB + CFence
    val laterR: Set[Id] = globals & varB

    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = updateD(laterW, laterR)

    copy(D = DPrime, read = Set(), written = Set())
  }

  def updateDFence: State = {
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
      for (v <- variables)
        yield v -> (variables, variables, variables, variables)
    }.toMap

    copy(D = DPrime, read = Set(), written = Set())
  }

  def updateDCFence: State = {
    val laterW: Set[Id] = Set()
    val laterR: Set[Id] = globals
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = updateD(laterW, laterR)
    copy(D = DPrime, read = Set(), written = Set())
  }
   */

  /*
  // !L(A[0]) || !L(A[1]) || ... to array.size
  def multiHighP(array: IdArray, indices: Seq[Int], p: List[Expression]): Boolean = {
    val list = {for (i <- indices)
      yield PreOp("!", L(array.array(i)))}.toList
    val Ls = orPredicates(list)
    val res = SMT.prove(Ls, p, debug)
    res
  }

  // security for array access
  def security(a: Id, index: Expression, p: List[Expression]): Security = {
    if (debug)
      println("checking array security for " + a + "[" + index + "]")

    val array = arrays(a)

    index match {
      // index is an int so access is unambiguous
      case Lit(n) =>
        if (debug)
          println("array access is unambiguous")
        val arrayId = array.array(n)
        if (gamma.contains(arrayId)) {
          gamma(arrayId)
        } else if (lowP(arrayId, p)) {
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
  def arrayAccessCheck(array: IdArray, indices: Seq[Int], index: Expression): Expression = {
    val list: List[Expression] = {for (i <- indices)
      yield BinOp("&&", BinOp("==", index, Lit(i)), L(array.array(i)))}.toList
    orPredicates(list)
  }
   */

  // gamma mapping
  def security(x: Id): Predicate = {
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

  // e is expression to get security of, returns predicate t
  def security(e: Expression): Predicate = {
    if (debug)
      println("checking classification of " + e)
    val varE = e.variables

    val t = e match {
      case l: Lit =>
        Predicate(List(Const._true), Set(), Set())

      case _ =>
        val tList: List[Predicate] = {for (x <- varE)
          yield security(x)
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
    val gammaPrime: Map[Id, Predicate] = {
      for (v <- state1.gamma.keySet & state2.gamma.keySet)
        yield v -> Predicate(state1.gamma(v).predicates ++ state2.gamma(v).predicates, state1.gamma(v).exists ++ state2.gamma(v).exists, state1.gamma(v).forall ++ state2.gamma(v).forall)
    }.toMap ++ {
      for (v <- state1.gamma.keySet -- state2.gamma.keySet)
        yield v -> Predicate(L(v) :: state1.gamma(v).predicates, state1.gamma(v).exists, state1.gamma(v).forall)
    } ++ {
      for (v <- state2.gamma.keySet -- state1.gamma.keySet)
        yield v -> Predicate(L(v) :: state2.gamma(v).predicates, state2.gamma(v).exists, state2.gamma(v).forall)
    }
    //val DPrime = this.mergeD(state2)

    // P1 OR P2 converted to CNF
    val PPrime = state1.P.merge(state2.P)

    copy(gamma = gammaPrime, P = PPrime)
  }


  def mergePs(ps: List[Predicate]): Predicate = {
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
  def gammaStable(gamma: Map[Id, Predicate], P: Predicate): Boolean = {
    val gammaEqualsGammaPrime: List[Expression] = {
      for (g <- globals if gamma.contains(g))
        yield BinOp("==", gamma(g).toAnd, gamma(g).subst(primed).toAnd)
    }.toList
    if (debug) {
      println("checking Gamma: " + gamma.gammaStr + " is stable")
    }
    SMT.proveImplies(P ++ R, gammaEqualsGammaPrime, debug)
  }

  def low_or_eq(P: Predicate): Set[Id] = {
    val PAnd = P.toAnd
    val PPlusRAnd = (P ++ R ++ P_inv).toAnd
    val lowOrEqTest = for (g <- globals)
      yield g -> BinOp("||", BinOp("==>", PAnd, L_R(g)), BinOp("==>", PPlusRAnd, BinOp("==", g.toVar, g.toVar.prime)))

    val globalLowOrEq = for ((g, pred) <- lowOrEqTest if SMT.proveExpression(pred, debug))
      yield g

    locals ++ globalLowOrEq
  }
}

object State {
  def init(definitions: Set[Definition], P_0: Option[List[Expression]], gamma_0: Option[List[GammaMapping]],
           P_invIn: List[Expression], guarantee: List[Expression], toLog: Boolean, debug: Boolean, noInfeasible: Boolean): State = {
    val globalDefs: Set[GlobalVarDef] = definitions collect {case g: GlobalVarDef => g}
    val localDefs: Set[LocalVarDef] = definitions collect {case l: LocalVarDef => l}

    val globals: Set[Id] = globalDefs map {g => g.name}
    val locals: Set[Id] = localDefs map {l => l.name}

    var controls: Set[Id] = Set()
    var controlled: Set[Id] = Set()
    var controlledBy: Map[Id, Set[Id]] = Map()

    if (debug) {
      //println(variables)
    }

    val ids: Set[Id] = globals ++ locals // ++ Set(CFence)

      /*
      val controllingArrays: Set[Id] = {
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
      val controlling: Set[Id] = g.lpredr.variables ++ g.lpredg.variables //++ controllingArrays

      if (controlling.nonEmpty) {
        controlled += g.name
      }
      for (i <- controlling) {
        if (controlledBy.contains(i))
          controlledBy += (i -> (controlledBy(i) + g.name))
        else
          controlledBy += (i -> Set(g.name))
        controls += i
      }
    }

    val controlAndControlled = controls & controlled
    if (controlAndControlled.nonEmpty) {
      throw error.InvalidProgram("the following variables are both control and controlled variables: "
        + controlAndControlled.mkString(", "))
    }

    /*
    // init D - every variable maps to Var
    val D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
      for (i <- ids)
        yield i -> (ids, ids, ids, ids)
    }.toMap
     */

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

    // for replacing Ids in predicates with Vars
    val idToVar: Subst = ({
      for (v <- ids)
        yield v -> v.toVar
      } ++ {
      for (v <- ids)
        yield v.prime -> v.toVar.prime
      }).toMap
    /* ++ {
      for (v <- arrays.keySet)
        yield v -> v.toVar
      }.toMap */

    val primed: Subst = {for (v <- ids)
      yield v.toVar -> v.toVar.prime
    }.toMap

    // initialise R & G
    val P_inv = Predicate(P_invIn map {i => i.subst(idToVar)})

    var R_var: Map[Id, List[(Expression, Expression)]] = Map()
    for (g <- globalDefs) {
      g.rvar match {
        case Some(rvars) =>
          R_var += (g.name -> (rvars map {rvar => (rvar.condition.subst(idToVar), rvar.relation.subst(idToVar))}))
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
        BinOp("==", l.toVar, l.toVar.prime)
    }.toList

    // R == P_inv ==> primed(P_inv) && R_var
    val R = Predicate(BinOp("==>", P_invAnd, P_invAnd.subst(primed)) :: R_var_pred ++ R_loc)

    val G = Predicate(guarantee map {i => i.subst(idToVar)})

    // initialise P - true by default
    val P: Predicate = P_0 match {
      case None =>
        Predicate(List(Const._true))

      case Some(p) =>
        Predicate(p map {i => i.subst(idToVar)})
    }

    // check P_0 is stable
    val PPrime = P.subst(primed)
    if (!SMT.proveImplies(P ++ R, PPrime, debug)) {
      throw error.InvalidProgram("P_0 is not stable")
    }

    // init L - map variables to their L predicates
    val L_R: Map[Id, Expression] = {
      for (v <- globalDefs) yield {
        val lpredVar = v.lpredr.subst(idToVar)
        v.name -> lpredVar
      }
    }.toMap
    val L_G: Map[Id, Expression] = {
      for (v <- globalDefs) yield {
        val lpredVar = v.lpredg.subst(idToVar)
        v.name -> lpredVar
      }
    }.toMap

    // L == L_R && L_G
    val L: Map[Id, Expression] = {
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

    // init Gamma
    val gamma: Map[Id, Predicate] = gamma_0 match {
      // empty gamma by default if user hasn't provided
      case None => Map()
      // user provided
      case Some(gs) => {
        //gs flatMap {g => g.toPair(arrays)}
        gs map {g => g.variable -> Predicate(List(g.security.subst(idToVar)))}
      }.toMap
    }
    val PAnd = P.toAnd
    val PPlusRAnd = (P ++ R).toAnd
    val lowOrEqTest = for (g <- globals)
      yield g -> BinOp("||", BinOp("==>", PAnd, L_R(g)), BinOp("==>", PPlusRAnd, BinOp("==", g.toVar, g.toVar.prime)))

    val globalLowOrEq = for ((g, pred) <- lowOrEqTest if SMT.proveExpression(pred, debug))
      yield g
    val low_or_eq: Set[Id] = locals ++ globalLowOrEq

    // check gamma domain only contains any variables in low_or_eq
    if (!(gamma.keySet subsetOf low_or_eq))
      throw error.InvalidProgram("provided gamma has invalid domain (" + gamma.keySet.mkString(", ")
        + "), as domain is not a subset of " + low_or_eq.mkString(", "))

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
      //println("D: " + D.DStr)
    }

    State(
      gamma = gamma,
      //D = D,
      P = P,
      P_inv = P_inv,
      R_var = R_var,
      R = R,
      G = G,
      L_R = L_R,
      L_G = L_G,
      L = L,
      globals = globals,
      locals = locals,
      controls = controls,
      controlled = controlled,
      controlledBy = controlledBy,
      variables = ids,
      primed = primed,
      //read = Set(),
      //written = Set(),
      //arrayIndices = arrayIndices,
      //arrays = arrays,
      toLog = toLog,
      debug = debug,
      noInfeasible = noInfeasible
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

  def mergeD(D1: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])],
             D2: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])]): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    for (v <- D1.keySet) yield {
      v -> ((D1(v)._1 intersect D2(v)._1,
        D1(v)._2 intersect D2(v)._2,
        D1(v)._3 intersect D2(v)._3,
        D1(v)._4 intersect D2(v)._4))
    }
    }.toMap

}