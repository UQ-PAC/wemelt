package tool

case class State(
  gamma: Map[Id, Security],
  D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])], // W_w, W_r, R_w, R_r
  P: List[Expression],

  L: Map[Id, Expression],

  globals: Set[Id],
  locals: Set[Id],

  noReadWrite: Set[Id],
  readWrite: Set[Id],
  noWrite: Set[Id],

  stable: Set[Id],

  controls: Set[Id],
  controlled: Set[Id],
  controlledBy: Map[Id, Set[Id]], // CLed(name)

  variables: Set[Id],

  read: Set[Id],
  written: Set[Id],

  arrayIndices: Set[Id],
  arrays: Map[Id, IdArray],

  nonblocking: Boolean, // whether the nonblocking rule is currently being applied
  nonblockingDepth: Int, // how many layers of the nonblocking rule are currently being applied

  toLog: Boolean,
  debug: Boolean) {

  def W_w(v: Id): Set[Id] = D(v)._1
  def W_r(v: Id): Set[Id] = D(v)._2
  def R_w(v: Id): Set[Id] = D(v)._3
  def R_r(v: Id): Set[Id] = D(v)._4

  def log = {
    if (toLog) {
      println("gamma: " + gamma.gammaStr)
      println("P: " + P.PStr)
      println("D: " + D.DStr)
    }
  }

  // update P with strongest post-condition after assignment
  def assign(id: Id, arg: Expression): State = {
    val v = id.toVar
    // create mapping from variable to fresh variable
    val toSubst: Subst = Map(v -> Var.fresh(id.name))

    // substitute variable in P for fresh variable
    val PReplace = P map (p => p.subst(toSubst))

    // substitute variable in expression for fresh variable
    val argReplace = arg.subst(toSubst)

    // add new assignment statement to P
    val PPrime = BinOp("==", v, argReplace) :: PReplace

    // restrict PPrime to stable variables
    val PPrimeRestrict = State.restrictP(PPrime, stable)

    if (debug) {
      println("assigning " + arg + " to " + id + ":")
      println("P: " + P.PStr)
      println("P': " + PPrimeRestrict.PStr)
    }
    copy(P = PPrimeRestrict)
  }

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

    // add assignments to P
    val PPrime = BinOp("==", _lhs, Question(BinOp("==", _x, _r1), Lit(1), Lit(0))) :: BinOp("==", _x, Question(BinOp("==", _x, _r1), _r2, _x)) :: PReplace

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
  def arrayAssign(a: Id, index: Expression, arg: Expression): State = {
    val v = a.toVar
    // create mapping from variable to fresh variable
    val toSubst: Subst = Map(v -> Var.fresh(a.name))

    // substitute variable in P for fresh variable
    val PReplace = P map (p => p.subst(toSubst))

    // substitute variable in expression for fresh variable
    val argReplace = arg.subst(toSubst)

    val indexToSubst: Subst = {
      for (i <- index.variables)
        yield i -> i.toVar
      }.toMap ++ toSubst

    val indexSubst = index.subst(indexToSubst)

    // add new assignment statement to P
    val PPrime = BinOp("==", VarAccess(v, indexSubst), argReplace) :: PReplace

    // restrict PPrime to stable variables
    val PPrimeRestrict = State.restrictP(PPrime, stable)

    if (debug) {
      println("assigning " + arg + " to " + a + "[" + index + "]" + ":")
      println("P: " + P.PStr)
      println("P': " + PPrimeRestrict.PStr)
    }
    copy(P = PPrimeRestrict)
  }

  def addToP(expr: Expression): State = {
    copy(P = expr :: P)
  }

  def resetReadWrite(): State = {
    copy(read = Set(), written = Set())
  }

  def updateRead(id: Id): State = {
    if (debug)
      println("updating read (" + read + ") with " + id)
    copy(read = read + id)
  }

  def updateWritten(id: Id): State = {
    if (debug)
      println("updating written (" + written + ") with " + id)
    copy(written = written + id)
  }

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
  }

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
    val laterW: Set[Id] = globals ++ varB
    val laterR: Set[Id] = globals & varB

    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = updateD(laterW, laterR)

    copy(D = DPrime, read = Set(), written = Set())
  }

  def updateDFence(): State = {
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
      for (v <- variables)
        yield v -> (variables, variables, variables, variables)
    }.toMap

    copy(D = DPrime, read = Set(), written = Set())
  }

  def lowP(id: Id, p: List[Expression]): Boolean = {
    if (debug)
      println("checking lowP for " + id)
    // prove if L(x) holds given P
    SMT.prove(L(id), p, debug)
  }

  def highP(id: Id, p: List[Expression]): Boolean = {
    if (debug)
      println("checking highP for " + id)
    // prove if L(x) doesn't hold given P
    SMT.prove(PreOp("!", L(id)), p, debug)
  }

  // security for array access
  def security(a: Id, index: Expression, p: List[Expression]): Security = {
    if (debug)
      println("checking security for " + a + "[" + index + "]")
    val array = arrays(a)

    index match {
      // index is an int
      case Lit(n) =>
        val arrayId = array.array(n)
        if (gamma.contains(arrayId)) {
          gamma(arrayId)
        } else if (SMT.prove(PreOp("!", L(arrayId)), p, debug)) {
          Low
        } else {
          High
        }
      // index must be evaluated for possible indices
      case _ =>
        // check bounds
        // index >= 0 && index < array size
        if (!SMT.prove(BinOp("&&", BinOp(">=", index, Lit(0)), BinOp("<", index, Lit(array.array.size))), p, debug)) {
          if (debug) {
            println("array access not provably inbounds so High security: " + a + "[" + index + "]")
          }
          return High
        }

        // probably this could be more efficient/neater somehow
        if (stable.contains(array.array(0))) { // based on assumption that all array indices share a mode
          val it = array.array.indices.toIterator
          var sec: Security = Low
          while (it.hasNext && sec == Low) {
            val i = it.next
            if (gamma.contains(array.array(i))) {
              if (SMT.proveSat(BinOp("==", index, Lit(i)), p, debug)) {
                sec = gamma(array.array(i))
              } else if (SMT.prove(BinOp("&&", BinOp("==", index, Lit(i)), L(array.array(i))), p, debug)) {
                sec = Low
              } else {
                sec = High
              }
            }
          }
          sec
        } else {
          if (SMT.prove(arrayAccessCheck(array, index), p, debug)) {
            Low
          } else {
            High
          }
        }
    }
  }

  // ((index == 0) && (L(A[0]))) || ((index == 1) && (L(A[1]))) || ... to array.size
  def arrayAccessCheck(array: IdArray, index: Expression): Expression = {
    val list = {for (i <- array.array.indices)
      yield BinOp("&&", BinOp("==", index, Lit(i)), L(array.array(i)))}.toList
    orPredicates(list)
  }

  def orPredicates(exprs: List[Expression]): Expression = exprs match {
    case Nil =>
      Const._false

    case expr :: rest =>
      val xs = orPredicates(rest)
      val x =  BinOp("||", expr, xs)
      x
  }

  // x is variable to get security of, p is P value given so can substitute in P_a etc.
  def security(x: Id, p: List[Expression]): Security = {
    if (debug)
      println("checking security for " + x)
    var sec: Security = High
    if (gamma.contains(x)) {
      sec = gamma(x)
    } else {
      if (lowP(x, p)) {
        sec = Low
      } // true/LOW if L(x) holds given P, false/HIGH otherwise
    }
    if (debug)
      println(x + " security is " + sec)
    sec
  }

  // e is expression to get security of, p is P value given so can substitute in P_a etc.
  def security(e: Expression, p: List[Expression]): Security = {
    if (debug)
      println("checking security for " + e)
    var sec: Security = Low
    val it = e.variables.toIterator
    // if x security is high, return, otherwise keep checking
    while (it.hasNext && sec == Low) {
      val x: Id = it.next()
      sec = security(x, p)
    }
    val it2 = e.arrays.toIterator
    while (it2.hasNext && sec == Low) {
      val a: Access = it2.next()
      sec = security(a.name, a.index, p)
    }

    if (debug)
      println(e + " security is " + sec)
    sec
  }

  // update gamma with new value t mapped to x, if x is in the domain of gamma
  def updateGamma(x: Id, t: Security): State = {
    if (gamma.contains(x)) {
      val gammaPrime = gamma + (x -> t)
      copy(gamma = gammaPrime)
    } else {
      this
    }
  }

  def updateGammaArray(a: IdArray, indices: Seq[Int], t: Security): State = {
    val toUpdate = if (indices.size == 1) {
      for (i <- indices if gamma.contains(a.array(i))) yield {
        a.array(i) -> t
      }
    } else {
      for (i <- indices if gamma.contains(a.array(i))) yield {
        if (gamma(a.array(i)) == High) {
          a.array(i) -> High
        } else {
          a.array(i) -> t
        }
      }
    }
    val gammaPrime = gamma ++ toUpdate
    copy (gamma = gammaPrime)
  }

  def updateGammaCAS(x: Id, t: Security): State = {
    if (gamma.contains(x)) {
      val toUpdate = if (gamma(x) == High) {
        x -> High
      } else {
        x -> t
      }
      val gammaPrime = gamma + toUpdate
      copy(gamma = gammaPrime)
    } else {
      this
    }
  }

  // update gamma with new value t mapped to x, regardless if x was in domain of gamma previously
  def updateGammaDomain(x: Id, t: Security): State = {
    val gammaPrime = gamma + (x -> t)
    copy(gamma = gammaPrime)
  }

  def removeGamma(x: Id): State = {
    val gammaPrime = gamma - x
    copy(gamma = gammaPrime)
  }

  // local variables should never be restricted
  def restrictP(restricted: Set[Id]): List[Expression] = {
    State.restrictP(P, restricted ++ locals)
  }

  def updatePIfLeft(b: Expression): State = {
    // remove free occurrences of unstable variables
    val bRestrict = b.restrict(stable)

    val PPrime = bRestrict :: this.P
    copy(P = PPrime)
  }

  def updatePIfRight(b: Expression): State = {
    // negate b
    val notB = PreOp("!", b)
    // remove free occurrences of unstable variables
    val bRestrict = notB.restrict(stable)

    val PPrime = bRestrict :: this.P
    copy(P = PPrime)
  }

  def mergeIf(state2: State): State = {
    val state1 = this

    // gamma'(x) = maximum security of gamma_1(x) and gamma_2(x))
    val gammaPrime: Map[Id, Security] = {
      for (v <- state1.gamma.keySet) yield {
        if (state1.gamma(v) == High || state2.gamma(v) == High) {
          v -> High
        } else {
          v -> Low
        }
      }
    }.toMap

    val DPrime = this.mergeD(state2)

    // P1 OR P2 converted to CNF
    val PPrime = mergeP(state1.P, state2.P)
    // restrict P' to stable variables
    val PPrimeRestricted = State.restrictP(PPrime, stable)
    if (debug)
      println("restricting P to stable variables: " + PPrimeRestricted.PStr)

    copy(gamma = gammaPrime, D = DPrime, P = PPrimeRestricted)
  }

  // D' = D1 intersect D2
  def mergeD(state2: State): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    State.mergeD(this.D, state2.D)
  }

  // https://www.cs.jhu.edu/~jason/tutorials/convert-to-CNF.html
  // P1 OR P2 converted to CNF, using switching variable to keep converted formula small
  def mergeP(P1: List[Expression], P2: List[Expression]): List[Expression] = {
  /*
    for (p1 <- P1;
         p2 <- P2) yield {
      BinOp("||", p1, p2)
    }
  */
    val switch = Switch.fresh
    val p1List: List[Expression] = for (p1 <- P1) yield {
      BinOp("||", PreOp("!", switch), p1)
    }
    val p2List: List[Expression] = for (p2 <- P2) yield {
      BinOp("||", switch, p2)
    }
    p1List ++ p2List
  }


  def setMode(z: Id, mode: Mode): State = {
    mode match {
      case NoW =>
        val noWritePrime = noWrite + z
        val readWritePrime = readWrite - z
        val noReadWritePrime = readWrite - z
        val stablePrime = stable + z
        copy(noWrite = noWritePrime, noReadWrite = noReadWritePrime, readWrite = readWritePrime, stable = stablePrime)
      case RW =>
        val noWritePrime = noWrite - z
        val readWritePrime = readWrite + z
        val noReadWritePrime = readWrite - z
        val stablePrime = stable - z
        copy(noWrite = noWritePrime, noReadWrite = noReadWritePrime, readWrite = readWritePrime, stable = stablePrime)
      case NoRW =>
        val noWritePrime = noWrite - z
        val readWritePrime = readWrite - z
        val noReadWritePrime = readWrite + z
        val stablePrime = stable + z
        copy(noWrite = noWritePrime, noReadWrite = noReadWritePrime, readWrite = readWritePrime, stable = stablePrime)
      case _ =>
        this
    }
  }


}

object State {
  def init(definitions: Set[Definition], P_0: Option[List[Expression]], gamma_0: Option[List[GammaMapping]], toLog: Boolean, debug: Boolean): State = {
    var globals: Set[Id] = Set()
    var locals: Set[Id] = Set()
    var noReadWrite: Set[Id] = Set()
    var readWrite: Set[Id] = Set()
    var noWrite: Set[Id] = Set()
    var controls: Set[Id] = Set()
    var controlled: Set[Id] = Set()
    var controlledBy: Map[Id, Set[Id]] = Map()

    val arrays: Map[Id, IdArray] = (definitions collect {case a: ArrayDef => a.name -> IdArray(a.name, a.size)}).toMap
    val arrayIndices: Set[Id] = definitions collect {case a: ArrayDef => a.name}
    val variables: Set[VarDef] = definitions flatMap {
      case a: ArrayDef => a.toVarDefs
      case v: VarDef => Seq(v)
    }
    if (debug) {
      println(variables)
    }

    val ids: Set[Id] = for (v <- variables)
      yield v.name

    for (v <- variables) {
      v.mode match {
        case Reg =>
          locals += v.name
          noReadWrite += v.name
        case NoRW =>
          globals += v.name
          noReadWrite += v.name
        case NoW =>
          globals += v.name
          noWrite += v.name
        case RW =>
          globals += v.name
          readWrite += v.name
      }

      val controllingArrays: Set[Id] = {
        for (i <- v.pred.arrays) yield {
          i.index match {
            case Lit(n) =>
              Set(arrays(i.name).array(n))
            case _ =>
              arrays(i.name).array.toSet
          }
        }
        }.flatten
      val controlling: Set[Id] = v.pred.variables ++ controllingArrays

      if (controlling.nonEmpty) {
        controlled += v.name
      }
      for (i <- controlling) {
        if (controlledBy.contains(i))
          controlledBy += (i -> (controlledBy(i) + v.name))
        else
          controlledBy += (i -> Set(v.name))
        controls += i
      }
    }

    val controlAndControlled = controls & controlled
    if (controlAndControlled.nonEmpty) {
      throw error.InvalidProgram("the following variables are both control and controlled variables: " + controlAndControlled.mkString(", "))
    }

    // init D - every variable maps to Var
    val D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
      for (i <- ids)
        yield i -> (ids, ids, ids, ids)
    }.toMap

    val stable = noReadWrite ++ noWrite

    if (debug) {
      println("variables: " + ids)
      println("array indices: " + arrayIndices)
      println("arrays: " + arrays.keySet)
      println("globals: " + globals)
      println("locals: " + locals)
      println("no read write: " + noReadWrite)
      println("read write: " + readWrite)
      println("no write: " + noWrite)
      println("stable: " + stable)
      println("controls: " + controls)
      println("controlled: " + controlled)
      println("controlled by: " + controlledBy)
    }

    val gammaDom: Set[Id] = ids collect {case v if !controls.contains(v) && stable.contains(v) => v}

    // init gamma
    val gamma: Map[Id, Security] = gamma_0 match {
      // security high by default if user hasn't provided
      case None => {
        for (i <- gammaDom) yield {
          i -> High
        }
        }.toMap
      // user provided
      case Some(gs) => {
        gs flatMap {g => g.toPair(arrays)}
        }.toMap
    }

    // check gamma domain
    if (gamma.keySet != gammaDom)
      throw error.InvalidProgram("provided gamma has invalid domain (" + gamma.keySet.mkString(", ") + "), correct domain is " + gammaDom.mkString(", "))

    // for replacing Ids in predicates with Vars
    val idToVar: Subst = {
      for (v <- ids)
        yield v -> v.toVar
      }.toMap ++ {
      for (v <- arrays.keySet)
        yield v -> v.toVar
      }.toMap

    // initialise P - true by default
    val P: List[Expression] = P_0 match {
      case None =>
        List(Const._true)

      case Some(p) =>
        // check no unstable variables in user-defined P_0
        // P_0 only contains stable variables - tested
        val PArrayAccess: Set[Id] = {p flatMap {x: Expression => x.arrays flatMap {y: Access => y.index match {
          case Lit(n) =>
            Set(arrays(y.name).array(n))
          case _ =>
            arrays(y.name).array.toSet
        }}}}.toSet

        val PVars: Set[Id] = (p flatMap {x => x.variables}).toSet ++ PArrayAccess
        if (debug) {
          println("variables in P_0: " + PVars.mkString(" "))
        }
        val unstableP = for (i <- PVars if !stable.contains(i))
          yield i
        if (unstableP.nonEmpty) {
          throw error.InvalidProgram("unstable variables in P_0: " + unstableP.mkString(", "))
        }

        p map {i => i.subst(idToVar)}
    }

    // init L - map variables to their L predicates
    val L: Map[Id, Expression] = {
      for (v <- variables) yield {
        val predVar = v.pred.subst(idToVar)
        v.name -> predVar
      }
    }.toMap
    if (debug) {
      println("L: " + L)
    }
    if (toLog) {
      println("gamma: " + gamma.gammaStr)
      println("P: " + P.PStr)
      println("D: " + D.DStr)
    }


    State(
      gamma = gamma,
      D = D,
      P = P,
      L = L,
      globals = globals,
      locals = locals,
      noReadWrite = noReadWrite,
      readWrite = readWrite,
      noWrite = noWrite,
      stable = stable,
      controls = controls,
      controlled = controlled,
      controlledBy = controlledBy,
      variables = ids,
      read = Set(),
      written = Set(),
      nonblocking = false,
      nonblockingDepth = 0,
      arrayIndices = arrayIndices,
      arrays = arrays,
      toLog = toLog,
      debug = debug
    )
  }

  // calculate P|_known_W(a) etc. with known_W(a) being the input set in that example
  def restrictP(P: List[Expression], restricted: Set[Id]): List[Expression] = {
    P map (p => p.restrict(restricted))
  }

  def mergeD(D1: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])], D2: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])]): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    for (v <- D1.keySet) yield {
      v -> ((D1(v)._1 intersect D2(v)._1,
        D1(v)._2 intersect D2(v)._2,
        D1(v)._3 intersect D2(v)._3,
        D1(v)._4 intersect D2(v)._4))
    }
    }.toMap

}