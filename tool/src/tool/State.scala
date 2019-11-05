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

  errors: List[String]) {

  def log = {
    println("gamma: " + gamma.gammaStr)
    println("P: " + P.PStr)
    println("D: " + D.DStr)
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

    copy(P = PPrimeRestrict)
  }

  def W_w(v: Id): Set[Id] = D(v)._1
  def W_r(v: Id): Set[Id] = D(v)._2
  def R_w(v: Id): Set[Id] = D(v)._3
  def R_r(v: Id): Set[Id] = D(v)._4

  def resetReadWrite(): State = {
    copy(read = Set(), written = Set())
  }

  def updateRead(id: Id): State = {
    copy(read = read + id)
  }

  def updateWritten(id: Id): State = {
    copy(written = written + id)
  }

  def knownW: Set[Id] = {
    val w = for (v <- written) yield {
      W_w(v)
    }
    val r = for (v <- read) yield {
      W_r(v)
    }
    w.flatten ++ r.flatten
  }

  def knownR: Set[Id] = {
    val r = for (v <- read) yield {
      R_r(v)
    }
    val w = for (v <- written) yield {
      R_w(v)
    }
    r.flatten ++ w.flatten
  }

  def updateD(laterW: Set[Id], laterR: Set[Id]): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    for (i <- variables) yield {
      val w_w = if (laterW.contains(i)) {
        W_w(i) ++ knownW
      } else {
        W_w(i) -- written
      }
      val w_r = if (laterR.contains(i)) {
        W_r(i) ++ knownW
      } else {
        W_r(i) -- written
      }
      val r_w = if (laterW.contains(i)) {
        R_w(i) ++ knownR
      } else {
        R_w(i) -- read
      }
      val r_r = if (laterR.contains(i)) {
        R_r(i) ++ knownR
      } else {
        R_r(i) -- read
      }
      i -> (w_w, w_r, r_w, r_r)
    }
  }.toMap

  def updateDAssign(x: Id, e: Expression) : State = {
    val varE = e.getVariables // var(e)
    val laterW: Set[Id] = Set(x) ++ varE
    val laterR: Set[Id] = if (varE.intersect(globals).nonEmpty) {
      Set(x) ++ varE.intersect(globals)
    } else {
      Set()
    }
    println("laterW: " + laterW)
    println("laterR: " + laterR)
    println("rd: " + read)
    println("wr: " + written)
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = updateD(laterW, laterR)

    copy(D = DPrime)
  }

  def updateDGuard(b: Expression) : State = {
    val varB = b.getVariables // var(b)
    val laterW: Set[Id] = globals ++ varB
    val laterR: Set[Id] = globals & varB

    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = updateD(laterW, laterR)

    copy(D = DPrime)
  }

  def updateDFence(): State = {
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
      for (v <- variables)
        yield v -> (variables, variables, variables, variables)
    }.toMap

    copy(D = DPrime)
  }

  def lowP(id: Id, p: List[Expression]): Boolean = {
    println("checking lowP for " + id)
    // prove if L(x) holds given P
    SMT.prove(L(id), p)
  }

  def highP(id: Id, p: List[Expression]): Boolean = {
    println("checking highP for " + id)
    // prove if L(x) doesn't hold given P
    SMT.prove(PreOp("!", L(id)), p)
  }

  // x is variable to get security of, p is P value given so can substitute in P_a etc.
  def security(x: Id, p: List[Expression]): Security = {
    println("checking security for " + x)
    var sec: Security = High
    if (gamma.contains(x)) {
      sec = gamma(x)
    } else {
      if (lowP(x, p)) {
        sec = Low
      } // true/LOW if L(x) holds given P, false/HIGH otherwise
    }
    if (sec == Low) {
      println(x + " security is low")
    } else {
      println(x + " security is high")
    }
    sec
  }

  // e is expression to get security of, p is P value given so can substitute in P_a etc.
  def security(e: Expression, p: List[Expression]): Security = {
    println("checking security for " + e)
    var sec: Security = Low
    val it = e.getVariables.toIterator
    // if x security is high, return, otherwise keep checking
    while (it.hasNext && sec == Low) {
      val x: Id = it.next()
      sec = security(x, p)
    }
    if (sec == Low) {
      println(e + "security is low")
    } else {
      println(e + "security is high")
    }
    sec
  }

  def updateGammaAssign(x: Id, e: Expression): State = {
    if (gamma.contains(x)) {
      val t = security(e, P)
      val gammaPrime = gamma + (x -> t)
      copy(gamma = gammaPrime)
    } else {
      this
    }
  }

  def restrictP(restricted: Set[Id]): List[Expression] = {
    State.restrictP(P, restricted)
  }

  def updatePIfLeft(b: Expression): State = {
    // remove free occurrences of unstable variables
    val bRestrict = b.restrict(noReadWrite ++ noWrite)

    val PPrime = bRestrict :: this.P
    copy(P = PPrime)
  }

  def updatePIfRight(b: Expression): State = {
    // negate B
    val notB = PreOp("!", b)
    // remove free occurrences of unstable variables
    val bRestrict = notB.restrict(noReadWrite ++ noWrite)

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

    copy(gamma = gammaPrime, D = DPrime, P = PPrimeRestricted)
  }

  // D' = D1 intersect D2
  def mergeD(state2: State): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    State.mergeD(this.D, state2.D)
  }

  // P1 OR P2 converted to CNF
  // assumes P1 and P2 are already in CNF - may need to add further conversion later to distribute nots etc.?
  // also consider using switching variables to keep the converted formula small
  def mergeP(P1: List[Expression], P2: List[Expression]): List[Expression] = {
    for (p1 <- P1;
         p2 <- P2) yield {
      BinOp("||", p1, p2)
    }
  }

}

object State {
  def init(variables: Set[VarDef], P_0: Option[List[Expression]], gamma_0: Option[List[Expression]]): State = {
    var globals: Set[Id] = Set()
    var locals: Set[Id] = Set()
    var noReadWrite: Set[Id] = Set()
    var readWrite: Set[Id] = Set()
    var noWrite: Set[Id] = Set()
    var controls: Set[Id] = Set()
    var controlled: Set[Id] = Set()
    var controlledBy: Map[Id, Set[Id]] = Map()

    val ids: Set[Id] = for (v <- variables)
      yield v.name

    for (v <- variables) {
      v.mode.mode match {
        case "Reg" =>
          locals += v.name
          noReadWrite += v.name
        case "NoRW" =>
          globals += v.name
          noReadWrite += v.name
        case "NoW" =>
          globals += v.name
          noWrite += v.name
        case "RW" =>
          globals += v.name
          readWrite += v.name
      }
      val controlling: Set[Id] = v.pred.getVariables
      if (controlling.nonEmpty) {
        if (controls.contains(v.name)) {
          throw error.InvalidProgram(v.name + " is both controlled and a control variable")
        }
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

    // init D - every variable maps to Var
    val D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
      for (i <- ids)
        yield i -> (ids, ids, ids, ids)
    }.toMap

    val stable = noReadWrite ++ noWrite

    // init gamma
    val gamma: Map[Id, Security] = gamma_0 match {
      // security high by default if user hasn't provided
      case None => {
        // dom gamma = stable variables without control variables
        for (i <- ids if !controls.contains(i) && stable.contains(i)) yield {
          i -> High
        }
        }.toMap
      // user provided
      case Some(gs) => {
        for (g <- gs) yield {
          g match {
            case BinOp("==", arg1: Id, Const.low) =>
              arg1 -> Low
            case BinOp("==", arg1: Id, Const.high) =>
              arg1 -> High
            case _ =>
              throw error.InvalidProgram(g + " is not a valid input to gamma")
          }
        }
        }.toMap
    }

    // check gamma domain
    val gammaDom: Set[Id] = for (i <- ids if !controls.contains(i) && stable.contains(i)) yield i
    if (gamma.keySet != gammaDom)
      throw error.InvalidProgram("provided gamma has invalid domain")

    // for replacing Ids in predicates with Vars
    val idToVar: Subst = {
      for (i <- ids)
        yield i -> i.toVar
      }.toMap


    // initialise P - true by default
    val P: List[Expression] = P_0 match {
      case None =>
        List(Const._true)

      case Some(p) =>
        p map {i => i.subst(idToVar)}
    }


    // init L - map variables to their L predicates
    val L: Map[Id, Expression] = {
      for (v <- variables) yield {
        val predVar = v.pred.subst(idToVar)
        v.name -> predVar
      }
    }.toMap

    println("globals: " + globals)
    println("locals: " + locals)
    println("no read write: " + noReadWrite)
    println("read write: " + readWrite)
    println("no write: " + noWrite)
    println("stable: " + stable)
    println("controls: " + controls)
    println("controlled: " + controlled)
    println("controlled by: " + controlledBy)
    println("D: " + D.DStr)
    println("P: " + P.PStr)
    println("L: " + L)
    println("gamma: " + gamma.gammaStr)

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
      errors = List(),
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