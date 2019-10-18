package tool

case class State(
  gamma: Map[Id, Boolean],
  D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])], // W_w, W_r, R_w, R_r
  P: List[Expression],

  L: Map[Id, Expression],

  globals: Set[Id],
  locals: Set[Id],

  noReadWrite: Set[Id],
  readWrite: Set[Id],
  noWrite: Set[Id],

  controls: Set[Id],
  controlled: Set[Id],
  controlledBy: Map[Id, Set[Id]], // CLed(name)

  variables: Set[Id],


  read: Set[Id],
  written: Set[Id]) {

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
    val PPrime = BinOp("=", v, argReplace) :: P

    // restrict PPrime to stable variables
    val stable = noWrite ++ noReadWrite
    val PPrimeRestrict = State.restrictP(PPrime, stable)

    copy(P = PPrimeRestrict)
  }

  /**
   * Introduce an uninitialised variable
   */
    /*
  def define(id: Id): State = {
    copy(stack = stack + (id -> Lit("uninitialised")))
  }
     */

  /**
   * Introduce a variable with an initializer.
   */
  def define(id: Id, _init: Expression): State = {
    val st0 = this
    val st1 = st0 assign (id, _init)
    st1
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

  def knownW(): Set[Id] = {
    val a = for (v <- read) yield {
      W_w(v)
    }
    val b = for (v <- written) yield {
      W_r(v)
    }
    a.flatten ++ b.flatten
  }

  def knownR(): Set[Id] = {
    val a = for (v <- read) yield {
      R_w(v)
    }
    val b = for (v <- written) yield {
      R_r(v)
    }
    a.flatten ++ b.flatten
  }

  def updateD(laterW: Set[Id], laterR: Set[Id]): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    for (i <- variables) yield {
      if ((read ++ written).contains(i)) {
        val w_w = if (laterW.contains(i)) {
          W_w(i) ++ knownW()
        } else {
          W_w(i) -- written
        }
        val w_r = if (laterW.contains(i)) {
          W_r(i) ++ knownW()
        } else {
          W_r(i) -- written
        }
        val r_w = if (laterR.contains(i)) {
          R_w(i) ++ knownR()
        } else {
          R_w(i) -- read
        }
        val r_r = if (laterR.contains(i)) {
          R_r(i) ++ knownR()
        } else {
          R_r(i) -- read
        }
        i -> (w_w, w_r, r_w, r_r)
      } else {
        i -> D(i)
      }
    }
  }.toMap

  def updateDAssign(x: Id, e: Expression) : State = {
    val varE = e.getVariables // var(e)
    val laterW: Set[Id] = Set(x) ++ varE
    val laterR: Set[Id] = if (varE.intersect(globals).isEmpty) {
      Set(x) ++ varE.intersect(globals)
    } else {
      Set()
    }

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

  // placeholder
  def lowP(id: Id): Boolean = {
    // prove if L(x) holds given P
    SMT.prove(L(id), P)

    true
  }

  def highP(id: Id): Boolean = {
    // prove if L(x) doesn't hold given P
    SMT.prove(PreOp("!", L(id)), P)

    true
  }

  // e is expression to get security of, p is P value given so can substitute in P_a etc. - not sure if this is the best way to do this
  def security(e: Expression, p: List[Expression]): Boolean = {
    var low = true
    val it = variables.toIterator
    // if x security is high, return, otherwise keep checking
    while (it.hasNext && low) {
      val x: Id = it.next()
      low = if (gamma.contains(x)) {
        gamma(x)
      } else {
        lowP(x) // true/LOW if L(x) holds given P, false/HIGH otherwise
      }
    }
    low
  }

  def updateGammaAssign(x: Id, e: Expression): State = {
    val t = security(e, P)
    val gammaPrime = gamma + (x -> t)
    copy(gamma = gammaPrime)
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
    val gammaPrime: Map[Id, Boolean] = {
      for (v <- state1.variables) yield {
        v -> (state1.gamma(v) && state2.gamma(v))
      }
    }.toMap

    // D' = D1 intersect D2
    val DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
      for (v <- state1.variables) yield {
        v -> ((state1.W_w(v) intersect state2.W_w(v),
          state1.W_r(v) intersect state2.W_r(v),
          state1.R_w(v) intersect state2.R_w(v),
          state1.R_r(v) intersect state2.R_r(v)))
      }
    }.toMap

    // P1 OR P2 converted to CNF
    val PPrime = mergeP(state1.P, state2.P)
    // restrict P' to stable variables
    val PPrimeRestricted = State.restrictP(PPrime, noReadWrite ++ noWrite)

    copy(gamma = gammaPrime, D = DPrime, P = PPrimeRestricted)
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
  def init(variables: Set[Variable]): State = {
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
          throw error.InvalidControlVariables(v.name + " is both controlled and a control variable")
        }
        controlled += v.name
      }

      // need to create empty sets for variables that don't control anything
      for (i <- controlling) {
        if (controlledBy.contains(i))
          controlledBy += (i -> (controlledBy(i) + v.name))
        else
          controlledBy += (i -> Set(v.name))
        controls += i
      }
    }
    println("globals")
    println(globals)
    println("locals")
    println(locals)
    println("no read write")
    println(noReadWrite)
    println("read write")
    println(readWrite)
    println("no write")
    println(noWrite)
    println("controls")
    println(controls)
    println("controlled")
    println(controlled)

    for (v <- variables) {
      println("controlled by " + v)
      //println(controlledBy(v.name))
    }

    // init D - every variable maps to Var
    val D: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
      for (i <- ids)
        yield i -> (ids, ids, ids, ids)
    }.toMap

    println(D)

    // init gamma - all variables uninitialised initially so set security to be high
    // will need to change this later to handle pre-defining variables etc
    val gamma: Map[Id, Boolean] = {
      // dom gamma = stable variables without control variables
      for (i <- ids if !controls.contains(i) && (noReadWrite.contains(i) || noWrite.contains(i))) yield {
        i-> false
      }
    }.toMap

    // init L - map variables to their L predicates
    val L: Map[Id, Expression] = {
      for (v <- variables)
        yield v.name -> v.pred
    }.toMap

    println(gamma)

    State(
      gamma = gamma,
      D = D,
      P = List(Lit("True")),
      L = L,
      globals = globals,
      locals = locals,
      noReadWrite = noReadWrite,
      readWrite = readWrite,
      noWrite = noWrite,
      controls = controls,
      controlled = controlled,
      controlledBy = controlledBy,
      variables = ids,
      read = Set(),
      written = Set()
    )
  }

  // calculate P|_known_W(a) etc. with known_W(a) being the input set in that example
  def restrictP(P: List[Expression], restricted: Set[Id]): List[Expression] = {
    P map (p => p.restrict(restricted))
  }

}