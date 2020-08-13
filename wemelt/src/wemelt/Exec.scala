package wemelt

sealed trait Cont {
  def st: State
}

object Cont {
  case class next(st: State) extends Cont
}

object Exec {
  def execute(statements: List[Statement], state: State): Cont = statements match {
    case Nil =>
      Cont.next(state)
    case stmt :: rest =>
      val st = execute(stmt, state).st
      execute(rest, st)
  }

  def execute(statement: Statement, state0: State): Cont = statement match {
    case Malformed =>
      throw error.InvalidProgram("parser")

    case block: Block =>
      // blocks currently leak local definitions but this isn't important for this application
      execute(block.statements, state0)

    case Assignment(lhs, rhs) =>

      if (state0.toLog)
        println("line " + statement.line + ": " + lhs + " = " + rhs + ":")
      //check if lhs is a local variable
      val state1 = if (state0.locals.contains(lhs)) {
        assignLRule(lhs, rhs, state0, statement.line)
      } else {
        assignGRule(lhs, rhs, state0, statement.line)
      }
      state1.log
      Cont.next(state1)


      /*
    case ArrayAssignment(array, index, rhs) =>
      if (state0.toLog)
        println("line " + statement.line + ": " + array + "[" + index + "] = " + rhs + ":")
      // check if array contains any control variables
      val state1 = if (state0.controls.intersect(state0.arrays(array).array.toSet).nonEmpty) {
         arrayAssignCRule(array, index, rhs, state0, statement.line)
      } else {
        arrayAssignRule(array, index, rhs, state0, statement.line)
      }
      // check nonblocking rule if necessary
      if (state1.nonblocking && state1.globals.contains(array)) {
        throw error.NonblockingError(statement.line, statement, "global variable " + array + " was written to within a nonblocking while loop")
      }
      state1.log
      Cont.next(state1)

    case CompareAndSwap(r3, x, r1, r2) =>
      if (state0.toLog)
        println("line " + statement.line + ": " + statement)
      val state1 = if (state0.controls.contains(x)) {
        compareAndSwapCRule(r3, x, r1, r2, state0, statement.line)
      } else {
        compareAndSwapRule(r3, x, r1, r2, state0, statement.line)
      }

      // check nonblocking rule if necessary
      if (state1.nonblocking && state1.globals.contains(r3)) {
        throw error.NonblockingError(statement.line, statement, "global variable " + r3 + " was written to within a nonblocking while loop")
      }
      // check nonblocking rule if necessary
      if (state1.nonblocking && state1.globals.contains(x)) {
        throw error.NonblockingError(statement.line, statement, "global variable " + x + " was written to within a nonblocking while loop")
      }
      state1.log
      Cont.next(state1)
*/


    case Fence =>
      // reset D
      val state1 = state0.updateDFence
      if (state0.toLog) {
        println("fence:")
        state1.log
      }
      Cont.next(state1)

    case ControlFence =>
      // reset D
      val state1 = state0.updateWritten(CFence)
      val state2 = state1.updateDCFence
      if (state0.toLog) {
        println("cfence:")
        state1.log
      }
      Cont.next(state2)


    case If(test, left, right) =>
      if (state0.toLog)
        println("line " + statement.line + ": If(" + test + ") {")
      val state1 = ifRule(test, left, right, state0, statement.line)
      if (state0.toLog)
        println("end of line " + statement.line + ": If(" + test + ")")
      state1.log
      if (state0.toLog)
        println("}")
      Cont.next(state1)

    case While(test, invariants, gamma, body) =>
      if (state0.toLog)
        println("line " + statement.line + ": While(" + test + ") {")
      // replace Ids in invariant with vars

      val primeMap: Map[Id, Var] = {
        {for (v <- state0.variables)
          yield v.prime -> v.toVar.fresh} ++
        {for (v <- state0.variables)
          yield v.prime.prime -> v.toVar.fresh} ++
        {for (v <- state0.variables)
          yield v.prime.prime.prime -> v.toVar.fresh} ++
        {for (v <- state0.variables)
          yield v.prime.prime.prime.prime -> v.toVar.fresh}
      }.toMap

      val idToVar: Subst = ({
        for (v <- state0.variables)
          yield v -> v.toVar
      } ++ primeMap).toMap/* ++ {
        for (v <- state0.arrays.keySet)
          yield v -> v.toVar
      }.toMap */

      // existentially quantify any prime variables
      val PPrime = Predicate(invariants map {i => i.subst(idToVar)}, (invariants flatMap { p => p.variables } collect {case i if i.name.endsWith("'") => primeMap(i)}).toSet, Set())

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Predicate] = (gamma map {g => g.variable -> Predicate(List(g.security.subst(idToVar)), g.security.variables collect {case i if i.name.endsWith("'") => primeMap(i)}, Set())}).toMap
      //val gammaPrime: Map[Id, Security] = (gamma flatMap {g => g.toPair(state0.arrays)}).toMap

      val state1 = whileRule(test, PPrime, gammaPrime, body, state0, statement.line)
      if (state0.toLog)
        println("end of line " + statement.line + ": While(" + test + ")")
      state1.log
      if (state0.toLog)
        println("}")
      Cont.next(state1)

    case DoWhile(test, invariants, gamma, body) =>
      if (state0.toLog)
        println("line " + statement.line + ": While(" + test + ") {")
      // replace Ids in invariant with vars
      val primeMap: Map[Id, Var] = {
        {for (v <- state0.variables)
          yield v.prime -> v.toVar.fresh} ++
          {for (v <- state0.variables)
            yield v.prime.prime -> v.toVar.fresh} ++
          {for (v <- state0.variables)
            yield v.prime.prime.prime -> v.toVar.fresh} ++
          {for (v <- state0.variables)
            yield v.prime.prime.prime.prime -> v.toVar.fresh}
      }.toMap

      val idToVar: Subst = ({
        for (v <- state0.variables)
          yield v -> v.toVar
      } ++ primeMap).toMap/* ++ {
        for (v <- state0.arrays.keySet)
          yield v -> v.toVar
      }.toMap */

      // existentially quantify any prime variables
      val PPrime = Predicate(invariants map {i => i.subst(idToVar)}, (invariants flatMap { p => p.variables } collect {case i if i.name.endsWith("'") => primeMap(i)}).toSet, Set())

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Predicate] = (gamma map {g => g.variable -> Predicate(List(g.security.subst(idToVar)), g.security.variables collect {case i if i.name.endsWith("'") => primeMap(i)}, Set())}).toMap
      //val gammaPrime: Map[Id, Security] = (gamma flatMap {g => g.toPair(state0.arrays)}).toMap

      // execute loop body once at start
      val state1 = execute(body, state0).st

      val state2 = whileRule(test, PPrime, gammaPrime, body, state1, statement.line)
      if (state0.toLog)
        println("end of line " + statement.line + ": While(" + test + ")")
      state2.log
      if (state0.toLog)
        println("}")
      Cont.next(state2)

    case _ =>
      throw error.InvalidProgram("unimplemented statement " + statement + " at line " + statement.line)

  }

  // compute fixed point of D
  def DFixedPoint(guard: Expression, body: Statement, state: State, invariant: Predicate): DType = {
    var DFixed = false
    var st0 = state.copy(P = invariant)
    var DPrime: DType = Map()
    var dfixedloops = 0
    if (st0.debug)
      println("DFixed0: " + st0.D.DStr)
    while (!DFixed) {
      dfixedloops = dfixedloops + 1
      // update rd for the guard
      val (_guard, st1) = eval(guard, st0)
      val st2 = st1.calculateIndirectUsed
      val st3 = st2.updateDGuard(_guard)
      val st4 = DFixedPoint(body, st3)
      // intersect with original D after loop body
      val st5 = st3.copy(D = st4.mergeD(state))

      if (st0.debug) {
        println("DFixed" + (dfixedloops - 1) + ": " + st0.D.DStr)
        println("DFixed" + dfixedloops + ": " + st5.D.DStr)
      }
      // compare st4.D to st0.D
      val it = st0.variables.toIterator
      DFixed = true
      while (it.hasNext && DFixed) {
        val v = it.next
        DFixed = (st0.W_r(v) == st5.W_r(v)) && (st0.W_w(v) == st5.W_w(v)) &&
          (st0.R_r(v) == st5.R_r(v)) && (st0.R_w(v) == st5.R_w(v)) &&
          (st0.I_r(v) == st5.I_r(v)) && (st0.I_w(v) == st5.I_w(v)) &&
          (st0.U_r(v) == st5.U_r(v)) && (st0.U_w(v) == st5.U_w(v))
      }
      // if D has changed, repeat
      if (DFixed) {
        DPrime = st5.D
      } else {
        st0 = st5.copy(P = invariant)
        DFixed = false
      }
    }
    if (st0.debug)
      println("dfixed loops " + dfixedloops)
    DPrime
  }

  def DFixedPoint(statements: List[Statement], state: State): State = statements match {
    case Nil =>
      state
    case stmt :: rest =>
      val st = DFixedPoint(stmt, state)
      DFixedPoint(rest, st)
  }

  def DFixedPoint(statement: Statement, st0: State): State = statement match {
    case Malformed =>
      throw error.InvalidProgram("parser")

    case block: Block =>
      DFixedPoint(block.statements, st0)

    case Assignment(lhs, rhs) =>
      val (_rhs, st1) = eval(rhs, st0)
      val st2 = st1.updateWritten(lhs)
      val st3 = st2.calculateIndirectUsed
      val (st4, _, _) = st3.assignUpdateP(lhs, _rhs)
      st4.updateDAssign(lhs, _rhs)

      /*
    case ArrayAssignment(name, index, rhs) =>
      val st1 = DFixedPoint(rhs, st0)
      val st2 = DFixedPoint(index, st1)
      val st3 = st2.updateWritten(st2.arrays(name))
      st3.updateDArrayAssign(name, rhs)
       */

    case Fence =>
      // reset D
      st0.updateDFence

    case ControlFence =>
      // reset D
      val st1 = st0.updateWritten(CFence)
      st1.updateDCFence

    case If(guard, left, None) =>
      // evaluate test which updates D
      val (_guard, st1) = eval(guard, st0)
      val st2 = st1.calculateIndirectUsed
      val (st3, _, _) = st2.guardUpdateP(_guard)
      val st4 = st3.updateDGuard(_guard)

      // right branch is empty
      val _left = DFixedPoint(left, st4)
      st4.copy(D = _left.mergeD(st4), P = _left.P.merge(st4.P))

    case If(guard, left, Some(right)) =>
      // evaluate test which updates D
      val (_guard, st1) = eval(guard, st0)
      val st2 = st1.calculateIndirectUsed
      val (st3, _, _) = st2.guardUpdateP(_guard)
      val st4 = st3.updateDGuard(_guard)

      val _left = DFixedPoint(left, st4)
      val _right = DFixedPoint(right, st4)
      st4.copy(D =_left.mergeD(_right), P = _left.P.merge(_right.P))

    case While(test, invariants, _, body) =>
      val primeMap: Map[Id, Var] = {
        {for (v <- st0.variables)
          yield v.prime -> v.toVar.fresh} ++
          {for (v <- st0.variables)
            yield v.prime.prime -> v.toVar.fresh} ++
          {for (v <- st0.variables)
            yield v.prime.prime.prime -> v.toVar.fresh} ++
          {for (v <- st0.variables)
            yield v.prime.prime.prime.prime -> v.toVar.fresh}
      }.toMap
      val idToVar: Subst = ({
        for (v <- st0.variables)
          yield v -> v.toVar
      } ++ primeMap).toMap
      val PPrime = Predicate(invariants map {i => i.subst(idToVar)}, (invariants flatMap { p => p.variables } collect {case i if i.name.endsWith("'") => primeMap(i)}).toSet, Set())
      st0.copy(D = DFixedPoint(test, body, st0, PPrime), P = PPrime)

    case DoWhile(test, invariants, _, body) =>
      val st1 = DFixedPoint(body, st0)
      val primeMap: Map[Id, Var] = {
        {for (v <- st0.variables)
          yield v.prime -> v.toVar.fresh} ++
          {for (v <- st0.variables)
            yield v.prime.prime -> v.toVar.fresh} ++
          {for (v <- st0.variables)
            yield v.prime.prime.prime -> v.toVar.fresh} ++
          {for (v <- st0.variables)
            yield v.prime.prime.prime.prime -> v.toVar.fresh}
      }.toMap
      val idToVar: Subst = ({
        for (v <- st0.variables)
          yield v -> v.toVar
      } ++ primeMap).toMap
      val PPrime = Predicate(invariants map {i => i.subst(idToVar)}, (invariants flatMap { p => p.variables } collect {case i if i.name.endsWith("'") => primeMap(i)}).toSet, Set())
      st1.copy(D = DFixedPoint(test, body, st0, PPrime), P = PPrime)

      /*
    case CompareAndSwap(r3, x, r1, r2) =>
      val st1 = DFixedPoint(r1, st0)
      val st2 = DFixedPoint(r2, st1)
      val st3 = st2.updateRead(x)
      val st4 = st3.updateWritten(x)
      val st5 = st4.updateWritten(r3)
      st5.updateDCAS(r3, x, r1, r2)
       */

    case _ =>
      throw error.InvalidProgram("unimplemented statement at line " + statement.line + ": " + statement)
  }

  def eval(expr: Expression, st0: State): (Expression, State) = expr match {
    case id: Id =>
      // value has been READ
      val st1 = st0.updateRead(id)
      (id.toVar, st1)

    case res: Lit =>
      (res, st0)

    case res: Const =>
      (res, st0)

      /*
    case Access(name, index) =>
      val (_index, st1) = eval(index, st0)
      val st2 = st1.updateRead(st1.arrays(name))
      (VarAccess(name.toVar, _index), st2)
       */

    case BinOp("==", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("==", _arg1, _arg2), st1)

    case BinOp("!=", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (PreOp("!", BinOp("==", _arg1, _arg2)), st1)

    case PreOp("!", arg) =>
      val (_arg, st1) = eval(arg, st0)
      (PreOp("!", _arg), st1)

    case PreOp("+", arg) =>
      eval(arg, st0)

    case PreOp("-", arg) =>
      val (_arg, st1) = eval(arg, st0)
      (PreOp("-", _arg), st1)

    case BinOp("+", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("+", _arg1, _arg2), st1)

    case BinOp("-", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("-", _arg1, _arg2), st1)

    case BinOp("*", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("*", _arg1, _arg2), st1)

    case BinOp("/", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("/", _arg1, _arg2), st1)

    case BinOp("%", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("%", _arg1, _arg2), st1)

    case BinOp("<=", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("<=", _arg1, _arg2), st1)

    case BinOp("<", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("<", _arg1, _arg2), st1)

    case BinOp(">=", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp(">=", _arg1, _arg2), st1)

    case BinOp(">", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp(">", _arg1, _arg2), st1)

    case BinOp("||", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("||", _arg1, _arg2), st1)

    case BinOp("&&", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("&&", _arg1, _arg2), st1)

    case BinOp("|", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("|", _arg1, _arg2), st1)

    case BinOp("&", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("&", _arg1, _arg2), st1)

    case BinOp("^", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("^", _arg1, _arg2), st1)

    case BinOp(">>", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp(">>", _arg1, _arg2), st1)

    case BinOp(">>>", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp(">>>", _arg1, _arg2), st1)

    case BinOp("<<", arg1, arg2) =>
      val (List(_arg1, _arg2), st1) = evals(List(arg1, arg2), st0)
      (BinOp("<<", _arg1, _arg2), st1)

    case PreOp("~", arg) =>
      val (_arg, st1) = eval(arg, st0)
      (PreOp("~", _arg), st1)

    case _ =>
      throw error.InvalidProgram("unimplemented expression: " + expr)

  }

  def ifRule(guard: Expression, left: Statement, right: Option[Statement], state0: State, line: Int): State = {
    // IF rule
    if (state0.toLog)
      println("IF applying")

    // evaluate test
    val (_guard, state1) = eval(guard, state0)
    val state2 = state1.calculateIndirectUsed

    // check guard is LOW
    val guardGamma = state2.security(_guard)
    val PRestrictU = state2.restrictP(state2.used)
    if (guardGamma.predicates != List(Const._true) && !SMT.proveImplies(PRestrictU, guardGamma, state2.debug)) {
      throw error.IfError(line, guard, "guard expression is HIGH")
    }

    // check any array indices in test are low
    /*
    for (i <- _test.arrays) {
      if (state2.security(i.index, state2.P) == High) {
        throw error.IfError(line, test, "array index " + i.index + " is HIGH")
      }
    }
     */

    // execute both sides of if statement
    val (_left, m, exists) = state2.guardUpdateP(_guard)
    val _left1 = _left.guardUpdateGamma(m, exists)
    val _left2 = _left1.updateDGuard(_guard)
    if (state0.toLog)
      println("D[b]: " + _left2.D.DStr)
    val _left3 = if (_left2.noInfeasible) {
      // don't check infeasible paths
      if (SMT.proveP(_left2.P ++ _left2.P_inv, _left2.debug)) {
        execute(left, _left2).st
      } else {
        _left2
      }
    } else {
      execute(left, _left2).st
    }

    val notGuard = PreOp("!", _guard)
    val _right3: State = right match {
      case Some(r) =>
        if (state0.toLog)
          println("} else {")

        val (_right, m, exists) = state2.guardUpdateP(notGuard)
        val _right1 = _right.guardUpdateGamma(m, exists)
        val _right2 = _right1.updateDGuard(_guard)
        if (_right2.noInfeasible) {
          // don't check infeasible paths
          if (SMT.proveP(_right2.P ++ _right2.P_inv, _right2.debug)) {
            execute(r, _right2).st
          } else {
            _right2
          }
        } else {
          execute(r, _right2).st
        }
      case None =>
        val (state3, m, exists) = state2.guardUpdateP(notGuard)
        val state4 = state3.guardUpdateGamma(m, exists)
        state4.updateDGuard(_guard)
    }

    // merge states
    _left3.mergeIf(_right3)
  }

  def whileRule(guard: Expression, PPrime: Predicate, gammaPrime: Map[Id, Predicate], body: Statement, state0: State, line: Int): State = {
    // WHILE rule

    if (state0.toLog)
      println("WHILE applying")

    // check P' is stable
    if (state0.debug) {
      println("checking P' is stable")
    }
    if (!state0.PStable(PPrime)) {
      throw error.WhileError(line, guard, "provided P': " + PPrime + " is not stable")
    }

    // check P' is weaker than previous P
    if (state0.debug) {
      println("checking previous P ==> P'")
    }
    if (!SMT.proveImplies(state0.P, PPrime, state0.debug)) {
      throw error.WhileError(line, guard, "provided P' " + PPrime + " is not weaker than P " + state0.P)
    }

    // check gamma prime has valid domain
    if (state0.debug) {
      println("checking Gamma' has correct domain")
    }
    val gammaPrimeDom = state0.low_or_eq(PPrime)
    if (!(gammaPrime.keySet == gammaPrimeDom)) {
      throw error.WhileError(line, guard, "provided Gamma': " + gammaPrime.gammaStr + " has incorrect domain, correct domain is: " + gammaPrimeDom)
    }

    if (state0.debug) {
      println("checking Gamma' is stable")
    }
    if (!state0.gammaStable(gammaPrime, PPrime)) {
      throw error.WhileError(line, guard, "provided Gamma': " + gammaPrime.gammaStr + " is not stable")
    }

    // D' will always be a subset of D as it equals D intersect DFixed

    // calculating DFixed will always terminate, as whether variables are added or removed from D is dependent on
    // laterW and laterR, which will always be the same for each loop iteration as they are dependent on the type of
    // statement, so variables will always be added or removed from each part of D on each loop iteration, causing it
    // to terminate.

    // D' will also always be a subset of D'', as for it not to be, D' would have to contain an element that is
    // not in D''. for an element to be in D' it must be in both D and DFixed. D'' is the result of calculating D on
    // a single loop iteration starting with D'. for D' to contain an element that is not in D'', it must be in both
    // D and DFixed, but not D''. this is impossible as if an element is in D and D_fixed, it will not be removed after
    // the single loop iteration that produces D''

    val DPrime = DFixedPoint(guard, body, state0, PPrime)
    if (state0.debug)
      println("D': " + DPrime.DStr)

    val state1 = state0.copy(P = PPrime, gamma = gammaPrime, D = DPrime)

    // check D' is subset of D
    if (!state1.DSubsetOf(state0)) {
      throw error.ProgramError("line " + line + ": D' is not a subset of D." + newline + "D': " +  state1.D.DStr + newline + "D: " + state0.D.DStr)
    }

    // check gamma' is greater or equal than gamma for all variables
    if (state0.debug) {
      println("checking Gamma >= Gamma'")
    }

    val gammaGreaterCheckStart: List[Expression] = {
      for (v <- state0.variables)
        yield {
          val gammaSec = state0.security(v)
          val gammaPrimeSec = state1.security(v)
          val notGammaPrimeSec = gammaPrimeSec.copy(predicates = List(PreOp("!", State.andPredicates(gammaPrimeSec.predicates))))
          val notGammaSec = gammaSec.copy(predicates = List(PreOp("!", State.andPredicates(gammaSec.predicates))))
          val PPrimeAndNotGammaPrime = state1.P.combine(notGammaPrimeSec)
          val PAndNotGamma = state0.P.combine(notGammaSec)
          if (state0.debug) {
            println("Gamma<" + v + ">: " + gammaSec)
            println("Gamma'<" + v + ">: " + gammaPrimeSec)
          }
          BinOp("==>", PAndNotGamma.toAnd, PPrimeAndNotGammaPrime.toAnd)
        }
    }.toList
    if (!SMT.proveListAnd(gammaGreaterCheckStart, state0.debug)) {
      throw error.WhileError(line, guard, "Gamma is not greater to or equal than than Gamma' ")
    }

    // evaluate guard
    val (_guard, state2) = eval(guard, state1)
    val state3 = state2.calculateIndirectUsed

    // check any array indices in test are low
    /*
    for (i <- _test.arrays) {
      if (state2.security(i.index, state2.P) == High) {
        throw error.WhileError(line, test, "array index " + i.index + " is HIGH")
      }
    }
     */

    // check guard is LOW with regards to P', gamma'
    val guardGamma = state3.security(_guard)
    val PRestrictU = state3.restrictP(state3.used)
    if (state0.debug) {
      println("checking guard is LOW")
    }
    if (guardGamma.predicates != List(Const._true) && !SMT.proveImplies(PRestrictU, guardGamma, state3.debug)) {
      throw error.WhileError(line, guard, "guard expression is HIGH")
    }

    // update P, Gamma and D with guard
    val (state4, m4, exists4) = state3.guardUpdateP(_guard)
    val state5 = state4.guardUpdateGamma(m4, exists4)
    val state6 = state5.updateDGuard(_guard)

    if (state0.debug) {
      println("while rule after test, before loop body:")
      println("gamma':" + state6.gamma.gammaStr)
      println("P and [e]_M:" + state6.P)
    }

    // evaluate body
    val _body = execute(body, state6)
    val state7 = _body.st

    if (state0.debug) {
      println("while rule after loop body:")
      println("gamma': " + gammaPrime.gammaStr)
      println("P': " + PPrime)

      println("gamma'': " + state7.gamma.gammaStr)
      println("P'': " + state7.P)
    }

    // this shouldn't be able to happen if D' is calculated correctly
    // check D' is subset of D''

    if (!state1.DSubsetOf(state7)) {
      throw error.ProgramError("line " + line + ": D' is not a subset of D''." + newline + "D': " +  state1.D.DStr + newline + "D'': " + state7.D.DStr)
    }

    // check P'' is stronger than P' - tested
    if (state0.debug) {
      println("checking P'' ==> P'")
    }
    if (!SMT.proveImplies(state7.P, PPrime, state0.debug)) {
      throw error.WhileError(line, guard, "provided P' " + PPrime + " does not hold after loop body. P'': " + state5.P)
    }

    // check gamma' is greater or equal than gamma'' for all in gamma domain
    if (state0.debug) {
      println("checking Gamma'' >= Gamma'")
    }
    val gammaGreaterCheck: List[Expression] = {
      for (v <- state7.variables)
        yield {
          val gammaPrimeSec = state1.security(v)
          val gammaSec = state7.security(v)
          val notGammaPrimeSec = gammaPrimeSec.copy(predicates = List(PreOp("!", State.andPredicates(gammaPrimeSec.predicates))))
          val notGammaSec = gammaSec.copy(predicates = List(PreOp("!", State.andPredicates(gammaSec.predicates))))
          val PPrimeAndNotGammaPrime = state1.P.combine(notGammaPrimeSec)
          val PAndNotGamma = state7.P.combine(notGammaSec)
          if (state0.debug) {
            println("Gamma''<" + v + ">: " + gammaSec)
            println("Gamma'<" + v + ">: " + gammaPrimeSec)
          }
          BinOp("==>", PAndNotGamma.toAnd, PPrimeAndNotGammaPrime.toAnd)
        }
    }.toList
    if (!SMT.proveListAnd(gammaGreaterCheck, state7.debug)) {
      throw error.WhileError(line, guard, "Gamma'' is not greater to or equal than than Gamma' ")
    }

    // state1 used here as do not keep gamma'', P'', D'' from after loop body execution
    // remove test from P'
    val notGuard = PreOp("!", _guard)
    val (state8, m8, exists8) = state1.guardUpdateP(notGuard)
    val state9 = state8.guardUpdateGamma(m8, exists8)
    state9.updateDGuard(notGuard)
  }


  /*
  def arrayAssignRule(a: Id, index: Expression, rhs: Expression, st0: State, line: Int): State = {
    val array = st0.arrays(a)
    // ARRAY ASSIGN rule
    if (st0.toLog)
      println("ARRAY ASSIGN applying")
    val (_rhs, st1) = eval(rhs, st0) // computes rd
    val (_index, st2) = eval(index, st1)
    val st3 = st2.updateWritten(st2.arrays(a)) // computes wr
    // at this point the rd and wr sets are complete for the current line

    val knownw = st3.knownW
    // calculate P_x:=e
    val PRestrict = st3.restrictP(knownw)
    if (st0.debug) {
      println("knownW: " + knownw)
      println("PRestrict: " + PRestrict.PStr)
    }

    // check lhs array index is low
    if (st3.security(_index, PRestrict) == High) {
      throw error.ArrayError(line, a, index, rhs, "array index to be written to is HIGH")
    }

    // check all array indices in rhs are low
    for (i <- _rhs.arrays) {
      if (st3.security(i.index, PRestrict) == High) {
        throw error.ArrayError(line, a, index, rhs, "array index " + i.index + " is HIGH")
      }
    }

    // prove array access is inbounds
    // index >= 0 && index < array size
    if (!SMT.prove(BinOp("&&", BinOp(">=", _index, Lit(0)), BinOp("<", _index, Lit(array.array.size))), PRestrict, st3.debug))
      throw error.ArrayError(line, a, index, rhs, "array access not provably in bounds")

    // possible indices that the index expression could evaluate to
    val possibleIndices: Seq[Int] = index match {
      case Lit(value) =>
        Seq(value)
      case _ =>
        for (i <- array.array.indices if SMT.proveSat(BinOp("==", _index, Lit(i)), PRestrict, st3.debug))
          yield i
    }

    if (st0.debug)
      println("possible indices: " + possibleIndices.mkString(" "))

    val t = st3.security(_rhs, PRestrict)

    // if x's mode is not NoRW, ensure that e's security level is not higher than x's security level, given P_x:=e - tested
    if (!st3.noReadWrite.contains(a) && t == High) { // optimisation to reduce smt calls
      // check if any possible array value accessed is provably High
      val arraySec: Security = if (st2.multiHighP(array, possibleIndices, PRestrict)) {
        High
      } else {
        Low
      }
      if (t > arraySec) {
        throw error.ArrayError(line, a, index, rhs, "HIGH expression assigned to LOW variable")
      }
    }
    val st4 = st3.updateGammaArray(array, possibleIndices, t)

    val st5 = st4.arrayAssign(a, index, _rhs, possibleIndices) // update P
    st5.updateDArrayAssign(a, _rhs)
  }

  def arrayAssignCRule(a: Id, index: Expression, rhs: Expression, st0: State, line: Int): State = {
    val array = st0.arrays(a)
    // ARRAY ASSIGNC rule
    if (st0.toLog)
      println("ARRAY ASSIGNC applying")
    val (_rhs, st1) = eval(rhs, st0) // computes rd
    val (_index, st2) = eval(index, st1)
    val st3 = st2.updateWritten(st2.arrays(a)) // computes wr
    // at this point the rd and wr sets are complete for the current line

    val knownw = st3.knownW
    // calculate P_x:=e
    val PRestrict = st3.restrictP(knownw)
    if (st0.debug) {
      println("knownW: " + knownw)
      println("PRestrict: " + PRestrict.PStr)
    }

    // check array index is low
    if (st3.security(_index, PRestrict) == High) {
      throw error.ArrayCError(line, a, index, rhs, "array index to be written to is high")
    }

    // check all array indices on rhs are low
    for (i <- _rhs.arrays) {
      if (st3.security(i.index, PRestrict) == High) {
        throw error.ArrayCError(line, a, index, rhs, "array index " + i.index + " is high")
      }
    }

    // prove array access is inbounds
    // index >= 0 && index < array size
    if (!SMT.prove(BinOp("&&", BinOp(">=", _index, Lit(0)), BinOp("<", _index, Lit(array.array.size))), PRestrict, st3.debug))
      throw error.ArrayCError(line, a, index, rhs, "array access not provably in bounds")

    // possible indices that the index expression could evaluate to
    val possibleIndices: Seq[Int] = index match {
      case Lit(value) =>
        Seq(value)
      case _ =>
        for (i <- array.array.indices if SMT.proveSat(BinOp("==", _index, Lit(i)), PRestrict, st3.debug))
          yield i
    }

    if (st0.debug)
      println("possible indices: " + possibleIndices.mkString(" "))

    // check _rhs is LOW
    val t = st3.security(_rhs, PRestrict)
    if (t == High) {
      throw error.ArrayCError(line, a, index, rhs, "HIGH expression assigned to control variable")
    }


    val knownR = st3.knownR
    // secure_update
    for (i <- possibleIndices) {
      val PPrime = st3.arrayAssign(a, Lit(i), _rhs, Seq(i)) // calculate PPrime
      val PPrimeRestrict = PPrime.restrictP(knownw)

      val falling = for (i <- st3.controlledBy(array.array(i)) if (!st3.lowP(i, PRestrict)) && !st3.highP(i, PPrimeRestrict))
        yield i

      if (st0.debug) {
        println("falling: " + falling)
        println("knownW: " + knownw)
      }


      //val fallingFail = for (y <- falling -- st3.noReadWrite if !knownw.contains(y) || st3.security(y, PRestrict) == High)

      // falling can only succeed if y is in gamma and maps to low
      val fallingFail = for (y <- falling -- st3.noReadWrite if !st3.gamma.contains(y) || st3.gamma(y) != Low)
        yield y

      if (fallingFail.nonEmpty) {
        throw error.ArrayCError(line, a, index, rhs, "secure update fails for falling variable/s: " + fallingFail.mkString(" "))
      }

      val rising = for (i <- st3.controlledBy(array.array(i)) if (!st3.highP(i, PRestrict)) && !st3.lowP(i, PPrimeRestrict))
        yield i

      if (st0.debug) {
        println("rising: " + rising)
      }
      val risingFail = for (y <- rising if !knownR.contains(y))
        yield y

      if (risingFail.nonEmpty) {
        throw error.ArrayCError(line, a, index, rhs, "secure update fails for rising variable/s: " + risingFail.mkString(" "))
      }
    }

    val st4 = st3.arrayAssign(a, index, _rhs, possibleIndices) // update P
    st4.updateDArrayAssign(a, _rhs)
  }
   */

  def assignLRule(lhs: Id, rhs: Expression, st0: State, line: Int): State = {
    // ASSIGNL rule
    if (st0.toLog)
      println("ASSIGNL applying")

    val (_rhs, st1) = eval(rhs, st0)
    val st2 = st1.updateWritten(lhs)
    val st3 = st2.calculateIndirectUsed
    val t = st3.security(_rhs)

    val (st4, m, exists) = st3.assignUpdateP(lhs, _rhs)
    val st5 = st4.assignUpdateGamma(lhs, t, m, exists)
    st5.updateDAssign(lhs, _rhs)
  }

  def assignGRule(lhs: Id, rhs: Expression, st0: State, line: Int): State = {
    // ASSIGNG rule
    if (st0.toLog)
      println("ASSIGNG applying")

    val (_rhs, st1) = eval(rhs, st0)
    val st2 = st1.updateWritten(lhs)
    val st3 = st2.calculateIndirectUsed
    val t = st3.security(_rhs)

    val PRestrictU = st3.restrictP(st3.used)

    // check guar P(x := e)
    val guarUnchanged: List[Expression] = {for (g <- st3.globals - lhs)
      yield BinOp("==", g.toVar, g.toVar.prime)}.toList
    val guarP: Predicate = st1.P.add(BinOp("==", lhs.toVar.prime, _rhs) :: guarUnchanged) ++ PRestrictU

    if (st3.debug) {
      println("checking assignment conforms to guarantee")
    }
    if (!SMT.proveImplies(guarP, st3.G, st3.debug)) {
      throw error.AssignGError(line, lhs, rhs, "assignment doesn't conform to guarantee " + st3.G)
    }

    // check t <:_P L_G(x)
    // L_G(x) && P ==> t
    if (st3.debug) {
      println("checking L_G(x) && P /restrict u ==> t holds")
    }
    if (t.predicates != List(Const._true) && !SMT.proveImplies(PRestrictU.add(st3.L_G(lhs)), t, st3.debug)) {
      throw error.AssignGError(line, lhs, rhs, "L_G(" + lhs + ") && P ==> " + lhs + " doesn't hold for assignment")
    }

    val PRestrictUState = st3.copy(P = PRestrictU)
    val PPlusR = PRestrictUState.PPlusRUpdate(lhs, _rhs)
    val knownU = st3.knownU
    val knownW = st3.knownW
    val knownR = st3.knownR

    val toSubstC: Subst = Map(lhs.toVar -> _rhs)  // to get c[e/x]
    if (st3.debug) {
      println("checking weaker")
    }
    /*
    var weaker: Set[Id] = Set()
    for (y <- st3.R_var.keySet) {
      // check !(P && c ==> c[e/x])
      val weakerCheck: List[Expression] = for ((c, r) <- st3.R_var(y) if c != Const._true)
        yield PreOp("!", BinOp("==>", BinOp("&&", c, PAnd), c.subst(toSubstC)))
      if (SMT.proveListOr(weakerCheck, st3.debug)) {
        weaker += y
      }
    }
     */

    var weaker: Set[Id] = Set()
    for (y <- st3.R_var.keySet) {
      // check !(P && c ==> c[e/x])
      var yAdded = false
      for ((c, _) <- st3.R_var(y) if !yAdded && c != Const._true) {
        if (!SMT.proveImplies(PRestrictU.add(c), c.subst(toSubstC), st3.debug)) {
          weaker +=y
          yAdded = true
        }
      }
    }

    if (st3.debug) {
      println("weaker: " + weaker)
      println("knownU " + knownU)
    }

    if (!(weaker subsetOf knownU)) {
      throw error.AssignGError(line, lhs, rhs, "weaker set: " + weaker + " is not subset of knownU: " + knownU)
    }

    if (st3.debug) {
      println("checking falling")
    }
    val falling: Set[Id] = for (x <- st3.globals if (st3.written & st3.L(x).variables).nonEmpty &&
      !SMT.proveImplies(PRestrictU, st3.L_G(x), st3.debug) &&
      !SMT.proveImplies(PPlusR, PreOp("!", st3.L_G(x)), st3.debug))
      yield x

    if (st3.debug) {
      println("falling: " + falling)
    }

    val fallingCompare: Set[Id] = for (y <- knownW & st3.gamma.keySet if SMT.proveImplies(PRestrictU, st3.gamma(y), st3.debug))
      yield y

    if (st3.debug) {
      println("fallingCompare: " + fallingCompare)
    }

    if (!(falling subsetOf fallingCompare)) {
      throw error.AssignGError(line, lhs, rhs, "falling set: " + falling + " is not subset of: " + fallingCompare)
    }

    if (st3.debug) {
      println("checking rising")
    }
    val rising: Set[Id] = for (x <- st3.globals if (st3.written & st3.L(x).variables).nonEmpty &&
      !SMT.proveImplies(PRestrictU, PreOp("!", st3.L(x)), st3.debug) &&
      !SMT.proveImplies(PPlusR, st3.L(x), st3.debug))
      yield x

    if (st3.debug) {
      println("rising: " + rising)
      println("knownR " + knownR)
    }

    if (!(rising subsetOf knownR)) {
      throw error.AssignGError(line, lhs, rhs, "rising set: " + rising + " is not subset of knownR: " + knownR)
    }

    if (st3.debug) {
      println("checking shrink")
    }
    var shrink: Set[Id] = Set()
    for (x <- st3.globals) {
      val cIdentities: List[Expression] = if (st3.R_var.contains(x)) {
        for ((c, r) <- st3.R_var(x) if r == BinOp("==", x.toVar, x.toVar.prime) || r == BinOp("==", x.toVar.prime, x.toVar))
          yield c
      } else {
        List()
      }
      val low_or_eq_exp = State.orPredicates(st3.L_R(x) :: cIdentities)
      if ((st3.written & low_or_eq_exp.variables).nonEmpty &&
        !SMT.proveImplies(PRestrictU, PreOp("!", low_or_eq_exp), st3.debug) &&
        !SMT.proveImplies(PPlusR, low_or_eq_exp, st3.debug)) {
        shrink += x
      }
    }

    if (st3.debug) {
      println("shrink: " + shrink)
      println("knownR " + knownR)
    }

    if (!(shrink subsetOf knownR)) {
      throw error.AssignGError(line, lhs, rhs, "shrink set: " + shrink + " is not subset of knownR: " + knownR)
    }

    if (st3.debug) {
      println("checking stronger")
    }
    var stronger: Set[Id] = Set()
    for (x <- st3.G_var.keySet) {
      // check !(P ==> c) && !(P + R ==> !c)
      var xAdded = false
      for ((c, _) <- st3.G_var(x)) {
        if (!xAdded && (st3.written & c.variables).nonEmpty &&
          !SMT.proveImplies(PRestrictU, c, st3.debug) &&
          !SMT.proveImplies(PPlusR, PreOp("!", c), st3.debug)) {
          stronger += x
          xAdded = true
        }
      }
    }

    if (st3.debug) {
      println("stronger: " + stronger)
      println("knownW " + knownW)
    }

    if (!(stronger subsetOf knownW)) {
      throw error.AssignGError(line, lhs, rhs, "stronger set: " + stronger + " is not subset of knownW: " + knownW)
    }

    val (st4, m, exists) = st3.assignUpdateP(lhs, _rhs)
    val st5 = st4.assignUpdateGamma(lhs, t, m, exists)
    st5.updateDAssign(lhs, _rhs)
  }

  /*
  def compareAndSwapRule(lhs: Id, x: Id, r1: Expression, r2: Expression, st0: State, line: Int): State = {
    // CAS rule
    if (st0.toLog)
      println("CAS applying")
    // compute rd
    val (_r1, st1) = eval(r1, st0)
    val (_r2, st2) = eval(r2, st1)
    val st3 = st2.updateRead(x)
    // compute wr
    val st4 = st3.updateWritten(x)
    val st5 = st4.updateWritten(lhs)
    // at this point the rd and wr sets are complete for the current line

    if (st5.controls.contains(lhs)) {
      throw error.CASError(line, lhs, x, r1, r2, "LHS of CAS assignment is a control variable")
    }

    val knownw = st5.knownW
    val PRestrict = st5.restrictP(knownw)
    if (st0.debug) {
      println("knownW: " + knownw)
      println("PRestrict: " + PRestrict.PStr)
    }

    // check any array indices in r1 are low
    for (i <- _r1.arrays) {
      if (st5.security(i.index, PRestrict) == High) {
        throw error.CASError(line, lhs, x, r1, r2, "array index " + i.index + " is HIGH")
      }
    }

    // check any array indices in r2 are low
    for (i <- _r2.arrays) {
      if (st5.security(i.index, PRestrict) == High) {
        throw  error.CASError(line, lhs, x, r1, r2, "array index " + i.index + " is HIGH")
      }
    }

    if (st5.security(x, PRestrict) == High) {
      throw error.CASError(line, lhs, x, r1, r2, "HIGH expression in first parameter of CAS")
    }
    if (st5.security(_r1, PRestrict) == High) {
      throw error.CASError(line, lhs, x, r1, r2, "HIGH expression in second parameter of CAS")
    }

    val PRestrictAssign = BinOp("==", x.toVar, _r1) :: PRestrict
    if (st0.debug) {
      println("PRestrictAssign: " + PRestrictAssign.PStr)
    }
    val t2 = st5.security(_r2, PRestrictAssign)


    // if x's mode is not NoRW, ensure that e's security level is not higher than x's security level, given P_x:=e - tested
    if (!st5.noReadWrite.contains(x) && t2 == High) { // optimisation to not check t2 security unless necessary
      // evalP
      val xSecurity = if (st5.highP(x, PRestrictAssign)) {
        High
      } else {
        Low
      }
      if (t2 > xSecurity) {
        throw error.CASError(line, lhs, x, r1, r2, "HIGH expression in third parameter of CAS potentially assigned to LOW expression in first parameter")
      }
    }
    val st6 = st5.updateGamma(lhs, Low)
    val st7 = st6.updateGammaCAS(x, t2)

    // update P
    val st8 = st7.assignCAS(lhs, x, _r1, _r2)
    st8.updateDCAS(lhs, x, _r1, _r2)
  }

  def compareAndSwapCRule(lhs: Id, x: Id, r1: Expression, r2: Expression, st0: State, line: Int): State = {
    // CASC rule
    if (st0.toLog)
      println("CASC applying")
    // computes rd
    val (_r1, st1) = eval(r1, st0)
    val (_r2, st2) = eval(r2, st1)
    val st3 = st2.updateRead(x)
    // computes wr
    val st4 = st3.updateWritten(x)
    val st5 = st4.updateWritten(lhs)
    // at this point the rd and wr sets are complete for the current line

    if (st5.controls.contains(lhs)) {
      throw error.CASCError(line, lhs, x, r1, r2, "LHS of CAS assignment is a control variable")
    }

    val knownw = st5.knownW
    val PRestrict = st5.restrictP(knownw)
    if (st0.debug) {
      println("knownW: " + knownw)
      println("PRestrict: " + PRestrict.PStr)
    }

    // check any array indices in r1 are low
    for (i <- _r1.arrays) {
      if (st5.security(i.index, PRestrict) == High) {
        throw error.CASCError(line, lhs, x, r1, r2, "array index " + i.index + " is HIGH")
      }
    }

    // check any array indices in r2 are low
    for (i <- _r2.arrays) {
      if (st5.security(i.index, PRestrict) == High) {
        throw error.CASCError(line, lhs, x, r1, r2, "array index " + i.index + " is HIGH")
      }
    }

    if (st5.security(_r1, PRestrict) == High) {
      throw error.CASCError(line, lhs, x, r1, r2, "HIGH expression in second parameter of CAS compared to control variable in first parameter")
    }

    val PRestrictAssign = BinOp("==", x.toVar, _r1) :: PRestrict
    if (st0.debug) {
      println("PRestrictAssign: " + PRestrictAssign.PStr)
    }

    // highP check is to check that x == r1 is possible, meaning that the x = r2 assignment is possible
    if (!st5.highP(x, PRestrictAssign) && (st5.security(_r2, PRestrictAssign) == High)) {
      throw error.CASCError(line, lhs, x, r1, r2, "HIGH expression in third parameter of CAS possibly assigned to control variable in first parameter")
    }

    // secure_update
    val PPrime = st5.addToP(BinOp("==", x.toVar, _r1)).assign(x, _r2) // calculate PPrime
    val PPrimeRestrict = PPrime.restrictP(knownw)

    val falling = for (i <- st5.controlledBy(x) if (!st5.lowP(i, PRestrictAssign)) && !st5.highP(i, PPrimeRestrict))
      yield i

    if (st0.debug) {
      println("falling: " + falling)
      println("knownW: " + knownw)
    }

    //val fallingFail = for (y <- falling -- st5.noReadWrite if !knownw.contains(y) || st5.security(y, PRestrictAssign) == High)

    // falling can only succeed if y is in gamma and maps to low
    val fallingFail = for (y <- falling -- st5.noReadWrite if !st5.gamma.contains(y) || st5.gamma(y) != Low)
      yield y

    if (fallingFail.nonEmpty) {
      throw error.CASCError(line, lhs, x, r1, r2, "secure update fails for falling variable/s: " + fallingFail.mkString(" "))
    }

    val rising = for (i <- st5.controlledBy(x) if (!st5.highP(i, PRestrictAssign)) && !st5.lowP(i, PPrimeRestrict))
      yield i

    if (st0.debug) {
      println("rising: " + rising)
    }
    val knownR = st5.knownR
    val risingFail = for (y <- rising if !knownR.contains(y))
      yield y

    if (risingFail.nonEmpty) {
      throw error.CASCError(line, lhs, x, r1, r2, "secure update fails for rising variable/s: " + risingFail.mkString(" "))
    }

    val st6 = st5.updateGamma(lhs, Low)

    val st7 = st6.assignCAS(lhs, x, _r1, _r2)
    st7.updateDCAS(lhs, x, _r1, _r2)
  }
   */

  // evaluate multiple expressions
  def evals(exprs: List[Expression], pre: State): (List[Expression], State) = exprs match {
    case Nil =>
      (Nil, pre)

    case expr :: rest => // XXX: right-to-left, should be parallel
      val (xs, st) = evals(rest, pre)
      val (x, post) = eval(expr, st)
      (x :: xs, post)
  }

}
