package wemelt

// remnant of handling break/continue/returns - might be useful in future
sealed trait Cont {
  def st: State
}

object Cont {
  case class next(st: State) extends Cont
  /*
  case class break(st: State) extends Cont
  case class cont(st: State) extends Cont
  case class ret(result: Expression, st: State) extends Cont */
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

      /*
    case Atomic(expr) =>

      val (_, state1) = rval(expr, state0)

      Cont.next(state1.resetReadWrite())
       */


    case block: Block =>
      // blocks currently leak local definitions but this isn't important for this application
      execute(block.statements, state0)

      /*
    case Continue =>
      Cont.cont(state0)

    case Break =>
      Cont.break(state0)

    case Return(None) =>
      Cont.ret(Lit("void"), state0)

    case Return(Some(expr)) =>
      val (_expr, st1) = rval(expr, state0)
      Cont.ret(_expr, st1)

       */

    case Assignment(lhs, rhs) =>
      if (state0.toLog)
        println("line " + statement.line + ": " + lhs + " = " + rhs + ":")
      // check if lhs is a control variable
      val state1 = if (state0.controls.contains(lhs)) {
        assignCRule(lhs, rhs, state0, statement.line)
      } else {
        assignRule(lhs, rhs, state0, statement.line)
      }
      // check nonblocking rule if necessary
      if (state1.nonblocking && state1.globals.contains(lhs)) {
        throw error.NonblockingError(statement.line, statement, "global variable " + lhs + " was written to within a nonblocking while loop")
      }
      state1.log
      Cont.next(state1)

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

    case While(test, invariants, gamma, None, body) =>
      if (state0.toLog)
        println("line " + statement.line + ": While(" + test + ") {")
      // replace Ids in invariant with vars
      val idToVar: Subst = {
        for (v <- state0.variables)
          yield v -> v.toVar
        }.toMap ++ {
        for (v <- state0.arrays.keySet)
          yield v -> v.toVar
      }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Security] = (gamma flatMap {g => g.toPair(state0.arrays)}).toMap

      val state1 = whileRule(test, PPrime, gammaPrime, body, state0, statement.line)
      if (state0.toLog)
        println("end of line " + statement.line + ": While(" + test + ")")
      state1.log
      if (state0.toLog)
        println("}")
      Cont.next(state1)

    case DoWhile(test, invariants, gamma, None, body) =>
      if (state0.toLog)
        println("line " + statement.line + ": While(" + test + ") {")
      // replace Ids in invariant with vars
      val idToVar: Subst = {
        for (v <- state0.variables)
          yield v -> v.toVar
        }.toMap ++ {
        for (v <- state0.arrays.keySet)
          yield v -> v.toVar
        }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Security] = (gamma flatMap {g => g.toPair(state0.arrays)}).toMap

      // execute loop body once at start
      val state1 = execute(body, state0).st

      val state2 = whileRule(test, PPrime, gammaPrime, body, state1, statement.line)
      if (state0.toLog)
        println("end of line " + statement.line + ": While(" + test + ")")
      state2.log
      if (state0.toLog)
        println("}")
      Cont.next(state2)

    // nonblocking rule
    case While(test, invariants, gamma, Some(stable), body) =>
      // replace array wildcard with whole array
      val _stable = stable flatMap {
        case i if state0.arrays.keySet.contains(i) =>
          state0.arrays(i).array
        case i =>
          Set(i)
      }
      val (oldMode, state1) = startNonBlocking(_stable, state0)

      if (state1.toLog)
        println("line " + statement.line + ": While(" + test + ") {")
      // replace Ids in invariant with vars
      val idToVar: Subst = {
        for (v <- state0.variables)
          yield v -> v.toVar
        }.toMap ++ {
        for (v <- state0.arrays.keySet)
          yield v -> v.toVar
        }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Security] = (gamma flatMap {g => g.toPair(state0.arrays)}).toMap

      val state2 = whileRule(test, PPrime, gammaPrime, body, state1, statement.line)
      state2.log
      val state3 = endNonBlocking(_stable, oldMode, state2)
      state3.log
      if (state3.toLog)
        println("}")

      Cont.next(state3)

    // nonblocking rule
    case DoWhile(test, invariants, gamma, Some(stable), body) =>
      // replace array wildcard with whole array
      val _stable = stable flatMap {
        case i if state0.arrays.keySet.contains(i) =>
          state0.arrays(i).array
        case i =>
          Set(i)
      }
      val (oldModes, state1) = startNonBlocking(_stable, state0)

      if (state1.toLog)
        println("line " + statement.line + ": While(" + test + ") {")
      // replace Ids in invariant with vars
      val idToVar: Subst = {
        for (v <- state0.variables)
          yield v -> v.toVar
        }.toMap ++ {
        for (v <- state0.arrays.keySet)
          yield v -> v.toVar
        }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Security] = (gamma flatMap {g => g.toPair(state0.arrays)}).toMap

      // execute loop body once at start
      val state2 = execute(body, state1).st

      val state3 = whileRule(test, PPrime, gammaPrime, body, state2, statement.line)
      state3.log
      val state4 = endNonBlocking(_stable, oldModes, state3)
      state4.log
      if (state4.toLog)
        println("}")

      Cont.next(state4)


    case _ =>
      throw error.InvalidProgram("unimplemented statement " + statement + " at line " + statement.line)

  }

  // compute fixed point of D
  def DFixedPoint(test: Expression, body: Statement, state: State): Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = {
    var DFixed = false
    var st0 = state
    var DPrime: Map[Id, (Set[Id], Set[Id], Set[Id], Set[Id])] = Map()
    var dfixedloops = 0
    if (st0.debug)
      println("DFixed0: " + st0.D.DStr)
    while (!DFixed) {
      dfixedloops = dfixedloops + 1
      // update rd for the guard
      val st1 = DFixedPoint(test, st0)
      val st2 = st1.updateDGuard(test)
      val st3 = DFixedPoint(body, st2)
      // intersect with original D after loop body
      val st4 = st3.copy(D = st3.mergeD(state))

      if (st0.debug) {
        println("DFixed" + (dfixedloops - 1) + ": " + st0.D.DStr)
        println("DFixed" + dfixedloops + ": " + st4.D.DStr)
      }
      // compare st4.D to st0.D
      val it = st0.variables.toIterator
      DFixed = true
      while (it.hasNext && DFixed) {
        val v = it.next
        DFixed = (st0.W_r(v) == st4.W_r(v)) && (st0.W_w(v) == st4.W_w(v)) && (st0.R_r(v) == st4.R_r(v)) && (st0.R_w(v) == st4.R_w(v))
      }
      // if D has changed, repeat
      if (DFixed) {
        DPrime = st4.D
      } else {
        st0 = st4
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
      val st1 = DFixedPoint(rhs, st0)
      val st2 = st1.updateWritten(lhs)
      st2.updateDAssign(lhs, rhs)

    case ArrayAssignment(name, index, rhs) =>
      val st1 = DFixedPoint(rhs, st0)
      val st2 = DFixedPoint(index, st1)
      val st3 = st2.updateWritten(st2.arrays(name))
      st3.updateDArrayAssign(name, rhs)

    case Fence =>
      // reset D
      st0.updateDFence

    case ControlFence =>
      // reset D
      val st1 = st0.updateWritten(CFence)
      st1.updateDCFence

    case If(test, left, None) =>
      // evaluate test which updates D
      val st1 = DFixedPoint(test, st0)
      val st2 = st1.updateDGuard(test)

      // right branch is empty
      val _left = DFixedPoint(left, st2)
      st2.copy(D = _left.mergeD(st2))

    case If(test, left, Some(right)) =>
      // evaluate test which updates D
      val st1 = DFixedPoint(test, st0)
      val st2 = st1.updateDGuard(test)

      val _left = DFixedPoint(left, st2)
      val _right = DFixedPoint(right, st2)
      st2.copy(D =_left.mergeD(_right))

    case While(test, invariants, gamma, _, body) =>
      st0.copy(D = DFixedPoint(test, body, st0))

    case DoWhile(test, invariants, gamma, _, body) =>
      val st1 = DFixedPoint(body, st0)
      st1.copy(D = DFixedPoint(test, body, st0))

    case CompareAndSwap(r3, x, r1, r2) =>
      val st1 = DFixedPoint(r1, st0)
      val st2 = DFixedPoint(r2, st1)
      val st3 = st2.updateRead(x)
      val st4 = st3.updateWritten(x)
      val st5 = st4.updateWritten(r3)
      st5.updateDCAS(r3, x, r1, r2)

    case _ =>
      throw error.InvalidProgram("unimplemented statement at line " + statement.line + ": " + statement)
  }

  def DFixedPoint(expr: Expression, st0: State): State = expr match {
    case id: Id =>
      st0.updateRead(id)

    case res: Lit =>
      st0

    case res: Const =>
      st0

    case Access(name, index) =>
      val st1 = DFixedPoint(index, st0)
      st1.updateRead(st1.arrays(name))

    case BinOp(_, arg1, arg2) =>
      val st1 = DFixedPoint(arg1, st0)
      DFixedPoint(arg2, st1)

    case PreOp(_, arg) =>
      DFixedPoint(arg, st0)

    case _ =>
      throw error.InvalidProgram("unimplemented expression: " + expr)
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

    case Access(name, index) =>
      val (_index, st1) = eval(index, st0)
      val st2 = st1.updateRead(st1.arrays(name))
      (VarAccess(name.toVar, _index), st2)

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

  def ifRule(test: Expression, left: Statement, right: Option[Statement], state0: State, line: Int): State = {
    // IF rule
    if (state0.toLog)
      println("IF applying")

    // evaluate test
    val (_test, state1) = eval(test, state0)

    // check test is LOW
    val PRestrict = state1.restrictP(state1.knownW) // calculate P_b
    if (state0.debug)
      println("P_b: " + PRestrict.PStr)

    // check any array indices in test are low
    for (i <- _test.arrays) {
      if (state1.security(i.index, PRestrict) == High) {
        throw error.IfError(line, test, "array index " + i.index + " is HIGH")
      }
    }

    if (state1.security(_test, PRestrict, true) == High) {
      throw error.IfError(line, test, "guard expression is HIGH")
    }

    val state2 = state1.updateDGuard(_test)
    if (state0.toLog)
      println("D[b]: " + state2.D.DStr)

    // execute both sides of if statement
    val _left = state2.updatePIfLeft(_test)
    val _left1 = if (state2.noInfeasible) {
      // don't check infeasible paths
      if (SMT.proveP(_left.P, _left.debug)) {
        execute(left, _left).st
      } else {
        _left
      }
    } else {
      execute(left, _left).st
    }

    val _right1: State = right match {
      case Some(r) =>
        if (state0.toLog)
          println("} else {")
        val _right = state2.updatePIfRight(_test)
        if (state2.noInfeasible) {
          // don't check infeasible paths
          if (SMT.proveP(_right.P, _right.debug)) {
            execute(r, _right).st
          } else {
            _right
          }
        } else {
          execute(r, _right).st
        }
      case None =>
        state2.updatePIfRight(_test)
    }

    // merge states
    _left1.mergeIf(_right1)
  }

  def whileRule(test: Expression, PPrime: List[Expression], gammaPrime: Map[Id, Security], body: Statement, state0: State, line: Int): State = {
    // WHILE rule

    if (state0.toLog)
      println("WHILE applying")

    // P' only contains stable variables - tested
    val PPrimeArrayAccess: Set[Id] = {PPrime flatMap {x => x.arrays flatMap {y => state0.arrays(y.name).array}}}.toSet

    val PPrimeVar: Set[Id] = (PPrime flatMap {x => x.variables}).toSet ++ PPrimeArrayAccess

    val unstablePPrime = for (i <- PPrimeVar if !state0.stable.contains(i))
      yield i
    if (unstablePPrime.nonEmpty) {
      throw error.WhileError(line, test, unstablePPrime.mkString(", ") + " in invariant is/are not stable")
    }

    // check P' is weaker than previous P - tested
    if (!SMT.proveImplies(state0.P, PPrime, state0.debug)) {
      throw error.WhileError(line, test, "provided P' " + PPrime.PStr + " is not weaker than P " + state0.P.PStr)
    }

    // gamma' has same domain as gamma - tested
    if (state0.gamma.keySet != gammaPrime.keySet) {
      throw error.InvalidProgram("input gamma " + gammaPrime.gammaStr + " for While(" +  test + ") { ... at line " + line + " does not have same domain as gamma: " + state0.gamma.gammaStr)
    }

    // check gamma' is greater or equal than gamma for all x - tested
    val gammaGreater = for (g <- state0.gamma.keySet if state0.gamma(g) > gammaPrime(g))
      yield g
    if (gammaGreater.nonEmpty) {
      throw error.WhileError(line, test, "gamma' " + gammaPrime.gammaStr + " is not greater than or equal to gamma " + state0.gamma.gammaStr + " for: " + gammaGreater.mkString(" "))
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

    val DPrime = DFixedPoint(test, body, state0)
    if (state0.debug)
      println("D': " + DPrime.DStr)

    val state1 = state0.copy(P = PPrime, gamma = gammaPrime, D = DPrime)

    // check D' is subset of D
    for (v <- state0.variables) {
      if (!((state1.W_r(v) subsetOf state0.W_r(v)) && (state1.W_w(v) subsetOf state0.W_w(v)) && (state1.R_r(v) subsetOf state0.R_r(v)) && (state1.R_w(v) subsetOf state0.R_w(v))))
        throw error.ProgramError("line " + line + ": D' is not a subset of D." + newline + "D': " +  state1.D.DStr + newline + "D: " + state0.D.DStr)
    }

    // evaluate test and update D
    val (_test, state2) = eval(test, state1)
    val state3 = state2.updateDGuard(_test)

    // check any array indices in test are low
    for (i <- _test.arrays) {
      if (state3.security(i.index, state3.P) == High) {
        throw error.WhileError(line, test, "array index " + i.index + " is HIGH")
      }
    }

    // check test is LOW with regards to P', gamma' - tested
    if (state3.security(_test, state3.P, true) == High) {
      throw error.WhileError(line, test, "guard expression is HIGH")
    }

    // add test to P
    val state4 = state3.updatePIfLeft(_test)

    if (state0.debug) {
      println("while rule after test, before loop body:")
      println("gamma':" + state4.gamma.gammaStr)
      println("P and [e]_M:" + state4.P.PStr)
    }

    // evaluate body
    val _body = execute(body, state4)
    val state5 = _body.st

    if (state0.debug) {
      println("while rule after loop body:")
      println("gamma': " + gammaPrime.gammaStr)
      println("P' :" + PPrime.PStr)

      println("gamma'': " + state5.gamma.gammaStr)
      println("P'' :" + state5.P.PStr)
    }

    // this shouldn't be able to happen if D' is calculated correctly
    // check D' is subset of D''
    for (v <- state0.variables) {
      if (!((state1.W_r(v) subsetOf state5.W_r(v)) && (state1.W_w(v) subsetOf state5.W_w(v)) && (state1.R_r(v) subsetOf state5.R_r(v)) && (state1.R_w(v) subsetOf state5.R_w(v))))
        throw error.ProgramError("line " + line + ": D' is not a subset of D''." + newline + "D': " +  state1.D.DStr + newline + "D'': " + state5.D.DStr)
    }

    // check gamma' is greater or equal than gamma'' for all x - tested
    val gammaPrimeGreater = for (g <- gammaPrime.keySet if state5.gamma(g) > gammaPrime(g))
      yield g
    if (gammaPrimeGreater.nonEmpty) {
        throw error.WhileError(line, test, "gamma' " + gammaPrime.gammaStr + " is not greater to or equal than than gamma'' " +  state5.gamma.gammaStr + " for: " + gammaPrimeGreater.mkString(" "))
    }

    // check P'' is stronger than P' - tested
    if (!SMT.proveImplies(state5.P, PPrime, state0.debug)) {
      throw error.WhileError(line, test, "provided P' " + PPrime.PStr + " does not hold after loop body. P'': " + state5.P.PStr)
    }

    // state1 used here as do not keep gamma'', P'', D'' from after loop body execution
    // remove test from P'
    state1.updatePIfRight(_test)
  }


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

  def assignRule(lhs: Id, rhs: Expression, st0: State, line: Int): State = {
    // ASSIGN rule
    if (st0.toLog)
      println("ASSIGN applying")
    val (_rhs, st1) = eval(rhs, st0) // computes rd
    val st2 = st1.updateWritten(lhs) // computes wr
    // at this point the rd and wr sets are complete for the current line

    val knownw = st2.knownW
    // calculate P_x:=e
    val PRestrict = st2.restrictP(knownw)
    if (st0.debug) {
      println("knownW: " + knownw)
      println("PRestrict: " + PRestrict.PStr)
    }

    // check any array indices in rhs are low
    for (i <- _rhs.arrays) {
      if (st2.security(i.index, PRestrict) == High) {
        throw error.AssignError(line, lhs, rhs, "array index " + i.index + " is HIGH")
      }
    }

    val t = st2.security(_rhs, PRestrict)

    // if x's mode is not NoRW, ensure that e's security level is not higher than x's security level, given P_x:=e - tested
    if (!st2.noReadWrite.contains(lhs) && t == High) { // optimisation to not check x security unless necessary
      // evalP
      val xSecurity = if (st2.highP(lhs, PRestrict)) {
        High
      } else {
        Low
      }
      if (t > xSecurity) {
        throw error.AssignError(line, lhs, rhs, "HIGH expression assigned to LOW variable")
      }
    }
    val st3 = st2.updateGamma(lhs, t)

    val st4 = st3.assign(lhs, _rhs) // update P
    st4.updateDAssign(lhs, _rhs)
  }

  def assignCRule(lhs: Id, rhs: Expression, st0: State, line: Int): State = {
    // ASSIGNC rule
    if (st0.toLog)
      println("ASSIGNC applying")
    val (_rhs, st1) = eval(rhs, st0)
    val st2 = st1.updateWritten(lhs)
    // at this point the rd and wr sets are complete for the current line

    val knownw = st2.knownW
    // calculate P_x:=e
    val PRestrict = st2.restrictP(knownw)
    if (st0.debug) {
      println("knownW: " + knownw)
      println("PRestrict: " + PRestrict.PStr)
    }

    // check any array indices in rhs are low
    for (i <- _rhs.arrays) {
      if (st2.security(i.index, PRestrict) == High) {
        throw error.AssignCError(line, lhs, rhs, "array index " + i.index + " is high")
      }
    }

    // check _rhs is LOW - tested
    val t = st2.security(_rhs, PRestrict)
    if (t == High) {
      throw error.AssignCError(line, lhs, rhs, "HIGH expression assigned to control variable")
    }

    // secure_update
    val PPrime = st2.assign(lhs, _rhs) // calculate PPrime
    val PPrimeRestrict = PPrime.restrictP(knownw)

    val falling = for (i <- st2.controlledBy(lhs) if (!st2.lowP(i, PRestrict)) && !st2.highP(i, PPrimeRestrict))
      yield i

    if (st0.debug) {
      println("falling: " + falling)
      println("knownW: " + knownw)
    }

    //val fallingFail = for (y <- falling -- st2.noReadWrite if !knownw.contains(y) || st2.security(y, PRestrict) == High)

    // falling can only succeed if y is in gamma and maps to low
    val fallingFail = for (y <- falling -- st2.noReadWrite if !st2.gamma.contains(y) || st2.gamma(y) != Low)
      yield y

    if (fallingFail.nonEmpty) {
      throw error.AssignCError(line, lhs, rhs, "secure update fails for falling variable/s: " + fallingFail.mkString(" "))
    }

    val rising = for (i <- st2.controlledBy(lhs) if (!st2.highP(i, PRestrict)) && !st2.lowP(i, PPrimeRestrict))
      yield i

    if (st0.debug) {
      println("rising: " + rising)
    }
    val risingFail = for (y <- rising if !st2.knownR.contains(y))
      yield y

    if (risingFail.nonEmpty) {
      throw error.AssignCError(line, lhs, rhs, "secure update fails for rising variable/s: " + risingFail.mkString(" "))
    }

    val st3 = st2.assign(lhs, _rhs) // update P
    st3.updateDAssign(lhs, _rhs)
  }

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


  // start application of the nonblocking rule
  def startNonBlocking(stable: Set[Id], state0: State): (Map[Id, Mode], State) = {
    // add stable set to gamma
    val state1 = state0.updateRead(stable)
    val PRestrict = state1.restrictP(state1.knownW)

    var zSec: Map[Id, Security] = Map()
    for (z <- stable) {
      zSec += (z -> state1.security(z, PRestrict))
    }
    val state2 = state1.updateGammasDomain(zSec)
    val state3 = state2.resetReadWrite()
    if (state3.debug) {
      println("previous gamma: " + state1.gamma.gammaStr)
      println("updated gamma: " + state3.gamma.gammaStr)
    }


    // make z noW
    val oldModes: Map[Id, Mode] = {stable map {
      case z if state3.noWrite.contains(z) =>
        z -> NoW
      case z if state3.noReadWrite.contains(z) =>
        z -> NoRW
      case z if state3.readWrite.contains(z) =>
        z -> RW
      case z =>
        z -> Reg
    }}.toMap
    for (z <- stable) {
      if (oldModes(z) == Reg) {
        throw error.ProgramError(z + " does not have a mode - internal error")
      }
    }

    val state4 = state3.setModes(stable, NoW)
    if (state4.debug) {
      println("previous modes: ")
      println("no read write: " + state3.noReadWrite)
      println("read write: " + state3.readWrite)
      println("no write: " + state3.noWrite)
      println("stable: " + state3.stable)
      println("current modes: ")
      println("no read write: " + state4.noReadWrite)
      println("read write: " + state4.readWrite)
      println("no write: " + state4.noWrite)
      println("stable: " + state4.stable)
    }

    // increment nonblocking depth so that the nonblocking rule will be checked while executing loop contents
    val state5 = state4.copy(nonblocking = true, nonblockingDepth = state4.nonblockingDepth + 1)

    (oldModes, state5)
  }

  // end application of the nonblocking rule for variables, restoring their mode to oldMode
  def endNonBlocking(stable: Set[Id], oldModes: Map[Id, Mode], state0: State): State = {
    // restore original modes
    val state1 = state0.setModes(oldModes)

    if (state1.debug) {
      println("previous modes: ")
      println("no read write: " + state0.noReadWrite)
      println("read write: " + state0.readWrite)
      println("no write: " + state0.noWrite)
      println("stable: " + state0.stable)
      println("current modes: ")
      println("no read write: " + state1.noReadWrite)
      println("read write: " + state1.readWrite)
      println("no write: " + state1.noWrite)
      println("stable: " + state1.stable)
    }

    // remove z from gamma
    val state2 = state1.removeGamma(stable)
    if (state2.debug) {
      println("previous gamma: " + state1.gamma.gammaStr)
      println("updated gamma: " + state2.gamma.gammaStr)
    }

    // decrement nonblocking depth so that the nonblocking rule will not be applied anymore if all nonblocking loops
    // are finished
    val state3 = if (state2.nonblockingDepth == 1) {
      state2.copy(nonblocking = false, nonblockingDepth = state2.nonblockingDepth - 1)
    } else {
      state2.copy(nonblockingDepth = state2.nonblockingDepth - 1)
    }
    state3
  }


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
