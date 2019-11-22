package tool

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
        throw error.NonblockingError(statement.line, lhs, rhs, "global variable " + lhs + " was written to within a nonblocking while loop")
      }
      state1.log
      Cont.next(state1.resetReadWrite())

    case Fence =>
      // reset D
      val state1 = state0.updateDFence()
      if (state0.toLog)
        println("fence:")
      state1.log
      Cont.next(state1)

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
        }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Security] = (gamma map {g => g.variable -> g.security}).toMap

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
        }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Security] = (gamma map {g => g.variable -> g.security}).toMap

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
    case While(test, invariants, gamma, Some(z), body) =>

      val (oldZMode, state1) = startNonBlocking(z, state0)

      if (state1.toLog)
        println("line " + statement.line + ": While(" + test + ") {")
      // replace Ids in invariant with vars
      val idToVar: Subst = {
        for (v <- state0.variables)
          yield v -> v.toVar
        }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Security] = (gamma map {g => g.variable -> g.security}).toMap

      val state2 = whileRule(test, PPrime, gammaPrime, body, state1, statement.line)
      state2.log
      val state3 = endNonBlocking(z, oldZMode, state2)
      state3.log
      if (state3.toLog)
        println("}")

      Cont.next(state3)

    // nonblocking rule
    case DoWhile(test, invariants, gamma, Some(z), body) =>

      val (oldZMode, state1) = startNonBlocking(z, state0)

      if (state1.toLog)
        println("line " + statement.line + ": While(" + test + ") {")
      // replace Ids in invariant with vars
      val idToVar: Subst = {
        for (v <- state1.variables)
          yield v -> v.toVar
        }.toMap

      val PPrime = invariants map {i => i.subst(idToVar)}

      // convert gammaPrime to map
      val gammaPrime: Map[Id, Security] = (gamma map {g => g.variable -> g.security}).toMap

      // execute loop body once at start
      val state2 = execute(body, state1).st

      val state3 = whileRule(test, PPrime, gammaPrime, body, state2, statement.line)
      state3.log
      val state4 = endNonBlocking(z, oldZMode, state3)
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
    while (!DFixed) {
      dfixedloops = dfixedloops + 1
      // update rd for the guard
      val st1 = DFixedPoint(test, st0)
      val st2 = st1.updateDGuard(test)
      val st3 = DFixedPoint(body, st2)
      // D intersect D after loop body
      val st4 = st3.copy(D = st3.mergeD(st0))

      // compare st4.D to st0.D
      val it = st0.variables.toIterator
      while (it.hasNext && !DFixed) {
        val v = it.next
        DFixed = (st0.W_r(v) == st4.W_r(v)) && (st0.W_w(v) == st4.W_w(v)) && (st0.R_r(v) == st4.R_r(v)) && (st0.R_w(v) == st4.R_w(v))
      }

      // if D has changed, repeat
      if (DFixed) {
        DPrime = st4.D
      } else {
        st0 = st4
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

    case Fence =>
      // reset D
      st0.updateDFence()

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

      /*
    case Access(name, index) =>
      val (_index, st1) = eval(index, st0)
      (Access(name, _index), st1)
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

  def ifRule(test: Expression, left: Statement, right: Option[Statement], state0: State, line: Int): State = {
    // IF rule
    if (state0.toLog)
      println("IF applying")

    // evaluate test which updates D
    val (_test, state1) = eval(test, state0)
    val state2 = state1.updateDGuard(_test)

    // check test is LOW
    val PRestrict = state2.restrictP(state2.knownW) // calculate P_b
    if (state2.security(_test, PRestrict) == High) {
      throw error.IfError(line, test, "guard expression is HIGH")
    }

    // execute both sides of if statement
    val _left = state2.updatePIfLeft(_test)
    val _left1 = execute(left, _left).st

    val _right1: State = right match {
      case Some(r) =>
        if (state0.toLog)
          println("} else {")
        val _right = state2.updatePIfRight(_test)
        execute(r, _right).st
      case None =>
        state2.updatePIfRight(_test)
    }

    // merge states
    _left1.mergeIf(_right1)
  }

  def whileRule(test: Expression, PPrime: List[Expression], gammaPrime: Map[Id, Security], body: Statement, state0: State, line: Int): State = {
    // WHILE rule

    //println("while rule:")
    //println("gamma':" + gammaPrime)
    //println("P':" + PPrime)
    if (state0.toLog)
      println("WHILE applying")

    // P' only contains stable variables - tested
    val PPrimeVar: Set[Id] = (PPrime flatMap {x => x.variables}).toSet
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
    val gammaGreater = for (g <- state0.gamma.keySet if (state0.gamma(g) == High && gammaPrime(g) == Low))
      yield g
    if (gammaGreater.nonEmpty) {
      throw error.WhileError(line, test, "gamma' " + gammaPrime.gammaStr + " is not greater than gamma " + state0.gamma.gammaStr + " for: " + gammaGreater.mkString(" "))
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
        throw error.ProgramError("line " + line + ": D' " + state1.D.DStr + " is not a subset of D" + state0.D.DStr + " caused by error in calculating D'")
    }

    // evaluate test which updates D
    val (_test, state2) = eval(test, state1)
    val state3 = state2.updateDGuard(_test)

    // check test is LOW with regards to P', gamma' - tested
    if (state3.security(_test, state3.P) == High) {
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
        throw error.ProgramError("line " + line + ": D' " + state1.D.DStr + " is not a subset of D'' " + state0.D.DStr)
    }

    // check gamma' is greater or equal than gamma'' for all x - tested
    val gammaPrimeGreater = for (g <- gammaPrime.keySet if state5.gamma(g) == High && gammaPrime(g) == Low)
      yield g
    if (gammaPrimeGreater.nonEmpty) {
        throw error.WhileError(line, test, "gamma' " + gammaPrime.gammaStr + " is not greater or equal than than gamma'' " +  state5.gamma.gammaStr + " for: " + gammaPrimeGreater.mkString(" "))
    }

    // check P'' is stronger than P' - tested
    if (!SMT.proveImplies(state5.P, PPrime, state0.debug)) {
      throw error.WhileError(line, test, "provided P' " + PPrime.PStr + " does not hold after loop body. P'': " + state5.P.PStr)
    }

    // state1 used here as do not keep gamma'', P'', D'' from after loop body execution
    // remove test from P'
    state1.updatePIfRight(_test)
  }


  def assignRule(lhs: Id, rhs: Expression, st0: State, line: Int): State = {
    // ASSIGN rule
    if (st0.toLog)
      println("ASSIGN applying")
    val (_rhs, st1) = eval(rhs, st0) // computes rd
    val st2 = st1.updateWritten(lhs) // computes wr
    // at this point the rd and wr sets are complete for the current line

    // calculate P_x:=e
    val PRestrict = st2.restrictP(st2.knownW)
    val t = st2.security(rhs, PRestrict)

    // if x's mode is not NoRW, ensure that e's security level is not higher than x's security level, given P_x:=e - tested
    if (!st2.noReadWrite.contains(lhs)) {
      // evalP
      val xSecurity = if (st2.highP(lhs, PRestrict)) {
        High
      } else {
        Low
      }
      if (t == High && xSecurity == Low) {
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

    // calculate P_x:=e
    val PRestrict = st2.restrictP(st2.knownW)

    // check _rhs is LOW - tested
    val t = st2.security(_rhs, PRestrict)
    if (t == High) {
      throw error.AssignCError(line, lhs, rhs, "HIGH expression assigned to control variable")
    }

    // secure_update
    val PPrime = st2.assign(lhs, _rhs) // calculate PPrime
    val PPrimeRestrict = PPrime.restrictP(st2.knownW)

    val falling = for (i <- st2.controlledBy(lhs) if (!st2.lowP(i, PRestrict)) && !st2.highP(i, PPrimeRestrict))
      yield i

    if (st0.debug) {
      println("falling: " + falling)
      println("knownW: " + st2.knownW)
    }

    // falling can only succeed if y is in gamma and maps to low

    val fallingFail = for (y <- falling -- st2.noReadWrite if !st2.knownW.contains(y) || st2.security(y, PRestrict) == High)
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

  // start application of the nonblocking rule
  def startNonBlocking(z: Id, state0: State): (Mode, State) = {
    // add z to gamma
    val state1 = state0.updateRead(z)
    val PRestrict = state1.restrictP(state1.knownW)
    val t = state1.security(z, PRestrict)
    val state2 = state1.updateGammaDomain(z, t)
    val state3 = state2.resetReadWrite()

    // make z noW
    val oldMode: Mode = if (state3.noWrite.contains(z)) {
      NoW
    } else if (state3.noReadWrite.contains(z)) {
      NoRW
    } else if (state3.readWrite.contains(z)) {
      RW
    } else {
      throw error.ProgramError(z + " does not have a mode - internal error")
    }
    val state4 = state3.setMode(z, NoW)

    // increment nonblocking depth so that the nonblocking rule will be checked while executing loop contents
    val state5 = state4.copy(nonblocking = true, nonblockingDepth = state4.nonblockingDepth + 1)

    (oldMode, state5)
  }

  // end application of the nonblocking rule for z, restoring its mode to oldMode
  def endNonBlocking(z: Id, oldMode: Mode, state0: State): State = {
    // restore original z mode
    val state1 = state0.setMode(z, oldMode)

    // remove z from gamma
    val state2 = state1.removeGamma(z)

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
