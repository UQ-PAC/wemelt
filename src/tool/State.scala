package tool

case class State(
  gamma: Map[Variable, Boolean],
  D: Map[Variable, (Set[Variable], Set[Variable], Set[Variable], Set[Variable])], // W_w, W_r, R_w, R_r
  knownW: Set[Variable],
  knownR: Set[Variable],
  later_w: Set[Variable],
  later_r: Set[Variable],
  globals: Set[Variable],
  locals: Set[Variable],
  noReadWrite: Set[Variable],
  readWrite: Set[Variable],
  noWrite: Set[Variable],
  controls: Set[Variable],
  controlled: Set[Variable],
  idToVariable: Map[Id, Variable],
  variables: Set[Variable]) {
}

object State {
  def init(variables: Set[Variable]): State = {
    var globals: Set[Variable] = Set()
    var locals: Set[Variable] = Set()
    var noReadWrite: Set[Variable] = Set()
    var readWrite: Set[Variable] = Set()
    var noWrite: Set[Variable] = Set()
    var controls: Set[Variable] = Set()
    var controlled: Set[Variable] = Set()
    var idToVariable: Map[Id, Variable] = Map()

    for (v <- variables) {
      idToVariable += (v.name -> v)
    }

    for (v <- variables) {
      v.mode.mode match {
        case "Reg" =>
          locals += v
          noReadWrite += v
        case "NoRW" =>
          globals += v
          noReadWrite += v
        case "NoW" =>
          globals += v
          noWrite += v
        case "RW" =>
          globals += v
          readWrite += v
      }
      val controlling: Set[Id] = v.pred.pred.getVariables
      if (controlling.nonEmpty) {
        if (controls.contains(v)) {
          throw error.InvalidControlVariables(v.name + " is both controlled and a control variable")
        }
        controlled += v
      }
      for (i <- controlling) {
        val variable: Variable = idToVariable(i)
        println(v)
        println(variable)
        variable.controlled += v
        controls += variable
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
      println(v.controlled)
    }

    // init D - every variable maps to Var

    // init gamma

    //

    State(
      gamma = Map(),
      D = Map(),
      knownW = Set(),
      knownR = Set(),
      later_w = Set(),
      later_r = Set(),
      globals = globals,
      locals = locals,
      noReadWrite = noReadWrite,
      readWrite = readWrite,
      noWrite = noWrite,
      controls = controls,
      controlled = controlled,
      idToVariable = idToVariable,
      variables = variables
    )
  }
}