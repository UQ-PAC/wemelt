package tool

import java.io.FileReader
import collection.JavaConverters._

object error {

  abstract class Error extends Exception {
    def info: Seq[Any]

    override def toString = info.mkString(" ")
  }

  case class InvalidControlVariables(info: Any*) extends Error

}

object Tool {

  def main(args: Array[String]): Unit = {
    if (args.isEmpty) {

    } else {
      for (file <- args) {
        Console.out.println(file)
        val (statements, variables) = parse(file)
        init(variables)
      }
    }

  }

  def parse(file: String): (List[Statement], Set[Variable]) = {
    val reader = new FileReader(file)
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val variables = new java.util.HashSet[Variable]
    parser.variables = variables

    val result = parser.parse(scanner)

    //result
    val globals: List[Statement] = result.asInstanceOf[java.util.ArrayList[Statement]].asScala.toList

    val variables2: Set[Variable] = variables.asInstanceOf[java.util.HashSet[Variable]].asScala.toSet
    println(globals)
    println(variables2)
    (globals, variables2)
  }

  def init(variables: Set[Variable]) = {
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
          throw error.InvalidControlVariables(v.name + "is both controlled and a control variable")
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
  }

}
