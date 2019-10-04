package tool

import java.io.FileReader
import collection.JavaConverters._

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

  def parse(file: String): (List[Statement], Set[VarDef]) = {
    val reader = new FileReader(file)
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val variables = new java.util.HashSet[VarDef]
    parser.variables = variables

    val result = parser.parse(scanner)

    //result
    val globals: List[Statement] = result.asInstanceOf[java.util.ArrayList[Statement]].asScala.toList

    val variables2: Set[VarDef] = variables.asInstanceOf[java.util.HashSet[VarDef]].asScala.toSet
    println(globals)
    println(variables2)
    (globals, variables2)
  }

  def init(variables: Set[VarDef]) = {
    var globals: Set[VarDef] = Set()
    var locals: Set[VarDef] = Set()
    var no_read_write: Set[VarDef] = Set()
    var read_write: Set[VarDef] = Set()
    var no_write: Set[VarDef] = Set()

    for (v <- variables) {
      v.mode.mode match {
        case "Reg" =>
          locals += v
          no_read_write += v
        case "NoRW" =>
          globals += v
          no_read_write += v
        case "NoW" =>
          globals += v
          no_write += v
        case "RW" =>
          globals += v
          read_write += v
      }

    }
    println(globals)
    println(locals)
  }

}
