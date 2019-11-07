package tool

import java.io.FileReader
import tool.error._

object Tool {

  def main(args: Array[String]): Unit = {
    var toLog: Boolean = false
    var debug: Boolean = false

    if (args.isEmpty) {
      println("usage: ./armlogictool.sh file1 file2...")
    } else {
      for (file <- args) file match {
        case "-v" =>
          toLog = true
        case "-d" =>
          debug = true
          toLog = true
        case _ =>
          val start = System.currentTimeMillis()
          try {
            println(file)
            val res = parse(file)
            val variables = res.variables
            val statements = res.statements
            val P_0 = res.P_0
            val gamma_0 = res.gamma_0
            if (debug) {
              println(statements)
              println(variables)
              println(P_0)
              println(gamma_0)
            }
            val state0: State = State.init(variables, P_0, gamma_0, toLog, debug)
            Exec.execute(statements, state0)
            val end = System.currentTimeMillis()
            val time = end - start
            println("no errors found")
            if (time >= 1000) {
              println("time: " + (time / 1000) + "s")
            } else {
              println("time: " + time + "ms")
            }
          } catch {
            case e: java.io.FileNotFoundException =>
              println("file does not exist")
            case e: InvalidProgram =>
              val end = System.currentTimeMillis()
              val time = end - start
              println("invalid input file: " + e)
              if (time >= 1000) {
                println("time: " + (time / 1000) + "s")
              } else {
                println("time: " + time + "ms")
              }
            case e: ProgramError =>
              val end = System.currentTimeMillis()
              val time = end - start
              println("internal error: " + e)
              if (time >= 1000) {
                println("time: " + (time / 1000) + "s")
              } else {
                println("time: " + time + "ms")
              }
            case e: Z3Error =>
              val end = System.currentTimeMillis()
              val time = end - start
              println("Z3 Failed: " + e)
              if (time >= 1000) {
                println("time: " + (time / 1000) + "s")
              } else {
                println("time: " + time + "ms")
              }
            case e: WhileError =>
              val end = System.currentTimeMillis()
              val time = end - start
              println(e)
              if (time >= 1000) {
                println("time: " + (time / 1000) + "s")
              } else {
                println("time: " + time + "ms")
              }
            case e: IfError =>
              val end = System.currentTimeMillis()
              val time = end - start
              println(e)
              if (time >= 1000) {
                println("time: " + (time / 1000) + "s")
              } else {
                println("time: " + time + "ms")
              }
            case e: AssignCError =>
              val end = System.currentTimeMillis()
              val time = end - start
              println(e)
              if (time >= 1000) {
                println("time: " + (time / 1000) + "s")
              } else {
                println("time: " + time + "ms")
              }
            case e: AssignError =>
              val end = System.currentTimeMillis()
              val time = end - start
              println(e)
              if (time >= 1000) {
                println("time: " + (time / 1000) + "s")
              } else {
                println("time: " + time + "ms")
              }
          }
      }
    }
  }

  def parse(file: String): Global = {
    val reader = new FileReader(file)
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val result = parser.parse(scanner).asInstanceOf[Global]

    result
  }



}
