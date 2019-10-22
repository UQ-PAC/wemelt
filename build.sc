import mill._
import mill.scalalib._

object tool extends ScalaModule {
    def scalaVersion = "2.12.8"
    def mainClass = Some("tool.Tool")
    def unmanagedClasspath = T {
        if (!ammonite.ops.exists(millSourcePath / "lib")) Agg()
        else Agg.from(ammonite.ops.ls(millSourcePath / "lib").map(PathRef(_)))
    }
}
