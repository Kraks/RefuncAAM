package refunc

import ast._
import ANFAAM._

object RefuncAAM {
  def main(args: Array[String]) {
    println("Artifact of \"Refunctionalization of Abstract Abstract Machines\"")
    println("To run test:")
    println("  sbt test")

  val prog = Let("a", App(Var("f"), Num(3)), Var("a"))
  val initenv = Map("f" -> BAddr("f", List()))
  val initstore = Store[BAddr, Storable](Map(BAddr("f", List()) ->
                                               Set(Clos(Lam("x", Var("x")), Map()),
                                                   Clos(Lam("x1", Let("t1", App(Var("f"), Var("x1")), Var("t1"))),
                                                        Map("f" -> BAddr("f", List()))),
                                                   Clos(Lam("y", Num(2)), Map()),
                                                   Clos(Lam("z", Num(1)), Map()))))
  ANFAAM.k = 0
      println(DirectStyleDC.analyze(prog, initenv, initstore).cache.in.map.size)
      println(RefuncCPS.analyze(prog, initenv, initstore).cache.in.map.size)
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.in.map.size == DirectStyleDC.analyze(prog, initenv, initstore).cache.in.map.size)
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.out.map.size == DirectStyleDC.analyze(prog, initenv, initstore).cache.out.map.size)
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.inVS == DirectStyleDC.analyze(prog, initenv, initstore).cache.inVS)
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.outVS == DirectStyleDC.analyze(prog, initenv, initstore).cache.outVS)
  }
}
