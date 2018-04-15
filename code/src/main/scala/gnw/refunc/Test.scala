package gnw.refunc

import scala.util.continuations._
import gnw.refunc.ast._

import ANFAAM._

// TODO: reorganize the tests

object RefuncTest {
  val mtTime = List()
  val mtEnv = Map[String, BAddr]()
  val mtStore = Store[BAddr, Storable](Map())
  
  def test_refunc_nd() {
    ANFAAM.k = 0
    val ndprog = Let("a", App(Var("f"), Num(3)), Var("a"))
    val initenv = Map("f" -> BAddr("f", List()))
    val initstore = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Var("x")), Map()),
                                                                         Clos(Lam("y", Num(2)), Map()),
                                                                         Clos(Lam("z", Num(1)), Map()))))

    assert(SmallStepUBStack.analyze(ndprog,initenv, initstore) == 
           LinearSmallStepUBStack.analyze(ndprog, initenv, initstore))
    assert(LinearSmallStepUBStack.analyze(ndprog, initenv, initstore) ==
           FusedLinearSmallStepUBStack.analyze(ndprog,initenv, initstore))
    assert(FusedLinearSmallStepUBStack.analyze(ndprog, initenv, initstore) ==
           DisLinearSmallStepUBStack.analyze(ndprog, initenv, initstore))
  
    return
    assert(RefuncCPSNoCacheBF.analyze(ndprog, initenv, initstore) ==
           RefuncCPSNoCache.analyze(ndprog, initenv, initstore))

    assert(DirectStyleDCNoCache.analyze(ndprog, initenv, initstore) ==
             RefuncCPSNoCache.analyze(ndprog, initenv, initstore))
    assert(DirectStyleDCNoCache.analyze(ndprog, initenv, initstore) ==
             DirectStyleDCNoCache2.analyze(ndprog, initenv, initstore))

    //assert(RefuncNoCache3.analyze(ndprog, initenv, initstore) ==
    //       Refunc.analyze(ndprog, initenv, initstore).vss)

    //assert(RefuncCPS.analyze(ndprog, initenv, initstore) ==
    //       Refunc.analyze(ndprog, initenv, initstore))

    assert(RefuncCPS.analyze(ndprog, initenv, initstore) ==
           DirectStyleSideEff.analyze(ndprog, initenv, initstore))
    
    println(RefuncCPS.analyze(ndprog, initenv, initstore).cache)
    println(DirectStyleDC.analyze(ndprog, initenv, initstore).cache)
  
    assert(RefuncCPS.analyze(ndprog, initenv, initstore) ==
           DirectStyleDC.analyze(ndprog, initenv, initstore))

    val initstore_nd = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), 
                                                                                            Var("t"))),
                                                                                 Map("g" -> BAddr("g", List()))),
                                                                            Clos(Lam("y", Num(2)), Map()),
                                                                            Clos(Lam("z", Num(1)), Map())),
                                                  BAddr("g", List()) -> Set(Clos(Lam("a", Num(3)), Map()),
                                                                            Clos(Lam("b", Num(4)), Map()))))

    assert(SmallStepUBStack.analyze(ndprog,initenv, initstore_nd) == 
      LinearSmallStepUBStack.analyze(ndprog,initenv, initstore_nd))

    assert(FusedLinearSmallStepUBStack.analyze(ndprog,initenv, initstore_nd) == 
      LinearSmallStepUBStack.analyze(ndprog,initenv, initstore_nd))

    //assert(RefuncNoCache2.analyze(ndprog, initenv, initstore_nd) ==
    //         RefuncNoCache3.analyze(ndprog, initenv, initstore_nd))
    //assert(RefuncNoCache3.analyze(ndprog, initenv, initstore_nd) ==
    //         Refunc.analyze(ndprog, initenv, initstore_nd).vss)

    //assert(RefuncCPSNoCacheBF.analyze(ndprog, initenv, initstore_nd) ==
    //         RefuncNoCache3.analyze(ndprog, initenv, initstore_nd))
    assert(RefuncCPSNoCacheBF.analyze(ndprog, initenv, initstore_nd) ==
             RefuncCPSNoCache.analyze(ndprog, initenv, initstore_nd))
    assert(DirectStyleDCNoCache.analyze(ndprog, initenv, initstore_nd) ==
             RefuncCPSNoCache.analyze(ndprog, initenv, initstore_nd))
    assert(DirectStyleDCNoCache.analyze(ndprog, initenv, initstore_nd) ==
             DirectStyleDCNoCache2.analyze(ndprog, initenv, initstore_nd))

    //println(RefuncNoCacheNoTime2.analyze(ndprog, initenv, initstore_nd))

    //assert(RefuncCPS.analyze(ndprog, initenv, initstore_nd) ==
    //         Refunc.analyze(ndprog, initenv, initstore_nd))

    assert(RefuncCPS.analyze(ndprog, initenv, initstore_nd) ==
             DirectStyleSideEff.analyze(ndprog, initenv, initstore_nd))

    assert(RefuncCPS.analyze(ndprog, initenv, initstore_nd) ==
             DirectStyleDC.analyze(ndprog, initenv, initstore_nd))

    val initstore_nd2 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), 
                                                                                            Num(5))), 
                                                                                  Map("g" -> BAddr("g", List()))),
                                                                             Clos(Lam("y", Num(2)), Map()),
                                                                             Clos(Lam("z", Num(1)), Map())
                                                                            ),
                                                  BAddr("g", List()) -> Set(Clos(Lam("a", Num(3)), Map()),
                                                                            Clos(Lam("b", Num(4)), Map()))))

    assert(SmallStepUBStack.analyze(ndprog,initenv, initstore_nd2) == 
      LinearSmallStepUBStack.analyze(ndprog,initenv, initstore_nd2))

    assert(FusedLinearSmallStepUBStack.analyze(ndprog, initenv, initstore_nd2) == 
      LinearSmallStepUBStack.analyze(ndprog, initenv, initstore_nd2)) 

    //assert(RefuncNoCache2.analyze(ndprog, initenv, initstore_nd2) ==
    //         RefuncNoCache3.analyze(ndprog, initenv, initstore_nd2))
    //println(RefuncNoCache3.analyze(ndprog, initenv, initstore_nd2))
    //assert(Refunc.analyze(ndprog, initenv, initstore_nd2).vss ==
    //         RefuncNoCache3.analyze(ndprog, initenv, initstore_nd2))
    //assert(RefuncCPSNoCacheBF.analyze(ndprog, initenv, initstore_nd2) ==
    //         RefuncNoCache3.analyze(ndprog, initenv, initstore_nd2))
    assert(RefuncCPSNoCacheBF.analyze(ndprog, initenv, initstore_nd2) ==
             RefuncCPSNoCache.analyze(ndprog, initenv, initstore_nd2))

    assert(DirectStyleDCNoCache.analyze(ndprog, initenv, initstore_nd2) ==
             RefuncCPSNoCache.analyze(ndprog, initenv, initstore_nd2))
    assert(DirectStyleDCNoCache.analyze(ndprog, initenv, initstore_nd2) ==
             DirectStyleDCNoCache2.analyze(ndprog, initenv, initstore_nd2))


    //assert(Refunc.analyze(ndprog, initenv, initstore_nd2) ==
    //       RefuncCPS.analyze(ndprog, initenv, initstore_nd2))
    assert(DirectStyleSideEff.analyze(ndprog, initenv, initstore_nd2) ==
           RefuncCPS.analyze(ndprog, initenv, initstore_nd2))

    assert(DirectStyleDC.analyze(ndprog, initenv, initstore_nd2) ==
           RefuncCPS.analyze(ndprog, initenv, initstore_nd2))
    /*
    ANFAAM.k = 1
    println(RefuncNoCache.analyze(ndprog, initenv, initstore))
    println(RefuncNoCache.analyze(ndprog, initenv, initstore))
     */

    /************************************/

    val id = Lam("t", Var("t"))
    val ndprog1 = Let("a", App(Var("f"), Num(3)),
                      Let("b", App(id, Var("a")),
                          Var("b")))
    //println(RefuncNoCacheNoTime1.analyze(ndprog1, initenv, initstore))

    /************************************/

    val initenv2 = Map("f" -> BAddr("f", List()),
                       "g" -> BAddr("g", List()))
    val initstore2 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), Var("t"))),
                                                                               Map("g" -> BAddr("g", List()))),
                                                                          Clos(Lam("y", Num(2)), Map()),
                                                                          Clos(Lam("z", Num(1)), Map()),
                                                                          Clos(Lam("x1", Let("t1", App(Var("h"), Var("x1")), Var("t1"))),
                                                                               Map("h" -> BAddr("h", List()))),
                                                                          Clos(Lam("p", Var("p")), Map())),
                                                BAddr("g", List()) -> Set(Clos(Lam("m", Num(4)), Map()),
                                                                          Clos(Lam("n", Num(5)), Map())),
                                                BAddr("h", List()) -> Set(Clos(Lam("d", Num(6)), Map()))))

    assert(SmallStepUBStack.analyze(ndprog1, initenv2, initstore2) == 
      LinearSmallStepUBStack.analyze(ndprog1, initenv2, initstore2))

    assert(FusedLinearSmallStepUBStack.analyze(ndprog1, initenv2, initstore2) == 
      LinearSmallStepUBStack.analyze(ndprog1, initenv2, initstore2))

    //assert(RefuncNoCache2.analyze(ndprog1, initenv2, initstore2) ==
    //         RefuncNoCache3.analyze(ndprog1, initenv2, initstore2))
    //assert(Refunc.analyze(ndprog1, initenv2, initstore2).vss ==
    //         RefuncNoCache3.analyze(ndprog1, initenv2, initstore2))
    //assert(RefuncCPSNoCacheBF.analyze(ndprog1, initenv2, initstore2) ==
    //         RefuncNoCache3.analyze(ndprog1, initenv2, initstore2))
    assert(RefuncCPSNoCacheBF.analyze(ndprog1, initenv2, initstore2) ==
             RefuncCPSNoCache.analyze(ndprog1, initenv2, initstore2))
    assert(DirectStyleDCNoCache.analyze(ndprog1, initenv2, initstore2) ==
             RefuncCPSNoCache.analyze(ndprog1, initenv2, initstore2))
    assert(DirectStyleDCNoCache.analyze(ndprog1, initenv2, initstore2) ==
             DirectStyleDCNoCache2.analyze(ndprog1, initenv2, initstore2))
    //assert(Refunc.analyze(ndprog1, initenv2, initstore2) ==
    //         RefuncCPS.analyze(ndprog1, initenv2, initstore2))
    assert(DirectStyleSideEff.analyze(ndprog1, initenv2, initstore2) ==
             RefuncCPS.analyze(ndprog1, initenv2, initstore2))
    assert(DirectStyleDC.analyze(ndprog1, initenv2, initstore2) ==
             RefuncCPS.analyze(ndprog1, initenv2, initstore2))
    /*
    println("------------------------")
    println(RefuncNoCacheNoTime2.analyze(ndprog1, initenv2, initstore2))
    */
    //ANFAAM.k = 0
    //println(RefuncNoCache.analyze(ndprog1, initenv2, initstore2))
    //println(Refunc.analyze(ndprog, initenv, initstore))
  }

  def test_pushdown() {
    val id = Lam("a", Var("a"))
    val pd1 = Let("id", id,
                  Let("x", App(id, Num(1)),
                      Let("m", App(id, Num(4)),
                          Let("y", App(id, Num(2)),
                              Let("z", App(id, Num(3)),
                                  Var("x"))))))
    ANFAAM.k = 0
    println(SmallStepP4F.analyze(pd1).filter(_.e == Var("x")))
    //assert(SmallStepUBStack.analyze(pd1).filter(_.e == Var("x")).head.bstore ==
    //         RefuncNoCache.analyze(pd1).head.store)
    //println(RefuncNoCache3.analyze(pd1))
  }

  def test_non_term() {
    """(letrec ([f1 (lambda (x)
                      (let ([x1 (f2 x)]) x1))]
                [f2 (lambda (y)
                      (let ([y1 (f1 y)]) y1))])
           (let ([res (f1 1)])
              res))"""
    val mutrec = Letrec(List(B("f1", Lam("x", Let("x1", App(Var("f2"), Var("x")), Var("x1")))),
                             B("f2", Lam("y", Let("y1", App(Var("f1"), Var("y")), Var("y1"))))),
                        Let("res", App(Var("f1"), Num(1)),
                            Var("res")))

    var p4fstates = SmallStepP4F.analyze(mutrec)
    var p4fstore = p4fstates.map(_.bstore).foldLeft(Store[BAddr, Storable](Map()))(_.join(_))

    //println(p4fstore) //TODO: how to get the store
    /* The final value should be empty */
    assert(DirectStyleDC.analyze(mutrec).vss == Set())
    assert(RefuncCPS.analyze(mutrec) == DirectStyleDC.analyze(mutrec))

    /************************************************************************/
    
    val ntprog = Let("a", App(Var("f"), Num(3)), Var("a"))
    val initenv = Map("f" -> BAddr("f", List()))
    val initstore = Store[BAddr, Storable](Map(BAddr("f", List()) ->
                                                 Set(Clos(Lam("x", Var("x")), Map()),
                                                     Clos(Lam("x1", Let("t1", App(Var("f"), Var("x1")), Var("t1"))),
                                                          Map("f" -> BAddr("f", List()))),
                                                     Clos(Lam("y", Num(2)), Map()),
                                                     Clos(Lam("z", Num(1)), Map()))))
    p4fstates = SmallStepP4F.analyze(ntprog, initenv, initstore)
    p4fstore = p4fstates.map(_.bstore).foldLeft(Store[BAddr, Storable](Map()))(_.join(_))
    /* The stores should be equal */
    assert(DirectStyleDC.analyze(ntprog, initenv, initstore).vss.map(_.store).foldLeft(mtStore)(_.join(_)) == p4fstore)
    assert(DirectStyleDC.analyze(ntprog, initenv, initstore).cache.outVS.map(_.store).foldLeft(mtStore)(_.join(_)) == p4fstore)
    assert(RefuncCPS.analyze(ntprog, initenv, initstore) == DirectStyleDC.analyze(ntprog, initenv, initstore))
  }

  def test_cache() {
    val initenv = Map("f" -> BAddr("f", List()))
    val initstore = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Var("x")), Map()),
                                                                         Clos(Lam("y", Var("y")), Map()))))
    val ndprog = Let("a", App(Var("f"), Num(3)), Var("a"))
    ANFAAM.k = 1

    //assert(RefuncNoCache.analyze(ndprog, initenv, initstore) ==
    //         RefuncNoCache2.analyze(ndprog, initenv, initstore))

    //assert(RefuncNoCache.analyze(ndprog, initenv, initstore) ==
    //        Refunc.analyze(ndprog, initenv, initstore).vss)

    //assert(RefuncCPS.analyze(ndprog, initenv, initstore) ==
    //         Refunc.analyze(ndprog, initenv, initstore))

    assert(RefuncCPS.analyze(ndprog, initenv, initstore) ==
             DirectStyleSideEff.analyze(ndprog, initenv, initstore))

    val id = Lam("t", Var("t"))
    val ndprog1 = Let("a", App(Var("f"), Num(3)),
                      Let("b", App(id, Var("a")),
                          Var("b")))
    val initenv1 = Map("f" -> BAddr("f", List()),
                       "g" -> BAddr("g", List()))
    val initstore1 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), Var("t"))), //4, 5
                                                                               Map("g" -> BAddr("g", List()))),
                                                                          Clos(Lam("y", Num(2)), Map()),
                                                                          Clos(Lam("z", Num(1)), Map()),
                                                                          Clos(Lam("x1", Let("t1", App(Var("h"), Var("x1")), Var("t1"))), //6, 7
                                                                               Map("h" -> BAddr("h", List()))),
                                                                          Clos(Lam("p", Var("p")), Map())),
                                                BAddr("g", List()) -> Set(Clos(Lam("m", Num(4)), Map()),
                                                                          Clos(Lam("n", Num(5)), Map())),
                                                BAddr("h", List()) -> Set(Clos(Lam("d", Num(6)), Map()),
                                                                          Clos(Lam("d", Num(7)), Map()))))

    //assert(RefuncNoCache.analyze(ndprog1, initenv1, initstore1) ==
    //         RefuncNoCache2.analyze(ndprog1, initenv1, initstore1))

    //assert(RefuncNoCache.analyze(ndprog1, initenv1, initstore1) ==
    //       Refunc.analyze(ndprog1, initenv1, initstore1).vss)

    //assert(RefuncCPS.analyze(ndprog1, initenv1, initstore1) ==
    //       Refunc.analyze(ndprog1, initenv1, initstore1))
    assert(RefuncCPS.analyze(ndprog1, initenv1, initstore1).vss ==
           RefuncCPSBF.analyze(ndprog1, initenv1, initstore1)._1)
    assert(RefuncCPS.analyze(ndprog1, initenv1, initstore1).cache ==
           RefuncCPSBF.analyze(ndprog1, initenv1, initstore1)._2)

    assert(RefuncCPS.analyze(ndprog1, initenv1, initstore1) ==
          DirectStyleSideEff.analyze(ndprog1, initenv1, initstore1))
    
    val p4fstates = SmallStepP4F.analyze(ndprog1, initenv1, initstore1)
    val finalstore = p4fstates.map(_.bstore).foldLeft(Store[BAddr, Storable](Map()))(_.join(_))

    val refuncstore = RefuncCPSBF.analyze(ndprog1, initenv1, initstore1)._1.map(_.store).foldLeft(Store[BAddr, Storable](Map()))(_.join(_))
    assert(finalstore == refuncstore)
  }

  def main(args: Array[String]) {
    test_non_term()
    //test_pushdown()
    //test_cache()
    test_refunc_nd()
  }
}
