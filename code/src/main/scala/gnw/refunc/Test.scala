package gnw.refunc

import scala.util.continuations._
import gnw.refunc.ast._

import ANFAAM._

object RefuncTest {
  val mtTime = List()
  val mtEnv = Map[String, BAddr]()
  val mtStore = Store[BAddr, Storable](Map())
  import SmallStepUBStack._

  def summarizeSS(ss: Set[State]): BStore = {
    ss.map(_.bstore).foldLeft(mtStore)(_.join(_))
  }

  def summarizeVSS(vss: Set[VS]): BStore = {
    vss.map(_.store).foldLeft(mtStore)(_.join(_))
  }
  
  def basic_test(k: Int, prog: Expr, initenv: Env, initstore: BStore) {
    ANFAAM.k = k
    
    assert(SmallStepUBStack.analyze(prog,initenv, initstore) == 
           LinearSmallStepUBStack.analyze(prog, initenv, initstore))

    assert(LinearSmallStepUBStack.analyze(prog, initenv, initstore) ==
           FusedLinearSmallStepUBStack.analyze(prog,initenv, initstore))

    assert(FusedLinearSmallStepUBStack.analyze(prog, initenv, initstore) ==
           DisLinearSmallStepUBStack.analyze(prog, initenv, initstore))

    assert(SmallStepP4F.analyze(prog, initenv, initstore).map(_.bstore).foldLeft(mtStore)(_.join(_)) ==
           summarizeVSS(RefuncCPS.analyze(prog, initenv, initstore).vss))

    assert(summarizeSS(DisLinearSmallStepUBStack.analyze(prog, initenv, initstore)) ==
           summarizeVSS(RefuncCPS.analyze(prog, initenv, initstore).vss))

    assert(RefuncCPS.analyze(prog, initenv, initstore) ==
           DirectStyleDC.analyze(prog, initenv, initstore))

    assert(DirectStyleDC.analyze(prog, initenv, initstore) ==
           DirectStyleSideEff.analyze(prog, initenv, initstore))
  }

  def test_refunc_nd() {
    val ndprog = Let("a", App(Var("f"), Num(3)), Var("a"))
    val initenv = Map("f" -> BAddr("f", List()))
    val initstore = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Var("x")), Map()),
                                                                         Clos(Lam("y", Num(2)), Map()),
                                                                         Clos(Lam("z", Num(1)), Map()))))
    
    basic_test(0, ndprog, initenv, initstore)
    basic_test(1, ndprog, initenv, initstore)

    /************************************************************************/

    val initstore_nd = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), 
                                                                                            Var("t"))),
                                                                                 Map("g" -> BAddr("g", List()))),
                                                                            Clos(Lam("y", Num(2)), Map()),
                                                                            Clos(Lam("z", Num(1)), Map())),
                                                  BAddr("g", List()) -> Set(Clos(Lam("a", Num(3)), Map()),
                                                                            Clos(Lam("b", Num(4)), Map()))))
    basic_test(0, ndprog, initenv, initstore_nd)
    basic_test(1, ndprog, initenv, initstore_nd)

    /************************************************************************/

    val initstore_nd2 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), 
                                                                                            Num(5))), 
                                                                                  Map("g" -> BAddr("g", List()))),
                                                                             Clos(Lam("y", Num(2)), Map()),
                                                                             Clos(Lam("z", Num(1)), Map())
                                                                            ),
                                                  BAddr("g", List()) -> Set(Clos(Lam("a", Num(3)), Map()),
                                                                            Clos(Lam("b", Num(4)), Map()))))

    basic_test(0, ndprog, initenv, initstore_nd2)
    basic_test(1, ndprog, initenv, initstore_nd2)

    /************************************************************************/

    val id = Lam("t", Var("t"))
    val ndprog1 = Let("a", App(Var("f"), Num(3)),
                      Let("b", App(id, Var("a")),
                          Var("b")))
    val initenv2 = Map("f" -> BAddr("f", List()),
                       "g" -> BAddr("g", List()))
    val initstore2 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), Var("t"))), //4, 5
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

    basic_test(0, ndprog1, initenv2, initstore2)
    basic_test(1, ndprog1, initenv2, initstore2)

    /************************************************************************/

    val pd1 = Let("id", id,
                  Let("x", App(id, Num(1)),
                      Let("m", App(id, Num(4)),
                          Let("y", App(id, Num(2)),
                              Let("z", App(id, Num(3)),
                                  Var("x"))))))
    basic_test(0, pd1, mtEnv, mtStore)
    basic_test(1, pd1, mtEnv, mtStore)

    /************************************************************************/
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

  def main(args: Array[String]) {
    test_non_term()
    test_refunc_nd()
  }
}
