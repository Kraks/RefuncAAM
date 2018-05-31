package refunc

import org.scalatest._
import refunc.ast._
import ANFAAM._

trait RefuncTest {
  val bot = Set()

  def summarize(ss: Set[BStore]): BStore = { ss.foldLeft(mtStore)(_.join(_)) }
  def summarizeState(ss: Set[ANFAAM.State]): BStore = { summarize(ss.map(_.bstore)) }
  def summarizeVSS(vss: Set[VS]): BStore = { summarize(vss.map(_.store)) }
  def summarizeUBState(ss: Set[SmallStepUBStack.State]): BStore = { 
    summarize(ss.map(_.bstore)) 
  }

  def basic_test(k: Int, prog: Expr, initenv: Env, initstore: BStore) {
    ANFAAM.k = k
    
    assert(SmallStepUBStack.analyze(prog,initenv, initstore) == 
           LinearSmallStepUBStack.analyze(prog, initenv, initstore))

    assert(LinearSmallStepUBStack.analyze(prog, initenv, initstore) ==
           FusedLinearSmallStepUBStack.analyze(prog,initenv, initstore))

    assert(FusedLinearSmallStepUBStack.analyze(prog, initenv, initstore) ==
           DisLinearSmallStepUBStack.analyze(prog, initenv, initstore))

    assert(summarizeUBState(DisLinearSmallStepUBStack.analyze(prog, initenv, initstore)) ==
           summarizeVSS(RefuncCPS.analyze(prog, initenv, initstore).vss))

    assert(RefuncCPS.analyze(prog, initenv, initstore) ==
           DirectStyleDC.analyze(prog, initenv, initstore))

    assert(DirectStyleDC.analyze(prog, initenv, initstore) ==
           DirectStyleSideEff.analyze(prog, initenv, initstore))

    /* The refunctionalized abstract interpreter in CPS has the same 
     * summarized store with small-step AAM with P4F allocator. */
    assert(summarizeState(SmallStepP4F.analyze(prog, initenv, initstore)) ==
           summarizeVSS(RefuncCPS.analyze(prog, initenv, initstore).vss))

    /* The refunctionalized abstract interpreter using delimited continuations
     * has the same summarized store with small-step AAM with P4F allocator. */
    assert(summarizeState(SmallStepP4F.analyze(prog, initenv, initstore)) ==
           summarizeVSS(DirectStyleDC.analyze(prog, initenv, initstore).vss))
  }
}

/** 
 *  Test terminated nondeterministic programs.
 */
class NDProgTest extends FunSuite with RefuncTest {
  /**
   * test case 1
   * exp: (let ([a (f 3)]) a)
   * init env: {f → BAddr(f, [])}
   * init store: {BAddr(f, []) → {<(λ (x) x), {}>, <(λ (y) 2), {}>, <(λ (z) 1), {}>}}
   */
  val exp1 = Let("a", App(Var("f"), Num(3)), Var("a"))
  val exp1_env1 = Map("f" -> BAddr("f", List()))
  val exp1_ndstore1 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Var("x")), Map()),
                                                                    Clos(Lam("y", Num(2)), Map()),
                                                                    Clos(Lam("z", Num(1)), Map()))))

  /**
   * test case 2
   * exp: (let ([a (f 3)]) a)
   * init env: {f → BAddr(f, [])}
   * init store:  
   */
  val exp1_ndstore2 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), Var("t"))),
                                                                           Map("g" -> BAddr("g", List()))),
                                                                      Clos(Lam("y", Num(2)), Map()),
                                                                      Clos(Lam("z", Num(1)), Map())),
                                            BAddr("g", List()) -> Set(Clos(Lam("a", Num(3)), Map()),
                                                                      Clos(Lam("b", Num(4)), Map()))))

  /**
   * test case 3
   * exp: (let ([a (f 3)]) a)
   * init env: {f → BAddr(f, [])}
   * init store:
   */
  val exp1_ndstore3 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), Num(5))), 
                                                                           Map("g" -> BAddr("g", List()))),
                                                                      Clos(Lam("y", Num(2)), Map()),
                                                                      Clos(Lam("z", Num(1)), Map())),
                                            BAddr("g", List()) -> Set(Clos(Lam("a", Num(3)), Map()),
                                                                      Clos(Lam("b", Num(4)), Map()))))

  /**
   * test case 4
   * exp: 
   * init env:
   * init store:
   */
  val id = Lam("t", Var("t"))
  val exp2 = Let("a", App(Var("f"), Num(3)),
                    Let("b", App(id, Var("a")),
                        Var("b")))
  val exp2_env1 = Map("f" -> BAddr("f", List()),
                     "g" -> BAddr("g", List()))
  val exp2_ndstore1 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), Var("t"))), //4, 5
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
    
  /**
   * test case 5
   * exp: (let ([id (λ (x) x)])
   *        (let ([x (id 1)])
   *          (let ([m (id 4)])
   *            (let ([y (id 2)])
   *              (let ([z (id 3)])
   *                x)))))
   * init env:
   * init store:
   */
  val exp3 = Let("id", id, Let("x", App(id, Num(1)), Let("m", App(id, Num(4)), Let("y", App(id, Num(2)), Let("z", App(id, Num(3)), Var("x"))))))
  
  /*******************Testing Start*******************/

  val K = 3
  for (k <- 0 to K) {
    test(s"Testing terminated nondeterministic program 1 under k=$k") {
      basic_test(k, exp1, exp1_env1, exp1_ndstore1) 
    }
    test(s"Testing terminated nondeterministic program 2 under k=$k") {
      basic_test(k, exp1, exp1_env1, exp1_ndstore2)
    }
    test(s"Testing terminated nondeterministic program 3 under k=$k") {
      basic_test(k, exp1, exp1_env1, exp1_ndstore3)
    }
    test(s"Testing terminated nondeterministic program 4 under k=$k") {
      basic_test(k, exp2, exp2_env1, exp2_ndstore1)
    }
    test(s"Testing terminated nondeterministic program 5 under k=$k") {
      basic_test(k, exp3, mtEnv, mtStore)
    }
  }
}

/** 
 *  Test non-terminated nondeterministic programs.
 */
class NTNDProgTest extends FunSuite with RefuncTest {
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

    /* The final value should be empty */
    assert(DirectStyleDC.analyze(mutrec).vss == bot)
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
}
