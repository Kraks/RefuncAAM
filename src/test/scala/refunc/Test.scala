package refunc

import org.scalatest._
import refunc.ast._
import ANFAAM._

/**
 * Description:
 * 
 * class RefuncTest provides some auxiliary functions;
 * class TDProgTest contains test cases that programs are terminated and deterministic;
 * class TNDProgTest contains test cases that programs are terminated but non-deterministic;
 * class NDProgTest contains test cases that programs are non-terminated;
 * class NTTNDProgTest contains test cases that programs are non-deterministic, but some branches
 * are terminated, while some other branches are not.
 *
 * For convenience, we test non-deterministic cases through passing an initial store that maps
 * an address to multiple target closures.
 */

trait RefuncTest extends FunSuite {
  final val K = 3 /* K-call-site context sensitivity */
  val bot = Set()

  def summarize(ss: Set[BStore]): BStore = { ss.foldLeft(mtStore)(_.join(_)) }
  def summarizeState(ss: Set[ANFAAM.State]): BStore = { summarize(ss.map(_.bstore)) }
  def summarizeVSS(vss: Set[VS]): BStore = { summarize(vss.map(_.store)) }
  def summarizeUBState(ss: Set[SmallStepUBStack.State]): BStore = {
    summarize(ss.map(_.bstore)) 
  }
  
  val description = "None"

  /* Assertions for TDProgTest, TNDProgTest and NTTNDProgTest. */
  def runTest(id: Int, prog: Expr, initenv: Env, initstore: BStore) {
    for (k <- 0 to K) {
      ANFAAM.k = k
      test(s"Testing $description case $id under k=$k") {
        /* The result analyzed by the small-step AAM with unbounded stack (SmallStepUBStack)
         * should have the same result analyzed by its linearized counterpart 
         * (LinearSmallStepUBStack). */
        assert(SmallStepUBStack.analyze(prog,initenv, initstore) == 
               LinearSmallStepUBStack.analyze(prog, initenv, initstore))
        
        /* The result analyzed by the linearized small-step AAM with unbounded stakc
         * (LinearSmallStepUBStack) should have the same result analyzed by its
         * fused counterpart (FusedLinearSmallStepUBStack). */
        assert(LinearSmallStepUBStack.analyze(prog, initenv, initstore) ==
               FusedLinearSmallStepUBStack.analyze(prog,initenv, initstore))

        /* The result analyzed by the fused linear small-step AAM with unbounded stack
         * (FusedLinearSmallStepUBStack) should have the same result analyzed by its
         * disentangled counterpart (DisLinearSmallStepUBStack). */
        assert(FusedLinearSmallStepUBStack.analyze(prog, initenv, initstore) ==
               DisLinearSmallStepUBStack.analyze(prog, initenv, initstore))
        
        /* Since the disentangled linearized small-step AAM with unbounded stack 
         * (DisLinearSmallStepUBStack) returns a set of state, while the refunctionalized 
         * abstract interpreter (RefuncCPS) returns a set of ValueStore (VS), to state their 
         * correspondence, we test the summarized store of these two sets. The store contains 
         * all the value flow information, which is the result we care about in term of 
         * control-flow analysis.  
         * Later, we also apply this approach when testing the result of RefuncCPS/DirectStyleDC 
         * interpreter against with AAM with P4F allocator.
         * 
         * The summarized store analyzed by DisLinearSmallStepUBStack machine should be
         * the same with the one analyzed by RefuncCPS abstract interpreter.
         */
        assert(summarizeUBState(DisLinearSmallStepUBStack.analyze(prog, initenv, initstore)) ==
               summarizeVSS(RefuncCPS.analyze(prog, initenv, initstore).vss))
      
        /* The result analyzed by the refunctionalized abstract interpreter written in CPS
         * (RefuncCPS) should have the same result analyzed by the direct-style abstract 
         * interpreter using delimited continuations (DirectStyleDC). */
        assert(RefuncCPS.analyze(prog, initenv, initstore) ==
               DirectStyleDC.analyze(prog, initenv, initstore))

        /* The result analyzed by the direct-style abstract interpreter using delimited 
         * continuations (DirectStyleDC) should have the same result analyzed by the abstract 
         * interpreter written with side effects (DirectStyleSideEff). */
        assert(DirectStyleDC.analyze(prog, initenv, initstore) ==
               DirectStyleSideEff.analyze(prog, initenv, initstore))

        /* The summarized store analyzed by the small-step AAM with P4F allocator (SmallStepP4F)
         * should be the same with the one analyzed by refunctionalized abstract interpreter 
         * written in CPS (RefuncCPS). */
        assert(summarizeState(SmallStepP4F.analyze(prog, initenv, initstore)) ==
               summarizeVSS(RefuncCPS.analyze(prog, initenv, initstore).vss))

        /* The summarized store analyzed by the small-step AAM with P4F allocator (SmallStepP4F)
         * should be the same with the one analyzed by direct-style abstract interpreter using 
         * delimited continuations (DirectStyleDC). */
        assert(summarizeState(SmallStepP4F.analyze(prog, initenv, initstore)) ==
               summarizeVSS(DirectStyleDC.analyze(prog, initenv, initstore).vss))

        /* The summarized store analyzed by the small-step AAM with P4F allocator (SmallStepP4F)
         * should be the same with the one analyzed by direct-style abstract interpreter written
         * with side effects (DirectStyleSideEff). */
        assert(summarizeState(SmallStepP4F.analyze(prog, initenv, initstore)) ==
               summarizeVSS(DirectStyleSideEff.analyze(prog, initenv, initstore).vss))
      }
    }
  }
  
  /* Common expressions */
  val id = Lam("t", Var("t"))
}

/** 
 *  Test terminated deterministic programs.
 */
class TDProgTest extends RefuncTest {
  override val description = "terminated deterministic"

  /** 
   * test case 1
   * exp: 
   * init env: ∅
   * init store: ∅ 
   */

  /** 
   * test case 2
   * exp:
   * init env: ∅
   * init store: ∅ 
   */

  /**
   * test case 3
   * exp: (let ([id (lambda (t) t)])
   *        (let ([x (id 1)])
   *          (let ([m (id 4)])
   *            (let ([y (id 2)])
   *              (let ([z (id 3)])
   *                x)))))
   * init env: ∅
   * init store: ∅ 
   */
  val exp3 = Let("id", id, 
             Let("x", App(id, Num(1)), 
             Let("m", App(id, Num(4)), 
             Let("y", App(id, Num(2)), 
             Let("z", App(id, Num(3)), 
               Var("x"))))))
  runTest(3, exp3, mtEnv, mtStore)
}

/** 
 *  Test terminated non-deterministic programs.
 */
class TNDProgTest extends RefuncTest {
  override val description = "terminated non-deterministic"

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
  runTest(1, exp1, exp1_env1, exp1_ndstore1) 

  /**
   * test case 2
   * exp: (let ([a (f 3)]) a)
   * init env: {f → BAddr(f, [])}
   * init store: exp1_ndstore2
   */
  val exp1_ndstore2 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), Var("t"))),
                                                                                Map("g" -> BAddr("g", List()))),
                                                                           Clos(Lam("y", Num(2)), Map()),
                                                                           Clos(Lam("z", Num(1)), Map())),
                                                 BAddr("g", List()) -> Set(Clos(Lam("a", Num(3)), Map()),
                                                                           Clos(Lam("b", Num(4)), Map()))))
  runTest(2, exp1, exp1_env1, exp1_ndstore2)

  /**
   * test case 3
   * exp: (let ([a (f 3)]) a)
   * init env: {f → BAddr(f, [])}
   * init store: exp1_ndstore3
   */
  val exp1_ndstore3 = Store[BAddr, Storable](Map(BAddr("f", List()) -> Set(Clos(Lam("x", Let("t", App(Var("g"), Var("x")), Num(5))), 
                                                                                Map("g" -> BAddr("g", List()))),
                                                                           Clos(Lam("y", Num(2)), Map()),
                                                                           Clos(Lam("z", Num(1)), Map())),
                                                 BAddr("g", List()) -> Set(Clos(Lam("a", Num(3)), Map()),
                                                                           Clos(Lam("b", Num(4)), Map()))))
  runTest(3, exp1, exp1_env1, exp1_ndstore3)

  /**
   * test case 4
   * exp: (let ([a (f 3)])
   *        (let ([b (id a)])
   *          b))
   * init env: {f → BAddr(f, []), g → BAddr(g, [])}
   * init store: 
   */
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
  runTest(4, exp2, exp2_env1, exp2_ndstore1)
}

/** 
 *  Test non-terminated programs.
 */
class NDProgTest extends RefuncTest {
  override val description = "non-terminated"
  
  override def runTest(id: Int, prog: Expr, initenv: Env, initstore: BStore) {
    for (k <- 0 to K) {
      test(s"Testing $description case $id under k=$k") {
        /* The expecting ValueStore is ⊥, since the program is non-terminated and 
         * no value is produced. 
         *
         * Other intermediate forms of abstract interpreters in our transformations (LinearSmallStepUBStack, 
         * FusedLinearSmallStepUBStack and DisLinearSmallStepUBStack) lack proper caching mechanisms, 
         * running them on non-terminated programs would cause the abstract interpreter to diverge.
         * So we don't test them here. */
        assert(RefuncCPS.analyze(prog, initenv, initstore).vss == bot)
        assert(DirectStyleDC.analyze(prog, initenv, initstore).vss == bot)
        assert(RefuncCPS.analyze(prog, initenv, initstore) == DirectStyleDC.analyze(prog, initenv, initstore))

        /* The result analyzed by the direct-style abstract interpreter using delimited 
         * continuations (DirectStyleDC) should have the same result analyzed by the 
         * abstract interpreter written with side effects (DirectStyleSideEff). */
        assert(DirectStyleDC.analyze(prog, initenv, initstore) == DirectStyleSideEff.analyze(prog, initenv, initstore))
      }
    }
  }

  /**
   * test case 1
   * exp: (letrec ([f1 (lambda (x) (let ([x1 (f2 x)]) x1))]
                   [f2 (lambda (y) (let ([y1 (f1 y)]) y1))])
             (let ([res (f1 1)])
                res))
   * init env: ∅
   * init store: ∅ 
   */
  val exp1 = Letrec(List(B("f1", Lam("x", Let("x1", App(Var("f2"), Var("x")), Var("x1")))),
                         B("f2", Lam("y", Let("y1", App(Var("f1"), Var("y")), Var("y1"))))),
                    Let("res", App(Var("f1"), Num(1)),
                        Var("res")))
  runTest(1, exp1, mtEnv, mtStore)

  /**
   * test case 2
   * exp: (letrec ([f1 (lambda (x) (let ([x1 (f2 x)]) x1))]
                   [f2 (lambda (y) (let ([y1 (f1 y)]) y1))])
             (let ([res (f2 1)])
                res))
   * init env: ∅
   * init store: ∅ 
   */
  val exp2 = Letrec(List(B("f1", Lam("x", Let("x1", App(Var("f2"), Var("x")), Var("x1")))),
                         B("f2", Lam("y", Let("y1", App(Var("f1"), Var("y")), Var("y1"))))),
                    Let("res", App(Var("f2"), Num(1)),
                        Var("res")))
  runTest(2, exp2, mtEnv, mtStore)
}

/**
 * Test mixing terminated/non-terminated and non-deterministic programs.
 */
class NTTNDProgTest extends RefuncTest {
  override val description = "mixing terminated/non-terminated and non-deterministic"

  def runTest1(id: Int, prog: Expr, initenv: Env, initstore: BStore) {
    for (k <- 0 to K) {
      ANFAAM.k = k
      test(s"Testing $description case $id under k=$k") {
        val p4fstore = summarizeState(SmallStepP4F.analyze(prog, initenv, initstore))
        /* For a non-deterministic program that some branches are non-terminated, but the others
         * are terminated, here we state the refunctionalized abstract interpreter (RefuncCPS)
         * and direct-style abstract interpreter using delimited continuations (DirectStyleDC)
         * produce correct result (against with P4F) for the partial branches. 
         *
         * Other intermediate forms of abstract interpreters in our transformations (LinearSmallStepUBStack, 
         * FusedLinearSmallStepUBStack and DisLinearSmallStepUBStack) lack proper caching mechanisms, 
         * running them on non-terminated programs would cause the abstract interpreter to diverge.
         * So we don't test them here. */
        assert(summarizeVSS(RefuncCPS.analyze(prog, initenv, initstore).vss) == p4fstore)
        assert(summarizeVSS(DirectStyleDC.analyze(prog, initenv, initstore).vss) == p4fstore)
        assert(summarizeVSS(DirectStyleSideEff.analyze(prog, initenv, initstore).vss) == p4fstore)
        
        /* The summarized stores extracted from the ValueStore of the cache also preserve the
         * equivalence comparing with P4F. */
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.outVS.map(_.store).foldLeft(mtStore)(_.join(_)) == p4fstore)
        assert(DirectStyleDC.analyze(prog, initenv, initstore).cache.outVS.map(_.store).foldLeft(mtStore)(_.join(_)) == p4fstore)

        /*
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.in.map.size == DirectStyleDC.analyze(prog, initenv, initstore).cache.in.map.size)
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.out.map.size == DirectStyleDC.analyze(prog, initenv, initstore).cache.out.map.size)
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.inVS == DirectStyleDC.analyze(prog, initenv, initstore).cache.inVS)
        assert(RefuncCPS.analyze(prog, initenv, initstore).cache.outVS == DirectStyleDC.analyze(prog, initenv, initstore).cache.outVS)
        */
      }
    }
  }

  /**
   * test case 1
   * exp: (let ([a (f 3)]) a)
   * init env: exp1_env1
   * init store: exp1_store1
   */
  val exp1 = Let("a", App(Var("f"), Num(3)), Var("a"))
  val exp1_env1 = Map("f" -> BAddr("f", List()))
  val exp1_store1 = Store[BAddr, Storable](Map(BAddr("f", List()) ->
                                               Set(Clos(Lam("x", Var("x")), Map()),
                                                   Clos(Lam("x1", Let("t1", App(Var("f"), Var("x1")), Var("t1"))),
                                                        Map("f" -> BAddr("f", List()))),
                                                   Clos(Lam("y", Num(2)), Map()),
                                                   Clos(Lam("z", Num(1)), Map()))))
  runTest1(1, exp1, exp1_env1, exp1_store1)
}
