package refunc

import scala.util.continuations._
import refunc.ast._

import ANFAAM._

object SmallStepP4F {
  def allocKont(tgtExpr: Expr, tgtEnv: Env, tgtStore: BStore, time: Time): KAddr = P4FContAddr(tgtExpr, tgtEnv)

  def step(s: State): List[State] = {
    val new_time = tick(s)
    s match {
      case State(Let(x, ae, e), env, bstore, kstore, kaddr, time) if isAtomic(ae) =>
        val baddr = allocBind(x, new_time)
        val new_env = env + (x -> baddr)
        val newBStore = bstore.update(baddr, atomicEval(ae, env, bstore))
        List(State(e, new_env, newBStore, kstore, kaddr, new_time))

      case State(Letrec(bds, body), env, bstore, kstore, kaddr, time) =>
        val new_env = bds.foldLeft(env)((accenv: Env, bd: B) => 
          accenv + (bd.x -> allocBind(bd.x, new_time)))
        val newBStore = bds.foldLeft(bstore)((accbst: BStore, bd: B) =>
          accbst.update(allocBind(bd.x, new_time), atomicEval(bd.e, new_env, accbst)))
        List(State(body, new_env, newBStore, kstore, kaddr, time))

      case State(Let(x, App(f, ae), e), env, bstore, kstore, kaddr, time) =>
        for (Clos(Lam(v, body), c_env) <- atomicEval(f, env, bstore).toList) yield {
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val newBStore = bstore.update(baddr, atomicEval(ae, env, bstore))
          val newKAddr = allocKont(body, c_env, newBStore, new_time)
          val newKStore = kstore.update(newKAddr, Cont(Frame(x, e, env), kaddr))
          State(body, new_env, newBStore, newKStore, newKAddr, new_time)
        }

      case State(ae, env, bstore, kstore, kaddr, time) if isAtomic(ae)=>
        for (Cont(Frame(x, e, f_env), f_kaddr) <- kstore(kaddr).toList) yield {
          val baddr = allocBind(x, new_time)
          val new_env = f_env + (x -> baddr)
          val new_store = bstore.update(baddr, atomicEval(ae, env, bstore))
          State(e, new_env, new_store, kstore, f_kaddr, new_time)
        }
    }
  }

  def drive(todo: List[State], seen: Set[State]): Set[State] = todo match {
    case Nil => seen
    case hd::tl if seen.contains(hd) => drive(tl, seen)
    case hd::tl => drive(step(hd) ++ tl, seen + hd)
  }

  def analyze(e: Expr): Set[State] = drive(List(inject(e)), Set())

  def analyze(e: Expr, env: Env, bstore: BStore): Set[State] = drive(List(inject(e, env, bstore)), Set())
}
