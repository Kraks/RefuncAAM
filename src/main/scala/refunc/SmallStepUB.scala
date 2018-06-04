package refunc

import scala.util.continuations._
import refunc.ast._
import ANFAAM._

object SmallStepUBStack {
  case class State(e: Expr, env: Env, bstore: BStore, konts: List[Frame], time: Time)

  def tick(s: State): Time = (s.e::s.time).take(k)

  def inject(e: Expr, env: Env = Map(), bstore: Store[BAddr, Storable] = Store[BAddr, Storable](Map())): State =
    State(e, env, bstore, List(), List())

  def step(s: State): List[State] = {
    val new_time = tick(s)
    s match {
      case State(Let(x, ae, e), env, bstore, konts, time) if isAtomic(ae) =>
        val baddr = allocBind(x, new_time)
        val new_env = env + (x -> baddr)
        val new_store = bstore.update(baddr, atomicEval(ae, env, bstore))
        List(State(e, new_env, new_store, konts, new_time))

      case State(Letrec(bds, body), env, bstore, konts, time) =>
        val new_env = bds.foldLeft(env)((accenv: Env, bd: B) => 
          accenv + (bd.x -> allocBind(bd.x, new_time)))
        val newBStore = bds.foldLeft(bstore)((accbst: BStore, bd: B) => 
          accbst.update(allocBind(bd.x, new_time), atomicEval(bd.e, new_env, accbst)))
        List(State(body, new_env, newBStore, konts, time))

      case State(Let(x, App(f, ae), e), env, bstore, konts, time) =>
        for (Clos(Lam(v, body), c_env) <- atomicEval(f, env, bstore).toList) yield {
          val frame = Frame(x, e, env)
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = bstore.update(baddr, atomicEval(ae, env, bstore))
          State(body, new_env, new_store, frame::konts, new_time)
        }

      case State(ae, env, bstore, konts, time) if isAtomic(ae) =>
        konts match {
          case Nil => List()
          case Frame(x, e, f_env)::konts =>
            val baddr = allocBind(x, new_time)
            val new_env = f_env + (x -> baddr)
            val new_store = bstore.update(baddr, atomicEval(ae, env, bstore))
            List(State(e, new_env, new_store, konts, new_time))
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
