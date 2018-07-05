package refunc.plainlam

import scala.util.continuations._
import refunc.ast._
import refunc.ANFAAM._
import refunc.plainlam.DSAAM._

/* Abstract abstract machine with P4F allocator for plain lambda-calculus. */
object AAMUB {
  import DSAAM._

  def step(s: State): List[State] = {
    val new_time = s.tick
    s match {
      case State(Num(_), env, store, konts, time) =>
        List(State(NumV, env, store, konts, new_time))

      case State(Var(x), env, store, konts, time) =>
        for (v <- atomicEval(Var(x), env, store).toList) yield v match {
          case NumV => State(NumV, env, store, konts, new_time)
          case Clos(lam, c_env) => State(lam, c_env, store, konts, new_time)
        }

      case State(App(e1, e2), env, store, konts, time) =>
        List(State(e1, env, store, Ar(e2, env)::konts, new_time))

      case State(If0(cnd, thn, els), env, store, konts, time) =>
        List(State(cnd, env, store, Br(thn, els, env)::konts, new_time))

      case State(v, env, store, konts, time) if isValue(v)=>
        konts match {
          case Fn(Lam(x, body), c_env)::ks =>
            val baddr = allocBind(x, new_time)
            val new_env = c_env + (x -> baddr)
            val new_store = store.update(baddr, atomicEval(v, env, store))
            List(State(body, new_env, new_store, ks, new_time))
          case Ar(arg, arg_env)::ks if v.isInstanceOf[Lam] =>
            List(State(arg, arg_env, store, Fn(v, env)::ks, new_time))
          case Br(thn, els, br_env)::ks if v == NumV =>
            List(State(thn, br_env, store, ks, new_time),
                 State(els, br_env, store, ks, new_time))
          case _ => List() // including cases of type error, or spurious flows
        }
    }
  }

  def drive(todo: List[State], seen: Set[State]): Set[State] = todo match {
    case Nil => seen
    case hd::tl if seen.contains(hd) => drive(tl, seen)
    case hd::tl => drive(step(hd).toList ++ tl, seen + hd)
  }

  def analyze(e: Expr): Set[State] = drive(List(inject(e)), Set())

  def analyze(e: Expr, env: Env, bstore: BStore): Set[State] = drive(List(inject(e, env, bstore)), Set())
}

