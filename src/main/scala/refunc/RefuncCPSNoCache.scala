package refunc

import scala.util.continuations._
import refunc.ast._

import ANFAAM._

object RefuncCPSNoCache {
  type Ans = Set[VS]
  type Cont = Ans => Ans

  def nd[T](ts: Iterable[T], acc: Ans, k: (T, Ans => Ans) => Ans, m: Ans => Ans): Ans = {
    if (ts.isEmpty) m(acc)
    else k(ts.head, (ans: Ans) => nd(ts.tail, acc ++ ans, k, m))
  }

  def aeval(e: Expr, env: Env, store: BStore, time: Time, continue: Cont): Ans = {
    val new_time = (e::time).take(k)
    e match {
      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store)
        nd[Storable](closures, Set[VS](), { case (clos, clsnd) =>
          val Clos(Lam(v, body), c_env) = clos
          val baddr = allocBind(v, new_time)
          val new_cenv = c_env + (v -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          aeval(body, new_cenv, new_store, new_time, (bdvss: Set[VS]) => {
            nd[VS](bdvss, Set[VS](), { case (vs, bdnd) =>
              val VS(vals, time, store) = vs
              val baddr = allocBind(x, time)
              val new_env = env + (x -> baddr)
              val new_store = store.update(baddr, vals)
              aeval(e, new_env, new_store, time, bdnd)
            }, clsnd)
          })
        },
        continue)
  
      case ae if isAtomic(ae) =>
        val ds = atomicEval(ae, env, store)
        continue(Set(VS(ds, new_time, store)))
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) =
    aeval(e, env, store, mtTime, (vss => vss))
}



/* Experimental implementation with breadth first evaluation */
object RefuncCPSNoCacheBF {
  type Cont = Set[VS] => Set[VS]

  def nd[T](cs: List[T], acc: Set[VS], f: (T, Set[VS], Cont) => Set[VS], g: Cont): Set[VS] = {
    cs match {
      case Nil => g(acc)
      case c::cs => f(c, acc, (vss: Set[VS]) => nd(cs, vss, f, g))
    }
  }

  def aeval(e: Expr, env: Env, store: BStore, time: Time, continue: Cont): Set[VS] = {
    val new_time = (e::time).take(k)
    e match {
      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).toList.asInstanceOf[List[Clos]]
        nd(closures, Set[VS](), (clos: Clos, acc: Set[VS], ndk: Cont) => {
          val Clos(Lam(v, body), c_env) = clos
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          aeval(body, new_env, new_store, new_time, (bodyvss: Set[VS]) => { ndk(bodyvss++acc) })
        }, (result_vss: Set[VS]) => {
          nd(result_vss.toList, Set[VS](), (vs: VS, acc: Set[VS], ndk: Cont) => {
            val VS(vals, time, store) = vs
            val baddr = allocBind(x, time)
            val new_env = env + (x -> baddr)
            val new_store = store.update(baddr, vals)
            aeval(e, new_env, new_store, time, (evss: Set[VS]) => { ndk(evss++acc) })
          },
          continue)
        })
      case ae if isAtomic(ae) =>
        val ds = atomicEval(ae, env, store)
        continue(Set(VS(ds, new_time, store)))
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) =
    aeval(e, env, store, mtTime, (vss => vss))
}
