package refunc

import scala.util.continuations._
import refunc.ast._

import ANFAAM._

/* Exprimental implementations */

object DirectStyleDCNoCache2 {
  /* Depth first evaluation */
  type Ans = Set[VS]
  type Cont = Ans => Ans

  def nd[T,S](ts: Set[T], acc: Set[S], k: T => Set[S]): Set[S] = {
    if (ts.isEmpty) acc
    else {
      val vss = k(ts.head)
      nd(ts.tail, acc ++ vss, k)
    }
  }
  
  def ndcps[T,S](ts: Set[T], acc: Set[S]): T @cps[Set[S]] = shift { f: (T => Set[S]) => 
    nd(ts, acc, f)
  }

  def aeval(e: Expr, env: Env, store: BStore, time: Time): Ans @cps[Ans] = {
    val new_time = (e::time).take(k)
    e match {
      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).asInstanceOf[Set[Clos]]
        val Clos(Lam(v, body), c_env) = ndcps[Clos, VS](closures, Set[VS]())
        val vbaddr = allocBind(v, new_time)
        val new_cenv = c_env + (v -> vbaddr)
        val new_store = store.update(vbaddr, atomicEval(ae, env, store))
        val bdvss = aeval(body, new_cenv, new_store, new_time)
        val VS(vals, time, vsstore) = ndcps[VS, VS](bdvss, Set[VS]())
        val baddr = allocBind(x, time)
        val new_env = env + (x -> baddr)
        val new_vsstore = vsstore.update(baddr, vals)
        aeval(e, new_env, new_vsstore, time)
  
      case ae if isAtomic(ae) =>
        val ds = atomicEval(ae, env, store)
        Set(VS(ds, new_time, store))
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) =
    reset { aeval(e, env, store, mtTime) }
}

/* Exprimental implementations */

object DirectStyleDCNoCache {
  /* Depth first evaluation */
  type Ans = Set[VS]
  type Cont = Ans => Ans

  def nd[T,S](ts: Set[T], acc: S, f: ((T, S, S=>S)) => S, g: S => S): S = {
    if (ts.isEmpty) g(acc)
    else f(ts.head, acc, (vss: S) => nd(ts.tail, vss, f, g))
  }

  def ndcps[T,S](ts: Set[T], acc: S, g: S => S): (T, S, S=>S) @cps[S] = shift { f: (((T, S, S=>S)) => S) =>
    nd(ts, acc, f, g)
  }

  def aeval(e: Expr, env: Env, store: BStore, time: Time): Ans @cps[Ans] = shift { cont: Cont =>
    val new_time = (e::time).take(k)
    e match {
      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).asInstanceOf[Set[Clos]]
        reset {
          val (clos, acc, closnd) = ndcps[Clos, Ans](closures, Set[VS](), cont)
          val Clos(Lam(v, body), c_env) = clos
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          reset { 
            val bdvss = aeval(body, new_env, new_store, new_time)
            reset {
              val (vs, acc_vss, bdnd) = ndcps[VS, Ans](bdvss, Set[VS](), (evss: Ans) => closnd(evss ++ acc))
              val VS(vals, time, store) = vs
              val baddr = allocBind(x, time)
              val new_env = env + (x -> baddr)
              val new_store = store.update(baddr, vals)
              reset {
                val evss = aeval(e, new_env, new_store, time)
                bdnd(acc_vss ++ evss)
              }
            }
          }
        }
  
      case ae if isAtomic(ae) =>
        val ds = atomicEval(ae, env, store)
        cont(Set(VS(ds, new_time, store)))
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) =
    reset { aeval(e, env, store, mtTime) }
}
