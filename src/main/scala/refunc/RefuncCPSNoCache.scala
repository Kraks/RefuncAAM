package refunc

import scala.util.continuations._
import refunc.ast._

import ANFAAM._

object RefuncCPSNoCache {
  import SmallStepUBStack._
  
  type Ans = Set[VS]
  type Cont = Ans => Ans

  def nd[T,S](ts: Set[T], acc: S, f: (T, S, S=>S) => S, g: S => S): S = {
    if (ts.isEmpty) g(acc)
    else f(ts.head, acc, (vss: S) => nd(ts.tail, vss, f, g))
  }

  def aval(e: Expr, env: Env, store: BStore, time: Time, cont: Cont): Ans = {
    val new_time = (e::time).take(k)
    e match {
      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).asInstanceOf[Set[Clos]]
        nd[Clos, Ans](closures, Set[VS](), { case (clos, clsacc, clsnd) =>
          val Clos(Lam(v, body), c_env) = clos
          val baddr = allocBind(v, new_time)
          val new_cenv = c_env + (v -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          aval(body, new_cenv, new_store, new_time, (bdvss: Set[VS]) => {
            nd[VS, Ans](bdvss, Set[VS](), { case (vs, bdacc, bdnd) =>
              val VS(vals, time, store) = vs
              val baddr = allocBind(x, time)
              val new_env = env + (x -> baddr)
              val new_store = store.update(baddr, vals)
              aval(e, new_env, new_store, time, { case evss => bdnd(bdacc ++ evss) })
            }, { 
              case evss => clsnd(evss ++ clsacc) 
            })
          })
        },
        cont)
  
      case ae if isAtomic(ae) =>
        val ds = atomicEval(ae, env, store)
        cont(Set(VS(ds, new_time, store)))
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) =
    aval(e, env, store, mtTime, (vss => vss))
}



/* Experimental implementation with breadth first evaluation */
object RefuncCPSNoCacheBF {
  import SmallStepUBStack._
  
  type Cont = Set[VS] => Set[VS]

  def nd[T](cs: List[T], acc: Set[VS], f: (T, Set[VS], Cont) => Set[VS], g: Cont): Set[VS] = {
    cs match {
      case Nil => g(acc)
      case c::cs => f(c, acc, (vss: Set[VS]) => nd(cs, vss, f, g))
    }
  }

  def aval(e: Expr, env: Env, store: BStore, time: Time, cont: Cont): Set[VS] = {
    val new_time = (e::time).take(k)
    e match {
      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).toList.asInstanceOf[List[Clos]]
        nd(closures, Set[VS](), (clos: Clos, acc: Set[VS], ndk: Cont) => {
          val Clos(Lam(v, body), c_env) = clos
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          aval(body, new_env, new_store, new_time, (bodyvss: Set[VS]) => { ndk(bodyvss++acc) })
        }, (result_vss: Set[VS]) => {
          nd(result_vss.toList, Set[VS](), (vs: VS, acc: Set[VS], ndk: Cont) => {
            val VS(vals, time, store) = vs
            val baddr = allocBind(x, time)
            val new_env = env + (x -> baddr)
            val new_store = store.update(baddr, vals)
            aval(e, new_env, new_store, time, (evss: Set[VS]) => { ndk(evss++acc) })
          },
          cont)
        })
      case ae if isAtomic(ae) =>
        val ds = atomicEval(ae, env, store)
        cont(Set(VS(ds, new_time, store)))
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) =
    aval(e, env, store, mtTime, (vss => vss))
}
