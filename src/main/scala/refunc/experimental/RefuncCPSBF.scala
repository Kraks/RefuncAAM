package refunc.experimental

import refunc.ast._
import refunc.ANFAAM._
import scala.util.continuations._

/* Experimental implementation with breadth first evaluation */
object RefuncCPSBF {
  type Cont = (Set[VS], Cache) => (Set[VS], Cache)

  def nd[T](ts: Set[T], acc: Set[VS], cache: Cache, 
            f: (T, Set[VS], Cache, Cont) => (Set[VS], Cache), g: Cont): (Set[VS], Cache) = {
    if (ts.isEmpty) g(acc, cache)
    else f(ts.head, acc, cache, (vss: Set[VS], cache: Cache) => nd(ts.tail, vss, cache, f, g))
  }

  def aeval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache, continue: Cont): (Set[VS], Cache) = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) {
      return continue(cache.outGet(config), cache)
    }

    val new_cache = cache.outUpdate(config, cache.inGet(config))
    val new_time = config.tick
    e match {
      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).asInstanceOf[Set[Clos]]
        nd(closures, Set[VS](), new_cache, (clos: Clos, acc: Set[VS], cache: Cache, ndk: Cont) => {
          val Clos(Lam(v, body), c_env) = clos
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          aeval(body, new_env, new_store, new_time, cache, (bodyvss: Set[VS], cache: Cache) => { 
            ndk(bodyvss++acc, cache) 
          })
        }, (result_vss: Set[VS], cache: Cache) => {
          nd(result_vss, Set[VS](), cache, (vs: VS, acc: Set[VS], cache: Cache, ndk: Cont) => {
            val VS(vals, time, store) = vs
            val baddr = allocBind(x, time)
            val new_env = env + (x -> baddr)
            val new_store = store.update(baddr, vals)
            aeval(e, new_env, new_store, time, cache, (evss: Set[VS], cache: Cache) => { 
              ndk(evss++acc, cache) 
            })
          },
          (ans: Set[VS], cache: Cache) => continue(ans, cache.outUpdate(config, ans)))
        })
  
      case ae if isAtomic(ae) =>
        val vs = Set(VS(atomicEval(ae, env, store), new_time, store))
        continue(vs, new_cache.outUpdate(config, vs))
    }
  }


  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): (Set[VS], Cache) = {
      val (vss, new_cache) = aeval(e, env, store, mtTime, cache, (vss, cache) => (vss, cache.outUpdate(Config(e, env, store, mtTime), vss)))
      if (new_cache.out == cache.out) { (vss, new_cache) }
      else { iter(Cache(new_cache.out, new_cache.out)) }
    }
    iter(Cache.mtCache)
  }
}

