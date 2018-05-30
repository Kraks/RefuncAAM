package refunc

import scala.util.continuations._
import refunc.ast._
import ANFAAM._

object DirectStyleDC {
  /* Depth first evaluation */
  import SmallStepUBStack._
  
  type Cont = Ans => Ans

  def nd[T](ts: Set[T], acc: Ans, k: ((T, Cache)) => Ans): Ans = {
    if (ts.isEmpty) acc
    else nd(ts.tail, acc ++ k(ts.head, acc.cache), k)
  }
  
  def ndcps[T](ts: Set[T], acc: Ans): (T, Cache) @cps[Ans] = shift { f: (((T, Cache)) => Ans) => 
    nd(ts, acc, f)
  }
  
  def aval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache): Ans @cps[Ans] = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) Ans(cache.outGet(config), cache)
    else {
      val new_time = (e::time).take(k)
      val new_cache = cache.outUpdate(config, cache.inGet(config))

      e match {
        case Let(x, ae, e) if isAtomic(ae) =>
          val baddr = allocBind(x, new_time)
          val new_env = env + (x -> baddr)
          val new_store = store.update(baddr, aeval(ae, env, store))
          val Ans(eval, ecache) = aval(e, new_env, new_store, new_time, new_cache)
          Ans(eval, ecache.outUpdate(config, eval))

        case Letrec(bds, body) => 
          val new_env = bds.foldLeft(env)((accenv: Env, bd: B) => { accenv + (bd.x -> allocBind(bd.x, new_time)) })
          val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) => { accbst.update(allocBind(bd.x, new_time), aeval(bd.e, new_env, accbst)) })
          val Ans(finval, fincache) = aval(body, new_env, new_store, new_time, new_cache)
          Ans(finval, fincache.outUpdate(config, finval))

        case Let(x, App(f, ae), e) =>
          val closures = atomicEval(f, env, store).asInstanceOf[Set[Clos]]
          val (Clos(Lam(v, body), c_env), clscache) = ndcps[Clos](closures, Ans(Set[VS](), new_cache))
          val vbaddr = allocBind(v, new_time)
          val new_cenv = c_env + (v -> vbaddr)
          val new_cstore = store.update(vbaddr, aeval(ae, env, store))
          val Ans(bodyvss, bodycache) = aval(body, new_cenv, new_cstore, new_time, clscache)
          val (VS(vals, time, vsstore), vscache) = ndcps[VS](bodyvss, Ans(Set[VS](), bodycache))
          val baddr = allocBind(x, time)
          val new_env = env + (x -> baddr)
          val new_store = vsstore.update(baddr, vals)
          val Ans(finval, fincache) = aval(e, new_env, new_store, time, vscache)
          Ans(finval, fincache.outUpdate(config, finval))

        case ae if isAtomic(ae) =>
          val vs = Set(VS(atomicEval(ae, env, store), new_time, store))
          Ans(vs, cache.outUpdate(config, vs))
      }
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      val Ans(vss, anscache) = reset { aval(e, env, store, mtTime, cache) }
      val initConfig = Config(e, env, store, mtTime)
      val new_cache = anscache.outUpdate(initConfig, vss)
      if (new_cache.out == cache.out) { Ans(vss, new_cache) }
      else { iter(Cache(new_cache.out, new_cache.out)) }
    }
    iter(Cache.mtCache)
  }
}

object DirectStyleSideEff {
  /* Using side effect to update new_cache */
  import SmallStepUBStack._
  import RefuncCPS._

  def aval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache): Ans = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) {
      return Ans(cache.outGet(config), cache)
    }

    var new_cache = cache.outUpdate(config, cache.inGet(config))
    val new_time = (e::time).take(k)

    e match {
      case Let(x, ae, e) if isAtomic(ae) =>
        val baddr = allocBind(x, new_time)
        val new_env = env + (x -> baddr)
        val new_store = store.update(baddr, aeval(ae, env, store))
        val Ans(eval, ecache) = aval(e, new_env, new_store, new_time, new_cache)
        Ans(eval, ecache.outUpdate(config, eval))

      case Letrec(bds, body) =>
        val new_env = bds.foldLeft(env)((accenv: Env, bd: B) => {
                                          accenv + (bd.x -> allocBind(bd.x, new_time))
                                        })
        val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) => {
                                              accbst.update(allocBind(bd.x, new_time), aeval(bd.e, new_env, accbst))
                                            })
        val Ans(vss, cache) = aval(body, new_env, new_store, new_time, new_cache)
        Ans(vss, cache.outUpdate(config, vss))

      case Let(x, App(f, ae), e) =>
        val closures = aeval(f, env, store).toList.asInstanceOf[List[Clos]]
        val letvs = for (Clos(Lam(v, body), c_env) <- closures) yield {
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = store.update(baddr, aeval(ae, env, store))
          val Ans(bdv, bdcache) = aval(body, new_env, new_store, new_time, new_cache)
          new_cache = bdcache
          val evs = for (VS(vals, time, store) <- bdv) yield {
            val baddr = allocBind(x, time)
            val new_env = env + (x -> baddr)
            val new_store = store.update(baddr, vals)
            val Ans(ev, ecache) = aval(e, new_env, new_store, time, new_cache)
            new_cache = ecache
            ev
          }
          evs.foldLeft(Set[VS]())(_ ++ _)
        }
        val letv = letvs.foldLeft(Set[VS]())(_ ++ _)
        Ans(letv, new_cache.outUpdate(config, letv))

      case ae if isAtomic(ae) =>
        val vs = Set(VS(aeval(ae, env, store), new_time, store))
        Ans(vs, new_cache.outUpdate(config, vs))
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      val Ans(vss, new_cache_) = aval(e, env, store, mtTime, cache)
      val new_cache = new_cache_.outUpdate(Config(e, env, store, mtTime), vss)
      if (new_cache.out == cache.out) { Ans(vss, new_cache) }
      else { iter(Cache(new_cache.out, new_cache.out)) }
    }
    iter(Cache.mtCache)
  }

}

