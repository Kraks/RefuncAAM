package refunc

import scala.util.continuations._
import refunc.ast._
import ANFAAM._

object DirectStyleDC {
  @deprecated
  def ndcps[T](ts: Set[T], acc: Ans): (T, Cache) @cps[Ans] = shift { 
    f: (((T, Cache)) => Ans) => nd(ts, acc, f)
  }

  def nd[T](ts: Iterable[T], acc: Ans, k: ((T, Cache)) => Ans): Ans = {
    if (ts.isEmpty) acc
    else nd(ts.tail, acc ++ k(ts.head, acc.cache), k)
  }

  def choices[T](ts: Iterable[T], cache: Cache): (T, Cache) @cps[Ans] = shift { 
    f: (((T, Cache)) => Ans) => nd(ts, Ans(Set[VS](), cache), f)
  }

  var trace: List[Expr] = List()

  def aeval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache): Ans @cps[Ans] = {
    trace = e::trace
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) Ans(cache.outGet(config), cache)
    else {
      val new_time = config.tick
      val new_cache = cache.outUpdate(config, cache.inGet(config))

      e match {
        case Let(x, ae, e) if isAtomic(ae) =>
          val baddr = allocBind(x, new_time)
          val new_env = env + (x -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          val Ans(evss, ecache) = aeval(e, new_env, new_store, new_time, new_cache)
          Ans(evss, ecache.outUpdate(config, evss))

        case Letrec(bds, body) => 
          val new_env = bds.foldLeft(env)((accenv: Env, bd: B) =>
            accenv + (bd.x -> allocBind(bd.x, new_time)))
          val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) =>
            accbst.update(allocBind(bd.x, new_time), atomicEval(bd.e, new_env, accbst)))
          val Ans(bdss, bdcache) = aeval(body, new_env, new_store, new_time, new_cache)
          Ans(bdss, bdcache.outUpdate(config, bdss))

        case Let(x, App(f, ae), e) =>
          val closures = atomicEval(f, env, store)
          val (Clos(Lam(v, body), c_env), clscache) = choices[Storable](closures, new_cache)
          val vbaddr = allocBind(v, new_time)
          val new_cenv = c_env + (v -> vbaddr)
          val new_store = store.update(vbaddr, atomicEval(ae, env, store))
          val Ans(bdvss, bdcache) = aeval(body, new_cenv, new_store, new_time, clscache)
          val (VS(vals, time, vsstore), vscache) = choices[VS](bdvss, bdcache)
          val baddr = allocBind(x, time)
          val new_env = env + (x -> baddr)
          val new_vsstore = vsstore.update(baddr, vals)
          val Ans(evss, ecache) = aeval(e, new_env, new_vsstore, time, vscache)
          Ans(evss, ecache.outUpdate(config, evss))

        case ae if isAtomic(ae) =>
          val vs = Set(VS(atomicEval(ae, env, store), new_time, store))
          Ans(vs, new_cache.outUpdate(config, vs))
      }
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      trace = List()
      val Ans(vss, anscache) = reset { aeval(e, env, store, mtTime, cache) }
      assert(anscache.outContains(Config(e, env, store, mtTime)))
      if (anscache.out == anscache.in) { Ans(vss, anscache) }
      else { iter(Cache(anscache.out, Store[Config, VS](Map()))) }
    }
    iter(Cache.mtCache)
  }
}

object DirectStyleSideEff {
  /* Using side effect to update new_cache */
  import RefuncCPS._

  var trace: List[Expr] = List()
  def aeval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache): Ans = {
    trace = e::trace
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) {
      return Ans(cache.outGet(config), cache)
    }
    
    /* Use mutation to update the cache every time. */
    var new_cache = cache.outUpdate(config, cache.inGet(config))
    val new_time = config.tick

    e match {
      case Let(x, ae, e) if isAtomic(ae) =>
        val baddr = allocBind(x, new_time)
        val new_env = env + (x -> baddr)
        val new_store = store.update(baddr, atomicEval(ae, env, store))
        val Ans(eval, ecache) = aeval(e, new_env, new_store, new_time, new_cache)
        Ans(eval, ecache.outUpdate(config, eval))

      case Letrec(bds, body) =>
        val new_env = bds.foldLeft(env)((accenv: Env, bd: B) => 
          accenv + (bd.x -> allocBind(bd.x, new_time)))
        val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) =>
          accbst.update(allocBind(bd.x, new_time), atomicEval(bd.e, new_env, accbst)))
        val Ans(vss, cache) = aeval(body, new_env, new_store, new_time, new_cache)
        Ans(vss, cache.outUpdate(config, vss))

      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).toList.asInstanceOf[List[Clos]]
        val letvs = for (Clos(Lam(v, body), c_env) <- closures) yield {
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          val Ans(bdv, bdcache) = aeval(body, new_env, new_store, new_time, new_cache)
          new_cache = bdcache
          val evs = for (VS(vals, time, store) <- bdv) yield {
            val baddr = allocBind(x, time)
            val new_env = env + (x -> baddr)
            val new_store = store.update(baddr, vals)
            val Ans(ev, ecache) = aeval(e, new_env, new_store, time, new_cache)
            new_cache = ecache.outUpdate(config, ev)
            ev
          }
          evs.foldLeft(Set[VS]())(_ ++ _)
        }
        Ans(letvs.foldLeft(Set[VS]())(_ ++ _), new_cache)

      case ae if isAtomic(ae) =>
        val vs = Set(VS(atomicEval(ae, env, store), new_time, store))
        Ans(vs, new_cache.outUpdate(config, vs))
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      trace = List()
      val Ans(vss, anscache) = aeval(e, env, store, mtTime, cache)
      assert(anscache.outContains(Config(e, env, store, mtTime)))
      if (anscache.out == anscache.in) { Ans(vss, anscache) }
      else { iter(Cache(anscache.out, Store[Config, VS](Map()))) }
    }
    iter(Cache.mtCache)
  }
}

