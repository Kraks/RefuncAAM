package gnw.refunc

import scala.util.continuations._
import gnw.refunc.ast._
import ANFAAM._

case class Config(e: Expr, env: Env, store: BStore, time: Time)
case class Cache(in: Store[Config, VS], out: Store[Config, VS]) {
  def inGet(config: Config): Set[VS] = in.getOrElse(config, Set())
  def inContains(config: Config): Boolean = in.contains(config)
  def outGet(config: Config): Set[VS] = out.getOrElse(config, Set())
  def outContains(config: Config): Boolean = out.contains(config)
  def outUpdate(config: Config, vss: Set[VS]): Cache = { Cache(in, out.update(config, vss)) }
  def outUpdate(config: Config, vs: VS): Cache = { Cache(in, out.update(config, vs)) }
  def outJoin(c: Cache): Cache = { Cache(in, out.join(c.out)) }

  def outVS: Set[VS] = { out.map.values.foldLeft(Set[VS]())(_ ++ _) }
}

object Cache {
  def mtCache = Cache(Store[Config, VS](Map()), Store[Config, VS](Map()))
}

case class Ans(vss: Set[VS], cache: Cache) {
  def ++(ans: Ans): Ans = {
    Ans(vss ++ ans.vss, ans.cache.outJoin(cache))
  }
}

object RefuncCPS {
  /* Depth First Evaluation */
  import SmallStepUBStack._

  type Cont = Ans => Ans

  def nd[T,S](ts: Set[T], acc: S, f: (T, S, S=>S) => S, g: S => S): S = {
    if (ts.isEmpty) g(acc)
    else f(ts.head, acc, (vss: S) => nd(ts.tail, vss, f, g))
  }
  
  def aval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache, cont: Cont): Ans = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) {
      return cont(Ans(cache.outGet(config), cache))
    }

    val new_time = (e::time).take(k)
    val new_cache = cache.outUpdate(config, cache.inGet(config))

    e match {
      case Let(x, ae, e) if isAtomic(ae) =>
        val baddr = allocBind(x, new_time)
        val new_env = env + (x -> baddr)
        val new_store = store.update(baddr, aeval(ae, env, store))
        aval(e, new_env, new_store, new_time, new_cache, { case Ans(evss, ecache) => 
          cont(Ans(evss, ecache.outUpdate(config, evss)))
        })

      case Letrec(bds, body) => 
        val new_env = bds.foldLeft(env)((accenv: Env, bd: B) => { accenv + (bd.x -> allocBind(bd.x, new_time)) })
        val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) => { accbst.update(allocBind(bd.x, new_time), aeval(bd.e, new_env, accbst)) })
        aval(body, new_env, new_store, new_time, new_cache, { case Ans(evss, ecache) => 
          cont(Ans(evss, ecache.outUpdate(config, evss)))
        })

      case Let(x, App(f, ae), e) =>
        val closures = aeval(f, env, store).asInstanceOf[Set[Clos]]
        nd[Clos, Ans](closures, Ans(Set[VS](), new_cache), { case (clos, Ans(acc, cache), closnd) =>
          val Clos(Lam(v, body), c_env) = clos
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = store.update(baddr, aeval(ae, env, store))
          aval(body, new_env, new_store, new_time, cache, { case Ans(bodyvss, bodycache) =>
            nd[VS, Ans](bodyvss, Ans(Set[VS](), bodycache), { case (vs, Ans(acc_vss, cache), bdnd) =>
              val VS(vals, time, store) = vs
              val baddr = allocBind(x, time)
              val new_env = env + (x -> baddr)
              val new_store = store.update(baddr, vals)
              aval(e, new_env, new_store, time, cache, { case Ans(evss, ecache) => bdnd(Ans(acc_vss ++ evss, ecache)) })
            },
            { case Ans(evss, cache) => closnd(Ans(evss ++ acc, cache)) })
          })
        },
        { case Ans(vss, cache) => cont(Ans(vss, cache.outUpdate(config, vss))) })
  
      case ae if isAtomic(ae) =>
        val vs = Set(VS(aeval(ae, env, store), new_time, store))
        cont(Ans(vs, new_cache.outUpdate(config, vs)))
    }
  }

  def mtTime = List()
  def mtEnv = Map[String, BAddr]()
  def mtStore = Store[BAddr, Storable](Map())

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      val Ans(vss, new_cache) = aval(e, env, store, mtTime, cache, {
        case Ans(vss, cache) => 
          val initConfig = Config(e, env, store, mtTime)
          Ans(vss, cache.outUpdate(initConfig, vss))
      })
      if (new_cache.out == cache.out) { Ans(vss, new_cache) }
      else { iter(Cache(new_cache.out, new_cache.out)) }
    }
    iter(Cache.mtCache)
  }
}

object RefuncCPSBF {
  /* Breath First Evaluation */
  import SmallStepUBStack._
  
  type Cont = (Set[VS], Cache) => (Set[VS], Cache)

  def nd[T](ts: Set[T], acc: Set[VS], cache: Cache, 
            f: (T, Set[VS], Cache, Cont) => (Set[VS], Cache), g: Cont): (Set[VS], Cache) = {
    if (ts.isEmpty) g(acc, cache)
    else f(ts.head, acc, cache, (vss: Set[VS], cache: Cache) => nd(ts.tail, vss, cache, f, g))
  }

  def aval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache, cont: Cont): (Set[VS], Cache) = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) {
      return cont(cache.outGet(config), cache)
    }

    val new_cache = cache.outUpdate(config, cache.inGet(config))
    val new_time = (e::time).take(k)
    e match {
      case Let(x, App(f, ae), e) =>
        val closures = aeval(f, env, store).asInstanceOf[Set[Clos]]
        nd(closures, Set[VS](), new_cache, (clos: Clos, acc: Set[VS], cache: Cache, ndk: Cont) => {
          val Clos(Lam(v, body), c_env) = clos
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val new_store = store.update(baddr, aeval(ae, env, store))
          aval(body, new_env, new_store, new_time, cache, (bodyvss: Set[VS], cache: Cache) => { ndk(bodyvss++acc, cache) })
        }, (result_vss: Set[VS], cache: Cache) => {
          nd(result_vss, Set[VS](), cache, (vs: VS, acc: Set[VS], cache: Cache, ndk: Cont) => {
            val VS(vals, time, store) = vs
            val baddr = allocBind(x, time)
            val new_env = env + (x -> baddr)
            val new_store = store.update(baddr, vals)
            aval(e, new_env, new_store, time, cache, (evss: Set[VS], cache: Cache) => { ndk(evss++acc, cache) })
          },
          (ans: Set[VS], cache: Cache) => cont(ans, cache.outUpdate(config, ans)))
        })
  
      case ae if isAtomic(ae) =>
        val vs = Set(VS(aeval(ae, env, store), new_time, store))
        cont(vs, new_cache.outUpdate(config, vs))
    }
  }

  def mtTime = List()
  def mtEnv = Map[String, BAddr]()
  def mtStore = Store[BAddr, Storable](Map())

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): (Set[VS], Cache) = {
      val (vss, new_cache) = aval(e, env, store, mtTime, cache, (vss, cache) => (vss, cache.outUpdate(Config(e, env, store, mtTime), vss)))
      if (new_cache.out == cache.out) { (vss, new_cache) }
      else { iter(Cache(new_cache.out, new_cache.out)) }
    }
    iter(Cache.mtCache)
  }
}

