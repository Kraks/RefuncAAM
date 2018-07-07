package refunc

import scala.util.continuations._
import refunc.ast._
import ANFAAM._

object RefuncCPS {
  type Cont = Ans => Ans

  def nd[T](ts: Iterable[T], acc: Ans, k: (T, Cache) => Ans): Ans = {
    if (ts.isEmpty) acc
    else nd(ts.tail, acc ++ k(ts.head, acc.cache), k)
  }
  
  var trace: List[Expr] = List()

  def aeval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache, continue: Cont): Ans = {
    trace = e::trace
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) continue(Ans(cache.outGet(config), cache))
    else {
      val new_time = config.tick
      val new_cache = cache.outUpdate(config, cache.inGet(config))

      e match {
        case Let(x, ae, e) if isAtomic(ae) =>
          val baddr = allocBind(x, new_time)
          val new_env = env + (x -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          aeval(e, new_env, new_store, new_time, new_cache, { 
            case Ans(evss, ecache) => continue(Ans(evss, ecache.outUpdate(config, evss)))
          })

        case Letrec(bds, body) => 
          val new_env = bds.foldLeft(env)((accenv: Env, bd: B) =>
            accenv + (bd.x -> allocBind(bd.x, new_time)))
          val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) => 
            accbst.update(allocBind(bd.x, new_time), atomicEval(bd.e, new_env, accbst)))
          aeval(body, new_env, new_store, new_time, new_cache, { 
            case Ans(bdss, bdcache) => continue(Ans(bdss, bdcache.outUpdate(config, bdss)))
          })

        case Let(x, App(f, ae), e) =>
          val closures = atomicEval(f, env, store)
          nd[Storable](closures, Ans(Set[VS](), new_cache), { 
            case (Clos(Lam(v, body), c_env), clscache) =>
              val vbaddr = allocBind(v, new_time)
              val new_cenv = c_env + (v -> vbaddr)
              val new_store = store.update(vbaddr, atomicEval(ae, env, store))
              aeval(body, new_cenv, new_store, new_time, clscache, { 
                case Ans(bdvss, bdcache) =>
                  nd[VS](bdvss, Ans(Set[VS](), bdcache), { 
                    case (VS(vals, time, vssstore), bdvsscache) =>
                      val baddr = allocBind(x, time)
                      val new_env = env + (x -> baddr)
                      val new_store = vssstore.update(baddr, vals)
                      aeval(e, new_env, new_store, time, bdvsscache, { 
                        case Ans(evss, ecache) => continue(Ans(evss, ecache.outUpdate(config, evss)))
                      })
                  })
              })
          })
    
        case ae if isAtomic(ae) =>
          val vs = Set(VS(atomicEval(ae, env, store), new_time, store))
          continue(Ans(vs, new_cache.outUpdate(config, vs)))
      }
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      trace = List()
      val Ans(vss, anscache) = aeval(e, env, store, mtTime, cache, ans => ans)
      assert(anscache.outContains(Config(e, env, store, mtTime)))
      if (anscache.out == anscache.in) { Ans(vss, anscache) }
      else { iter(Cache(anscache.out, Store[Config, VS](Map()))) }
    }
    iter(Cache.mtCache)
  }
}

object RefuncCPSNoCache {
  type Ans = Set[Config]
  type Cont = (Config, Ans) => Ans

  def inject(e: Expr, env: Env = Map(), 
             store: Store[BAddr, Storable] = Store[BAddr, Storable](Map())): Config =
    Config(e, env, store, List())

  def nd[T](ts: Iterable[T], acc: Ans, k: (T, Ans) => Ans): Ans = {
    if (ts.isEmpty) acc
    else nd(ts.tail, acc ++ k(ts.head, acc), k)
  }
  
  def aeval(config: Config, seen: Ans, continue: Cont): Ans = {
    trace = config.e::trace
    val Config(e, env, store, time) = config
    val new_time = config.tick
    val new_seen = if (seen.contains(config)) seen else seen + config
    e match {
      case Let(x, ae, e) if isAtomic(ae) =>
        val baddr = allocBind(x, new_time)
        val new_env = env + (x -> baddr)
        val new_store = store.update(baddr, atomicEval(ae, env, store))
        aeval(Config(e, new_env, new_store, new_time), new_seen, continue)

      case Letrec(bds, body) => 
        val new_env = bds.foldLeft(env)((accenv: Env, bd: B) =>
          accenv + (bd.x -> allocBind(bd.x, new_time)))
        val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) => 
          accbst.update(allocBind(bd.x, new_time), atomicEval(bd.e, new_env, accbst)))
        aeval(Config(body, new_env, new_store, new_time), new_seen, continue)

      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).toList.asInstanceOf[List[Clos]]
        nd[Storable](closures, new_seen, { case (Clos(Lam(v, body), c_env), seen) =>
          val baddr = allocBind(v, new_time)
          val new_env = c_env + (v -> baddr)
          val argvs = atomicEval(ae, env, store)
          val new_store = store.update(baddr, argvs)
          aeval(Config(body, new_env, new_store, new_time), seen, {
            case (config@Config(ae, env_, store, time), seen) =>
              val new_time = config.tick
              val baddr = allocBind(x, new_time)
              val new_env = env + (x -> baddr)
              val new_store = store.update(baddr, atomicEval(ae, env_, store))
              aeval(Config(e, new_env, new_store, new_time), seen, continue)
          })
        })

      case ae if isAtomic(ae) =>
        continue(config, new_seen)
    }
  }
  var trace: List[Expr] = List()

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore): Set[Config] = {
    trace = List()
    aeval(inject(e, env, store), Set(), { (c, seen) => seen })
  }
}
