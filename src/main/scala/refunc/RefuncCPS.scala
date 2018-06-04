package refunc

import scala.util.continuations._
import refunc.ast._
import ANFAAM._

object RefuncCPS {
  import SmallStepUBStack._

  type Cont = Ans => Ans

  def nd[T,S](ts: Iterable[T], acc: S, f: (T, S, S=>S) => S, g: S => S): S = {
    if (ts.isEmpty) g(acc)
    else f(ts.head, acc, (vss: S) => nd(ts.tail, vss, f, g))
  }
  
  def aeval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache, cont: Cont): Ans = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) cont(Ans(cache.outGet(config), cache))
    else {
      val new_time = (e::time).take(k)
      val new_cache = cache.outUpdate(config, cache.inGet(config))

      e match {
        case Let(x, ae, e) if isAtomic(ae) =>
          val baddr = allocBind(x, new_time)
          val new_env = env + (x -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env, store))
          aeval(e, new_env, new_store, new_time, new_cache, { 
            case Ans(evss, ecache) => cont(Ans(evss, ecache.outUpdate(config, evss)))
          })

        case Letrec(bds, body) => 
          val new_env = bds.foldLeft(env)((accenv: Env, bd: B) =>
            accenv + (bd.x -> allocBind(bd.x, new_time)))
          val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) => 
            accbst.update(allocBind(bd.x, new_time), atomicEval(bd.e, new_env, accbst)))
          aeval(body, new_env, new_store, new_time, new_cache, { 
            case Ans(bdss, bdcache) => cont(Ans(bdss, bdcache.outUpdate(config, bdss)))
          })

        case Let(x, App(f, ae), e) =>
          val closures = atomicEval(f, env, store)
          nd[Storable, Ans](closures, Ans(Set[VS](), new_cache), { 
            case (Clos(Lam(v, body), c_env), clsans, clsnd) =>
              val vbaddr = allocBind(v, new_time)
              val new_cenv = c_env + (v -> vbaddr)
              val new_store = store.update(vbaddr, atomicEval(ae, env, store))
              aeval(body, new_cenv, new_store, new_time, clsans.cache, { 
                case Ans(bdvss, bdcache) =>
                  nd[VS, Ans](bdvss, Ans(Set[VS](), bdcache), { 
                    case (VS(vals, time, vssstore), bdans, bdnd) =>
                      val baddr = allocBind(x, time)
                      val new_env = env + (x -> baddr)
                      val new_store = vssstore.update(baddr, vals)
                      aeval(e, new_env, new_store, time, bdans.cache, { 
                        case Ans(evss, ecache) => bdnd(bdans ++ Ans(evss, ecache.outUpdate(config, evss)))
                      })
                  }, { 
                    case eans => clsnd(eans ++ clsans)
                  })
              })
          }, 
          cont)
    
        case ae if isAtomic(ae) =>
          val vs = Set(VS(atomicEval(ae, env, store), new_time, store))
          cont(Ans(vs, new_cache.outUpdate(config, vs)))
      }
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      val Ans(vss, new_cache) = aeval(e, env, store, mtTime, cache, {
        case Ans(vss, cache) => 
          val init_config = Config(e, env, store, mtTime)
          Ans(vss, cache.outUpdate(init_config, vss))
      })
      if (new_cache.out == cache.out) { Ans(vss, new_cache) }
      else { iter(Cache(new_cache.out, new_cache.out)) }
    }
    iter(Cache.mtCache)
  }
}



/* Experimental implementation with breadth first evaluation */
object RefuncCPSBF {
  import SmallStepUBStack._
  
  type Cont = (Set[VS], Cache) => (Set[VS], Cache)

  def nd[T](ts: Set[T], acc: Set[VS], cache: Cache, 
            f: (T, Set[VS], Cache, Cont) => (Set[VS], Cache), g: Cont): (Set[VS], Cache) = {
    if (ts.isEmpty) g(acc, cache)
    else f(ts.head, acc, cache, (vss: Set[VS], cache: Cache) => nd(ts.tail, vss, cache, f, g))
  }

  def aeval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache, cont: Cont): (Set[VS], Cache) = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) {
      return cont(cache.outGet(config), cache)
    }

    val new_cache = cache.outUpdate(config, cache.inGet(config))
    val new_time = (e::time).take(k)
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
          (ans: Set[VS], cache: Cache) => cont(ans, cache.outUpdate(config, ans)))
        })
  
      case ae if isAtomic(ae) =>
        val vs = Set(VS(atomicEval(ae, env, store), new_time, store))
        cont(vs, new_cache.outUpdate(config, vs))
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

