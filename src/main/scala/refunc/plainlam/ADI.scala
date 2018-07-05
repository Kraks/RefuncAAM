package refunc.plainlam

import scala.util.continuations._
import refunc.ast._
import refunc.ANFAAM._
import refunc.plainlam.DSAAM._

/* Abstract definitional interpreter using delimited control for plain lambda-calculus. */
object ADIDC {
  def nd[T](ts: Iterable[T], acc: Ans, k: ((T, Cache)) => Ans): Ans = {
    if (ts.isEmpty) acc
    else nd(ts.tail, acc ++ k(ts.head, acc.cache), k)
  }

  def choices[T](ts: Iterable[T], cache: Cache): (T, Cache) @cps[Ans] = shift { 
    f: (((T, Cache)) => Ans) => nd(ts, Ans(Set[VS](), cache), f)
  }
  
  def aeval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache): Ans @cps[Ans] = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) 
      Ans(cache.outGet(config), cache)
    else {
      val new_time = config.tick
      val new_cache = cache.outUpdate(config, cache.inGet(config))
      e match {
        case Num(_) =>
          val vs = Set(VS(Set(NumV), new_time, store))
          Ans(vs, new_cache.outUpdate(config, vs))

        case vbl@Var(x) =>
          val vs = Set(VS(atomicEval(vbl, env, store), new_time, store))
          Ans(vs, new_cache.outUpdate(config, vs))

        case App(f, arg) =>
          val Ans(fs, fcache) = aeval(f, env, store, new_time, new_cache)
          val (VS(fvals, ftime, fstore), new_fcache) = choices[VS](fs, fcache)
          val (Clos(Lam(v, body), c_env), clscache) = choices[Storable](fvals, new_fcache)
          val Ans(args, argcache) = aeval(arg, env, fstore, ftime, clscache)
          val (VS(argvals, argtime, argstore), new_argcache) = choices[VS](args, argcache)
          val baddr = allocBind(v, argtime)
          val new_env = c_env + (v -> baddr)
          val new_store = argstore.update(baddr, argvals)
          val Ans(res, rescache) = aeval(body, new_env, new_store, argtime, new_argcache)
          Ans(res, rescache.outUpdate(config, res))

        case If0(cnd, thn, els) =>
          val Ans(cndvs, cndvscache) = aeval(cnd, env, store, new_time, new_cache)
          val (VS(cndv, cndtime, cndstore), cndcache) = choices[VS](cndvs, cndvscache)
          val thnans = aeval(thn, env, cndstore, cndtime, cndcache)
          val elsans = aeval(els, env, cndstore, cndtime, cndcache)
          thnans ++ elsans

        case v if isValue(v) => 
          val vs = Set(VS(atomicEval(v, env, store), new_time, store))
          Ans(vs, new_cache.outUpdate(config, vs))
      }
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      val Ans(vss, anscache) = reset { aeval(e, env, store, mtTime, cache) }
      if (anscache.out == anscache.in) { Ans(vss, anscache) }
      else { iter(Cache(anscache.out, Store[Config, VS](Map()))) }
    }
    iter(Cache.mtCache)
  }
}

object PlainLamTest {
  def main(args: Array[String]) {
    val id = Lam("z", Var("z"))
    val exp1 = App(Lam("id", App(Var("id"), Var("id"))), id)
    println(AAMUB.analyze(exp1).mkString("\n"))
  }
}

