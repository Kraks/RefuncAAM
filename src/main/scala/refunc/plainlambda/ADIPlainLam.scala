package refunc.plainlambda

import scala.util.continuations._
import refunc.ast._
import refunc.ANFAAM._

object DSAAM {
  trait Cont
  //case object Mt extends Cont
  case class Ar(e: Expr, env: Env) extends Cont
  case class Fn(lam: Expr, env: Env) extends Cont

  case class State(e: Expr, env: Env, store: BStore, konts: List[Cont], time: Time) {
    def tick: Time = (e :: time).take(k)
  }

  def inject(e: Expr, env: Env = mtEnv, store: Store[BAddr, Storable] = mtStore): State =
    State(e, env, store, List(), List())
}

/* Abstract abstract machine with P4F allocator for plain lambda-calculus. */
object AAMUBPlainLam {
  import DSAAM._

  def isValue(e: Expr): Boolean = e.isInstanceOf[Value]

  def step(s: State): List[State] = {
    val new_time = s.tick
    s match {
      case State(App(e1, e2), env, store, konts, time) =>
        List(State(e1, env, store, Ar(e2, env)::konts, new_time))
      case State(Var(x), env, store, konts, time) =>
        for (v <- atomicEval(Var(x), env, store).toList) yield v match {
          case Clos(lam, c_env) => State(lam, c_env, store, konts, new_time)
          case NumV => State(NumV, env, store, konts, new_time)
        }
      case State(v, env, store, konts, time) if isValue(v)=>
        konts match {
          case Fn(Lam(x, body), c_env)::ks =>
            val baddr = allocBind(x, new_time)
            val new_env = c_env + (x -> baddr)
            val new_store = store.update(baddr, atomicEval(v, env, store))
            List(State(body, new_env, new_store, ks, new_time))
          case Ar(arg, arg_env)::ks if v.isInstanceOf[Lam] =>
            List(State(arg, arg_env, store, Fn(v, env)::ks, new_time))
          case _ => List() //including cases of type error, or spurious flows
        }
    }
  }

  def drive(todo: List[State], seen: Set[State]): Set[State] = todo match {
    case Nil => seen
    case hd::tl if seen.contains(hd) => drive(tl, seen)
    case hd::tl => drive(step(hd).toList ++ tl, seen + hd)
  }

  def analyze(e: Expr): Set[State] = drive(List(inject(e)), Set())

  def analyze(e: Expr, env: Env, bstore: BStore): Set[State] = drive(List(inject(e, env, bstore)), Set())
}

/* Abstract definitional interpreter using delimited control for plain lambda-calculus. */
object ADIPlainLam {
  def nd[T](ts: Iterable[T], acc: Ans, k: ((T, Cache)) => Ans): Ans = {
    if (ts.isEmpty) acc
    else nd(ts.tail, acc ++ k(ts.head, acc.cache), k)
  }

  def choices[T](ts: Iterable[T], cache: Cache): (T, Cache) @cps[Ans] = shift { 
    f: (((T, Cache)) => Ans) => nd(ts, Ans(Set[VS](), cache), f)
  }
  
  def aeval(e: Expr, env: Env, store: BStore, time: Time, cache: Cache): Ans @cps[Ans] = {
    val config = Config(e, env, store, time)
    if (cache.outContains(config)) Ans(cache.outGet(config), cache)
    else {
      val new_time = config.tick
      val new_cache = cache.outUpdate(config, cache.inGet(config))
      e match {
        case ae if isAtomic(ae) =>
          val vs = Set(VS(atomicEval(ae, env, store), new_time, store))
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
      }
    }
  }

  def analyze(e: Expr, env: Env = mtEnv, store: BStore = mtStore) = {
    def iter(cache: Cache): Ans = {
      val Ans(vss, anscache) = reset { aeval(e, env, store, mtTime, cache) }
      val init_config = Config(e, env, store, mtTime)
      val new_cache = anscache.outUpdate(init_config, vss)
      if (new_cache.out == cache.out) { Ans(vss, new_cache) }
      else { iter(Cache(new_cache.out, new_cache.out)) }
    }
    iter(Cache.mtCache)
  }
}

object PlainLamTest {
  def main(args: Array[String]) {
    val id = Lam("z", Var("z"))
    val exp1 = App(Lam("id", App(Var("id"), Var("id"))), id)
    println(AAMUBPlainLam.analyze(exp1).mkString("\n"))
  }
}

