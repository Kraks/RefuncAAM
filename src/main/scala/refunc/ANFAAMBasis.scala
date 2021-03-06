package refunc

import scala.util.continuations._
import refunc.ast._

object ANFAAM {
  def isValue(e: Expr): Boolean = e.isInstanceOf[Value]

  def isAtomic(e: Expr): Boolean =
    e.isInstanceOf[Var] ||
    e.isInstanceOf[Lam] ||
    e.isInstanceOf[Num] ||
    e.isInstanceOf[PrimOp]

  case class Store[K,V](map: Map[K, Set[V]]) {
    def contains(addr: K): Boolean = map.contains(addr)
    def getOrElse(addr: K, default: Set[V]): Set[V] = map.getOrElse(addr, default)
    def apply(addr: K): Set[V] = map(addr)
    def update(addr: K, d: Set[V]): Store[K,V] = { 
      val oldd = map.getOrElse(addr, Set())
      Store[K, V](map ++ Map(addr -> (d ++ oldd)))
    }
    def update(addr: K, sd: V): Store[K,V] = update(addr, Set(sd))
    def join(s: Store[K,V]): Store[K,V] = { 
      var store = this
      for ((addr, vals) <- s.map) {
        store = store.update(addr, vals)
      }
      store
    }
  }

  type Time = List[Expr]

  case class BAddr(x: String, time: Time)
  type Env = Map[String, BAddr]

  abstract class Storable
  case class  Clos(v: Lam, env: Env) extends Storable
  case class  CNumV(i: Int) extends Storable with Value
  case object NumV extends Storable with Value
  type BStore = Store[BAddr, Storable]

  abstract class KAddr
  case class ContAddr(tgt: Expr) extends KAddr
  case class P4FContAddr(tgt: Expr, tgtEnv: Env) extends KAddr
  case object Halt extends KAddr

  case class Frame(x: String, e: Expr, env: Env)
  case class Cont(frame: Frame, kaddr: KAddr)
  type KStore = Store[KAddr, Cont]

  var k: Int = 0

  def allocBind(x: String, time: Time): BAddr = BAddr(x, time)
  def allocKont(tgtExpr: Expr, tgtEnv: Env, tgtStore: BStore, time: Time): KAddr = ContAddr(tgtExpr)

  case class State(e: Expr, env: Env, bstore: BStore, kstore: KStore, kaddr: KAddr, time: Time) {
    def tick: Time = (e :: time).take(k)
  }

  def inject(e: Expr, env: Env = Map(), bstore: Store[BAddr, Storable] = Store[BAddr, Storable](Map())): State =
    State(e, env, bstore, Store[KAddr, Cont](Map(Halt -> Set())), Halt, List())

  def atomicEval(e: Expr, env: Env, bstore: BStore): Set[Storable] = e match {
    case NumV => Set(NumV)
    case Num(i) => Set(CNumV(i))
    case Var(x) => bstore(env(x))
    case lam@Lam(x, body) => Set(Clos(lam, env))
    case _ => throw new NotImplementedError(e.toString)
  }

  /****************************************************************/

  case class VS(vals: Set[Storable], time: Time, store: BStore)

  case class Config(e: Expr, env: Env, store: BStore, time: Time) {
    def tick: Time = (e :: time).take(k)
  }

  case class Cache(in: Store[Config, VS], out: Store[Config, VS]) {
    def inGet(config: Config): Set[VS] = in.getOrElse(config, Set())
    def inContains(config: Config): Boolean = in.contains(config)
    def outGet(config: Config): Set[VS] = out.getOrElse(config, Set())
    def outContains(config: Config): Boolean = out.contains(config)
    def outUpdate(config: Config, vss: Set[VS]): Cache = { Cache(in, out.update(config, vss)) }
    def outUpdate(config: Config, vs: VS): Cache = { Cache(in, out.update(config, vs)) }
    def join(c: Cache): Cache = { Cache(in.join(c.in), out.join(c.out)) }
    
    def inVS: Set[VS] = { in.map.values.foldLeft(Set[VS]())(_ ++ _) }
    def outVS: Set[VS] = { out.map.values.foldLeft(Set[VS]())(_ ++ _) }
  }

  object Cache {
    def mtCache = Cache(Store[Config, VS](Map()), Store[Config, VS](Map()))
  }

  case class Ans(vss: Set[VS], cache: Cache) {
    def ++(ans: Ans): Ans = {
      Ans(vss ++ ans.vss, cache.join(ans.cache))
      //Ans(vss ++ ans.vss, ans.cache) //If cache is always monotonic
    }
  }

  def mtTime = List()
  def mtEnv = Map[String, BAddr]()
  def mtStore = Store[BAddr, Storable](Map())
}

