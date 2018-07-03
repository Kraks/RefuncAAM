package refunc

import scala.util.continuations._
import refunc.ast._
import ANFAAM._

object RefuncECPS {
  import SmallStepUBStack._

  def inject(e: Expr, env: Env = Map(), 
             store: Store[BAddr, Storable] = Store[BAddr, Storable](Map())): Config =
    Config(e, env, store, List())

  type Cont = (Config, Set[Config], MCont) => Set[Config]
  type MCont = (Config, Set[Config]) => Set[Config]

  def aeval(config: Config, seen: Set[Config], continue: Cont, mcontinue: MCont): Set[Config] = {
    val Config(e, env, store, time) = config
    val new_time = config.tick
    val new_seen = if (seen.contains(config)) seen else seen + config
    e match {
      case Let(x, ae, e) if isAtomic(ae) =>
        val baddr = allocBind(x, new_time)
        val new_env = env + (x -> baddr)
        val new_store = store.update(baddr, atomicEval(ae, env, store))
        aeval(Config(e, new_env, new_store, new_time), new_seen, continue, mcontinue)

      case Letrec(bds, body) => 
        val new_env = bds.foldLeft(env)((accenv: Env, bd: B) =>
          accenv + (bd.x -> allocBind(bd.x, new_time)))
        val new_store = bds.foldLeft(store)((accbst: BStore, bd: B) => 
          accbst.update(allocBind(bd.x, new_time), atomicEval(bd.e, new_env, accbst)))
        aeval(Config(body, new_env, new_store, new_time), new_seen, continue, mcontinue)

      case Let(x, App(f, ae), e) =>
        val closures = atomicEval(f, env, store).toList.asInstanceOf[List[Clos]]
        val Clos(Lam(v, body), c_env) = closures.head
        val baddr = allocBind(v, new_time)
        val new_env = c_env + (v -> baddr)
        val argvs = atomicEval(ae, env, store)
        val new_store = store.update(baddr, argvs)
        val new_cont: Cont = { case (config@Config(ae, env_, store, time), seen, m) => 
          val new_time = config.tick
          val baddr = allocBind(x, new_time)
          val new_env = env + (x -> baddr)
          val new_store = store.update(baddr, atomicEval(ae, env_, store))
          aeval(Config(e, new_env, new_store, new_time), seen, continue, m)
        }
        def makeMCont(cls: List[Clos]): MCont = {
          val mcont: MCont = { case (config, seen) =>
            if (cls.isEmpty) aeval(config, seen, (c, seen, m) => m(c, seen), mcontinue)
            else {
              val Clos(Lam(v, body), c_env) = cls.head
              val baddr = allocBind(v, new_time)
              val new_env = c_env + (v -> baddr)
              val new_store = store.update(baddr, argvs)
              aeval(Config(body, new_env, new_store, new_time), seen, new_cont, makeMCont(cls.tail))
            }
          }
          mcont
        }
        val new_mcont: MCont = makeMCont(closures.tail)
        aeval(Config(body, new_env, new_store, new_time), new_seen, new_cont, new_mcont)

      case ae if isAtomic(ae) =>
        continue(config, new_seen, mcontinue)
    }
  }

  def analyze(e: Expr): Set[Config] = 
    aeval(inject(e), Set(), { (c, seen, m) => m(c, seen) }, { (c, seen) => seen })

  def analyze(e: Expr, env: Env, bstore: BStore): Set[Config] = 
    aeval(inject(e, env, bstore), Set(), { (c, seen, m) => m(c, seen) }, { (c, seen) => seen })
}
