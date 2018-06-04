package refunc

import refunc.ast._

object Concrete {
  type Addr = Int
  type Env = Map[String, Addr]
  type Store = Map[Addr, Storable]

  abstract class Storable
  case class Clos(v: Lam, env: Env) extends Storable
  case class Num(i: Int) extends Storable

  def atomicEval(e: Expr, env: Env, store: Store): Storable = e match {
    case Var(x) => store(env(x))
    case lam@Lam(x, body) => Clos(lam, env)
    case _ => throw new NotImplementedError(e.toString)
  }

  def alloc(store: Store): Addr = store.keys.size + 1

  def isAtomic(e: Expr): Boolean = e.isInstanceOf[Var] || e.isInstanceOf[Lam]
}

import Concrete._

/* Concrete interpreter in CESK abstract machine style. */
object CESK {
  case class Frame(x: String, e: Expr, env: Env)
  type Kont = List[Frame]
  case class State(e: Expr, env: Env, store: Store, k: Kont)

  def step(s: State): State = s match {
    case State(Let(x, ae, e), env, store, k) if isAtomic(ae) =>
      val addr = alloc(store)
      State(e, env + (x->addr), store + (addr->atomicEval(ae, env, store)), k)

    case State(Let(x, App(f, ae), e), env, store, k) if isAtomic(ae) =>
      val Clos(Lam(v, body), env_c) = atomicEval(f, env, store)
      val addr = alloc(store)
      val frame = Frame(x, e, env)
      State(body, env_c+(v->addr), store+(addr->atomicEval(ae, env, store)), frame::k)

    case State(ae, env, store, k) if isAtomic(ae) =>
      val Frame(x, e, env_k)::ks = k
      val addr = alloc(store)
      State(e, env_k+(x->addr), store+(addr->atomicEval(ae, env, store)), ks) 
  }

  def drive(s: State): State = s match {
    case State(ae, _, _, Nil) if isAtomic(ae) => s
    case _ => drive(step(s))
  }

  def inject(e: Expr): State = State(e, Map(), Map(), Nil)
  def eval(e: Expr): State = drive(inject(e))
}

/* Refunctionalized concrete interpreter in CPS style. */
object RefuncCESK {
  case class VS(v: Storable, store: Store)
  type Ans = VS
  type Cont = Ans => Ans

  def eval(e: Expr, env: Env, store: Store, k: Cont): VS = e match {
    case Let(x, ae, e) if isAtomic(ae) =>
      val addr = alloc(store)
      eval(e, env+(x->addr), store+(addr->atomicEval(ae, env, store)), k)

    case Let(x, App(f, ae), e) =>
      val Clos(Lam(v, body), env_c) = atomicEval(f, env, store)
      val addr = alloc(store)
      eval(body, env_c+(v->addr), store+(addr->atomicEval(ae, env, store)), (vs: VS) => {
        val addr = alloc(vs.store)
        eval(e, env+(x->addr), vs.store+(addr->vs.v), k)
      })

    case ae if isAtomic(ae) =>
      k(VS(atomicEval(ae, env, store), store))
  }

  def run(e: Expr) = eval(e, Map(), Map(), (vs: VS) => vs)
}

/* Cocnrete interpreter in direct-style. */
object DirectStyleCES {
  import RefuncCESK._
  def eval(e: Expr, env: Env, store: Store): VS = e match {
    case Let(x, ae, e) if isAtomic(ae) =>
      val addr = alloc(store)
      eval(e, env+(x->addr), store+(addr->atomicEval(ae, env, store)))

    case Let(x, App(f, ae), e) =>
      val Clos(Lam(v, body), env_c) = atomicEval(f, env, store)
      val vaddr = alloc(store)
      val VS(appv, appstore) = eval(body, env_c+(v->vaddr), store+(vaddr->atomicEval(ae, env, store)))
      val xaddr = alloc(appstore)
      eval(e, env+(x->xaddr), appstore+(xaddr->appv))

    case ae if isAtomic(ae) =>
      VS(atomicEval(ae, env, store), store)
  }
}
