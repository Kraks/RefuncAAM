package refunc.plainlam

import scala.util.continuations._
import refunc.ast._
import refunc.ANFAAM._

object DSAAM {
  trait Cont
  case class Ar(e: Expr, env: Env) extends Cont
  case class Fn(lam: Expr, env: Env) extends Cont
  case class Br(thn: Expr, els: Expr, env: Env) extends Cont

  case class State(e: Expr, env: Env, store: BStore, konts: List[Cont], time: Time) {
    def tick: Time = (e :: time).take(k)
  }

  def inject(e: Expr, env: Env = mtEnv, store: Store[BAddr, Storable] = mtStore): State =
    State(e, env, store, List(), List())
}
