package gnw.refunc

import scala.util.continuations._
import gnw.refunc.ast._
import ANFAAM._

object DisLinearSmallStepUBStack {
  import SmallStepUBStack._

  case class NDCont(cls: List[Clos], argvs: Set[Storable], store: BStore, time: Time, frames: List[Frame])

  case class NDState(e: Expr, env: Env, bstore: BStore, konts: List[Frame], time: Time, ndk: List[NDCont]) {
    def toState: State = State(e, env, bstore, konts, time)
  }

  def tick(s: NDState): Time = (s.e::s.time).take(k)

  def inject(e: Expr, env: Env = Map(), bstore: Store[BAddr, Storable] = Store[BAddr, Storable](Map())): NDState =
    NDState(e, env, bstore, List(), List(), List())

  def drive_step(nds: NDState, seen: Set[State]): Set[State] = {
    nds match {
      case NDState(ae, _, _, Nil, _, Nil) if isAtomic(ae) => seen
      case nds =>
        val s = nds.toState
        val new_seen = if (seen.contains(s)) seen else seen + s
        val new_time = tick(nds)
        nds match {
          case NDState(Let(x, App(f, ae), e), env, bstore, konts, time, ndk) =>
            val closures = atomicEval(f, env, bstore).toList.asInstanceOf[List[Clos]]
            val Clos(Lam(v, body), c_env) = closures.head
            val frame = Frame(x, e, env)
            val baddr = allocBind(v, new_time)
            val new_env = c_env + (v -> baddr)
            val argvs = atomicEval(ae, env, bstore)
            val new_store = bstore.update(baddr, argvs)
            val new_frames = frame::konts
            val new_ndk = NDCont(closures.tail, argvs, bstore, new_time, new_frames)::ndk
            drive_step(NDState(body, new_env, new_store, new_frames, new_time, new_ndk), new_seen)

          case NDState(ae, env, bstore, konts, time, ndk) if isAtomic(ae) =>
            continue(nds, new_seen)
        }
    }
  }

  def continue(nds: NDState, seen: Set[State]): Set[State] = {
    val NDState(ae, env, bstore, konts, time, ndk) = nds
    val new_time = tick(nds)
    konts match {
      case Nil => ndcontinue(nds, seen)
      case Frame(x, e, f_env)::konts =>
        val baddr = allocBind(x, new_time)
        val new_env = f_env + (x -> baddr)
        val new_store = bstore.update(baddr, atomicEval(ae, env, bstore))
        drive_step(NDState(e, new_env, new_store, konts, new_time, ndk), seen)
    }
  }

  def ndcontinue(nds: NDState, seen: Set[State]): Set[State] = {
    val NDState(ae, env, bstore, konts, time, ndk) = nds
    ndk match {
      case NDCont(Nil, _, _, _, _)::ndk => 
        drive_step(NDState(ae, env, bstore, konts, time, ndk), seen)
      case NDCont(cls, argvs, bstore, time, frames)::ndk => 
        val Clos(Lam(v, body), c_env) = cls.head
        val baddr = allocBind(v, time)
        val new_env = c_env + (v -> baddr)
        val new_store = bstore.update(baddr, argvs)
        drive_step(NDState(body, new_env, new_store, frames, time, 
                           NDCont(cls.tail, argvs, bstore, time, frames)::ndk),
                   seen)
    }
  }

  def analyze(e: Expr): Set[State] = drive_step(inject(e), Set())

  def analyze(e: Expr, env: Env, bstore: BStore): Set[State] = drive_step(inject(e, env, bstore), Set())
}
