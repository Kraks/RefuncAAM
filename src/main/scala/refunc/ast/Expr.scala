package refunc.ast

sealed trait Expr
trait Value extends Expr

case class B(x: String, e: Expr)

case class  Num(i: Int) extends Expr
case class  Var(x: String) extends Expr
case class  App(e1: Expr, e2: Expr) extends Expr
case class  Letrec(bds: List[B], body: Expr) extends Expr
case class  Lam(x: String, body: Expr) extends Value
case class  If0(cnd: Expr, thn: Expr, els: Expr) extends Expr

// not used for now
case class  PrimOp(op: Symbol, e1: Expr, e2: Expr) extends Expr
case class  Let(x: String, e: Expr, body: Expr) extends Expr
