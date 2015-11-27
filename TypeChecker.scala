import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object TypeChecker {
  import Trees._
  import Types._

  def typeChecks(e: Expr, exp: Option[Type]): Boolean = e match {
    case Times(l, r)    => (exp.getOrElse(IntType) == IntType)   && typeChecks(l, Some(IntType))  && typeChecks(r, Some(IntType))
    case Plus(l, r)     => (exp.getOrElse(IntType) == IntType)   && typeChecks(l, Some(IntType))  && typeChecks(r, Some(IntType))
    case And(l, r)      => (exp.getOrElse(BoolType) == BoolType) && typeChecks(l, Some(BoolType)) && typeChecks(r, Some(BoolType))
    case Or(l, r)       => (exp.getOrElse(BoolType) == BoolType) && typeChecks(l, Some(BoolType)) && typeChecks(r, Some(BoolType))
    case LessThan(l, r) => (exp.getOrElse(BoolType) == BoolType) && typeChecks(l, Some(IntType))  && typeChecks(r, Some(IntType))
    case Ite(c, th, el) => typeChecks(c, Some(BoolType)) && typeChecks(th, exp) && typeChecks(el, exp)
    case IntLiteral(_)  => exp.getOrElse(IntType) == IntType
    case Var(_)         => exp.getOrElse(IntType) == IntType
  }

  def typeChecks(e: Expr): Boolean = typeChecks(e, None())
}

