import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object Parser {
  import Tokens._
  import Trees._

  def parsePhrase(ts: List[Token]): Option[Expr] = {
    parseGoal(ts) match {
      case Some((res, Nil())) => Some(res)
      case _ => None()
    }
  }

  def parseGoal(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseOr(ts)
  }

  def parseOr(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseAnd(ts) match {
      case Some((lhs, Cons(TLOr, r))) =>
        parseAnd(r) match {
          case Some((rhs, ts2)) => Some((Or(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parseAnd(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseLT(ts) match {
      case Some((lhs, Cons(TLAnd, r))) =>
        parseLT(r) match {
          case Some((rhs, ts2)) => Some((And(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parseLT(ts: List[Token]): Option[(Expr, List[Token])] = {
    parsePlus(ts) match {
      case Some((lhs, Cons(TLT, r))) =>
        parsePlus(r) match {
          case Some((rhs, ts2)) => Some((LessThan(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parsePlus(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseTimes(ts) match {
      case Some((lhs, Cons(TPlus, r))) =>
        parsePlus(r) match {
          case Some((rhs, ts2)) => Some((Plus(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parseTimes(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseLits(ts) match {
      case Some((lhs, Cons(t, r))) if (t == TTimes) =>
        parseTimes(r) match {
          case Some((rhs, ts2)) => Some((Plus(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parseLits(ts: List[Token]): Option[(Expr, List[Token])] = ts match {
    case Cons(TInt(v), r) => Some((IntLiteral(v), r))
    case Cons(TId(v), r) => Some((Var(v), r))
    case Cons(TLeftPar, r) =>
      parseGoal(r) match {
        case Some((e, Cons(TRightPar, ts2))) => Some((e, ts2))
        case _ => None()
      }
    case Cons(TIf, Cons(TLeftPar, r)) =>
      parseGoal(r) match {
        case Some((c, Cons(TRightPar, Cons(TLeftBrace, ts2)))) =>
          // Then
          parseGoal(ts2) match {
            case Some((th, Cons(TRightBrace, Cons(TElse, Cons(TLeftBrace, ts3))))) =>
              // Else
              parseGoal(ts3) match {
                case Some((el, Cons(TRightBrace, ts4))) =>
                  Some((Ite(c, th, el), ts4))
                case _ => None()
              }
            case _ => None()
          }
        case _ => None()
      }
    case _ => None()
  }
}

