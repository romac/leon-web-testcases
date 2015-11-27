import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object Tokens {
  abstract class Token
  case object TPlus extends Token
  case object TTimes extends Token
  case object TLT extends Token
  case object TIf extends Token
  case object TElse extends Token
  case object TLAnd extends Token
  case object TLOr extends Token
  case object TLeftBrace extends Token
  case object TRightBrace extends Token
  case object TLeftPar extends Token
  case object TRightPar extends Token
  case class TInt(v: Int) extends Token
  case class TId(name: Int) extends Token // All variables are : Int
}
