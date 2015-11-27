import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object Types {
  abstract class Type
  case object IntType extends Type
  case object BoolType extends Type
}
