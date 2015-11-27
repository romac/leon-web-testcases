import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object Compiler {
  import Tokens._
  import Trees._
  import Types._
  import Parser._
  import TypeChecker._


  def parse(ts: List[Token]): Option[Expr] = {
    parsePhrase(ts)
  } ensuring { _ match {
    case Some(tree) => typeChecks(tree)
    case None()     => true
  }}
}
