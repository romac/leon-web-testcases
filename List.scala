package simple

import leon.lang._
import leon.annotation._

object list {

/** List class */
sealed abstract class List {

  def size : BigInt = (this match {
    case Nil => BigInt(0)
    case Cons(_, xs) => 1 + xs.size
  }) ensuring(_ >= 0)

  def contents: Set[BigInt] = this match {
    case Nil => Set.empty
    case Cons(x,xs) => xs.contents ++ Set(x)
  }

  def isSorted: Boolean = this match {
    case Nil => true
    case Cons(x, Nil) => true
    case Cons(x, Cons(y, ys)) => x <= y && Cons(y, ys).isSorted
  }

  /* Inserting element 'e' into a sorted list 'l' produces a sorted list with
   * the expected content and size */
  def sortedIns(e: BigInt): List = {
    require(this.isSorted)
    this match {
      case Nil => Cons(e,Nil)
      case Cons(x, xs) => if (x <= e) Cons(x, xs.sortedIns(e)) else Cons(e, this)
    }
  } ensuring(res => res.contents == this.contents ++ Set(e) 
                    && res.isSorted
                    && res.size == this.size + 1
            )

}

case class Cons(head:BigInt, tail:List) extends List
case object Nil extends List

}

