package simple

import leon.lang._
import leon.annotation._

// Hello, world
object Sort {

  import list._

  /* Insertion sort yields a sorted list of same size and content as the input
   * list */
  def sort(l: List): List = (l match {
    case Nil => Nil
    case Cons(x,xs) => sort(xs).sortedIns(x)
  }) ensuring(res => res.contents == l.contents 
                     && res.isSorted
                     && res.size == l.size
             )

  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil))))))

    // println(ls)
    // println(sort(ls))
  }

}

