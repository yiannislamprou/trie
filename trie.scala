import leon.lang._
import leon.collection._
import leon._

/**
 * Trie Tree Data Structure
 * Ioannis Lamprou
 * SAV 2015
 */

object TrieTree{

abstract class Trie {
	
	val WordLengthBound = BigInt(1)	//
	val NumOfChildren = BigInt(1) //
	
// Main functions 	
	
	def findValue(s: List[Char]): (Option[BigInt], Boolean) = {
		//require(/* s.size <= WordLengthBound && this.size <= 1 && NoEmptyChild && this.getChildren().size <= NumOfChildren*/ )
		this match{
			case Empty => (None(), false)
			case Node(v, children) =>
				s match{
					case Nil() => (v, true) //  v is an Option already
					case Cons(h, t) => findInList(h, children).findValue(t)  
				}
		}
	} ensuring{ res => // 3 periptwseis - string oxi mesa kai res None; string mesa alla me value none; string mesa me value some
	          (/*!(this.allWords(Nil()) contains s) &&*/ res._2 == false) ||
	          (/*(this.allWords(Nil()) contains s) &&*/ res._2 == true && ((res._1).isInstanceOf[None[BigInt]])) ||
	          (/*(this.allWords(Nil()) contains s) &&*/ res._2 == true && !((res._1).isInstanceOf[None[BigInt]]) && (this.contents contains (res._1).getOrElse(0)) /*&& (setToList(contentPairs(Nil())) contains((s, (res._1).getOrElse(0)) )) */)
	}
	
	def findInList(c: Char, l: List[(Char, Trie)]): Trie = {
//	  require(NoEmptySecond(l))
	  l match {
	    case Nil() => Empty
	    case Cons((c, t), tt) => t
	    case Cons(h, t) => findInList(c, t)
	  }
//	}	ensuring{
//	   res => ((first(l) contains c)/* && res != Empty*/) || (!(first(l) contains c)/* && res == Empty*/)
	}
	
		// insert new string/value; if already in, then update value
	def insert(s: List[Char], n: BigInt): Trie = {
		require(s.size <= WordLengthBound) //
		this match{
		  case Empty =>
		    s match{
		      //case Nil() => Empty
		      case Nil() => Node(Some(n), List[(Char, Trie)]())
		      case Cons(h, t) => Node(None(), List((h, Empty.insert(t, n))))
		    }
		  case Node(v, children) =>
		    s match{
		      case Nil() => Node(Some(n), children)     // case internal/leaf node and no more string: update the value
		      case Cons(h, t) =>
		        val child = findInList(h, children)
		        child match{
		          case Empty => Node(v, children ++ List((h, child.insert(t, n))))
		          case tree => Node(v, children -- List((h, child)) ++ List((h, child.insert(t, n))))
		        }
		      // case internal/leaf node and more string: continue in the child
		    }
		}
  }ensuring {res => ((res.findValue(s))._1).getOrElse(0) == n// (setToList(res.contentPairs(Nil())) contains (s,n)) && 
                   // (res.numOfWords() >= this.numOfWords()) &&
                   // (res.numOfWords() <= this.numOfWords() + 1)
            }
  
// Delete

  def DELETE(s: List[Char]): Trie = {
    require(s.size >= 1 && allLeafsAreWords && positiveValues && NoEmptyChild)
	  
	  val output = delete(s, this, List(s.head), this)
	  output._2 match{
	     case None() => output._1
	     case Some((t, l)) => this.killPath(t, l)
	  }
	 } ensuring{ res =>   (((res.findValue(s))._2) == false) && 
	                    // !(res.allWords(Nil()) contains s) &&
                      // (res.numOfWords() <= this.numOfWords()) &&
                      // (res.numOfWords() >= this.numOfWords() - 1) &&
                      // res.NoEmptyChild &&
	                    allLeafsAreWords &&
	                    positiveValues &&
	                    res.size <= this.size
	  }
  
	def delete(s: List[Char], lastWordOrBranch: Trie, path: List[Char], start: Trie): (Trie,Option[(Trie, List[Char])]) = { 
	  require(s.size >= 1 && allLeafsAreWords && positiveValues && path.size >= 1 && NoEmptyChild)
	  
	  s match{
		    case Cons(h, Nil()) => 
		    this match {
		      case Empty => (Empty, None()) // string is not in the tree
		      case Node(v, ch) => 
		          val child = findInList(h, ch)
		          child match{
		            case Empty => (Node(v, ch), None()) // not in the tree
		            case Node(v1, ch1) => 
		              if(ch1.size == 0){
		                if(ch.size <= 1)
		                  (Node(v, ch -- List((h, child)) ++ List((h, Node(None(), ch1)))), Some((lastWordOrBranch, path ++ List(h))))  // leaf -> return info upwards
		                else
		                  (Node(v, ch -- List((h, child)) ++ List((h, Node(None(), ch1)))), Some((this, path ++ List(h))))
		              }
		              else  
		                (Node(v, ch -- List((h, child))++ List((h, Node(None(), ch1)))), None()) // internal node - update value to None
		            }
		    } 
		   case Cons(h, t) => 
		    this match{
		      case Empty => (Empty, None()) // string is not in the tree
		      case Node(Some(v), ch) =>  // new last value
		        val child = findInList(h, ch)
		        val childUpd = child.delete(t, Node(Some(v), ch), path ++ List(h), start)
		        (Node(Some(v), ch ++ List((h, childUpd._1)) -- List((h, child))), childUpd._2)
		      case Node(None(), ch) => 
		        val child = findInList(h, ch)
		        if (ch.size <= 1){
		          val childUpd = child.delete(t, lastWordOrBranch, path ++ List(h), start)
		          (Node(None(), ch ++ List((h, childUpd._1)) -- List((h, child))), childUpd._2)
		        }
		        else {// new last branch
		          val childUpd = child.delete(t, Node(None(), ch), path ++ List(h), start)
		          (Node(None(), ch ++ List((h, childUpd._1)) -- List((h, child))), childUpd._2)
		        }
		    }
	  }
	      
	} ensuring { res => allLeafsAreWords && 
	                    positiveValues && 
	                    // noDuplicateValues &&
                      ((res._2.isInstanceOf[None[(Trie, List[Char])]] && (((res._1.findValue(s))._2) == false)) || (!res._2.isInstanceOf[None[(Trie, List[Char])]] && start.notEmptyPathTo((res._2.getOrElse((Empty, Nil())))._1, (res._2.getOrElse((Empty, Nil())))._2)))
	}
	
	
   def killPath(s: Trie, path: List[Char]): Trie = {
    require(path.size >= 1 && notEmptyPathTo(s, path) && allLeafsAreWords && positiveValues)
    this match{
      case Node(v, ch) =>
        if (s == this)
            path match{
              case Cons(h, t) => 
                val child = findInList(h, ch)
                Node(v, ch -- List((h, child)))
            }
        else
            path match{
              case Cons(h, t) => 
                val child = findInList(h, ch)
                Node(v, ch -- List((h, child)) ++ List((h, child.killPath(s, t))))
            }
      }
  } ensuring{
    res => allLeafsAreWords && positiveValues
  }
	
// -------------------------------------------------------------------------
// Functions gathering content
	
	def contents(): Set[BigInt] = {
	  this match{
	    case Empty => Set()
	    case Node(v, children) =>
        v match{
          case None() => contentsList(children)
          case Some(vl) => Set(vl) ++ contentsList(children)
        }
        
	  }
	}
	
	def contentsList(a: List[(Char, Trie)]): Set[BigInt] = {
	  a match{
	    case Nil() => Set()
	    case Cons((c, t), tail) => t.contents() ++ contentsList(tail)
	  }
	}
	
	def allWords(prefix: List[Char]): List[List[Char]] = {
	  this match{
	    case Empty => Nil()
	    case Node(None(), l) => List(List[Char]()) ++ allWordsList(prefix, l)
	    case Node(Some(v), l) => List(prefix) ++ allWordsList(prefix, l)
	  }
	}
	
	def allWordsList(prefix: List[Char], l: List[(Char, Trie)]): List[List[Char]] = {
	  l match{
	    case Nil() => List()
	    case Cons((c, t), tail) => t.allWords(prefix ++ List(c)) ++ allWordsList(prefix, tail)
	  }
	}
	
	def contentPairs(prefix: List[Char]): Set[(List[Char], BigInt)] = {
	  this match{
	    case Empty => Set()
	    case Node(None(), l) => contentPairsList(prefix, l)
	    case Node(Some(v), l) => Set((prefix, v)) ++ contentPairsList(prefix, l)
	  }
	}
	
	def contentPairsList(prefix: List[Char], l: List[(Char, Trie)]): Set[(List[Char], BigInt)] = {
	  l match{
	    case Nil() => Set()
	    case Cons((c, t), tail) => t.contentPairs(prefix ++ List(c)) ++ contentPairsList(prefix, tail)
	  }
	}
	
	def numOfWords(): BigInt = {
	  setToList(this.contentPairs(Nil())).size
	}
	
	def size(): BigInt = {
	  this match {
	    case Empty => BigInt(0)
	    case Node(v, t) => BigInt(1) + sizeList(second(t))
	  }
	}
	
	def sizeList(l: List[Trie]): BigInt = {
	  l match{
	    case Nil() => BigInt(0)
	    case Cons(c, t) => c.size + sizeList(t)
	  }
	}
	
// ------------------------------------------------------------------------------
// Properties' functions
  
  def allLeafsAreWords(): Boolean = {
    this match{
      case Empty => true
      case Node(v, Nil()) =>
        v match{
          case None() => false
          case Some(v) => true
        }
      case Node(v, ch) => allLeafsList(ch)
    }
  }
  
  def allLeafsList(l: List[(Char, Trie)]): Boolean = {
    l match{
      case Nil() => true
      case Cons((h,t), tt) => t.allLeafsAreWords()
    }  
  }
  
  def NoEmptyChild(): Boolean = {
	  this match{
	    case Empty => true
	    case Node(v, ch) => if (second(ch) contains Empty) false else NoEmptyChildList(ch)
	  }
	}
	
	def NoEmptyChildList(ch: List[(Char, Trie)]): Boolean = {
	  ch match {
	    case Nil() => true
	    case Cons((c,t), tt) => t.NoEmptyChild() && NoEmptyChildList(tt)
	  }
	}
	
	def NoEmptySecond(ch: List[(Char, Trie)]): Boolean = {
	  ch match{
	    case Nil() => true
	    case Cons((c,Empty), tt) => false
	    case Cons(h, t) => NoEmptySecond(t)
	  }
	}
  
  def positiveValues(): Boolean = {
     this match{
       case Empty => true
       case Node(None(), ch) => positiveValuesList(ch)
       case Node(Some(v), ch) => (v > 0) && positiveValuesList(ch)
     }
   }
   
  def positiveValuesList(l: List[(Char,Trie)]): Boolean = {
     l match{
       case Nil() => true
       case Cons((h, t), tt) => t.positiveValues() && positiveValuesList(tt)
     }
   }
  
  def notEmptyPathTo(s: Trie, p: List[Char]): Boolean = {
     this match{
       case Empty => false
       case Node(v, ch) =>
        if(s == this) 
          if(p.size >= 1) true else false // need to know which child to kill
        else
            p match{
              case Nil() => false 
              case Cons(h, t) => findInList(h,ch).notEmptyPathTo(s, t)
            }
      }
   }
  
  // -------------------------------------------------------------------------
  // Auxiliary functions
  
  def getValue(): Option[BigInt] = {
    this match{
      case Empty => None()
      case Node(v, t) => v
    }
  }
  
	def getChildren() : List[(Char, Trie)] = {
	  this match{
	    case Empty => Nil()
	    case Node(v, ch) => ch
	  }
	}
	
	def first(l: List[(Char, Trie)]) : List[Char] = {
	  l match{
	    case Nil() => Nil()
	    case Cons((c,t), tt) => Cons(c, first(tt))
	  }
	}
	
	def second(l: List[(Char, Trie)]) : List[Trie] = {
	  l match {
	    case Nil() => Nil()
	    case Cons((c,t), tt) => Cons(t, second(tt))
	  }
	}
	
}

// ----------------------------------------------------------------------------------
// Case Definitions

case object Empty extends Trie
case class Node(v: Option[BigInt], children: List[(Char, Trie)]) extends Trie 
// v is None() for root and (some) intermediate nodes

}
