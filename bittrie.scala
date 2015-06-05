import leon.lang._
import leon.collection._
import leon._

/**
 * Bit-Trie Tree Data Structure
 * Ioannis Lamprou
 * SAV 2015
 */

object BitTrieTree{

abstract class BitTrie {
	
	// Main functionality
	
	def findValue(s: List[Bit]): (Option[BigInt], Boolean) = {
  	require(this.allLeafsAreWords()/* && this.positiveValues */)
		this match{
			case Empty => (None(), false)
			case Node(l, v, r) =>
				s match{
					case Nil() => (v, true)
					case Cons(Zero, t) => l.findValue(t)  
					case Cons(One, t) => r.findValue(t)
				}
		}
	} ensuring{ res =>
	          (/*!(this.allWords(Nil()) contains s) &&*/ res._2 == false) ||  // string not in
	          (/*(this.allWords(Nil()) contains s) &&*/ res._2 == true && ((res._1).isInstanceOf[None[BigInt]])) || // string in and None()
	          (/*(this.allWords(Nil()) contains s) &&*/ res._2 == true && !((res._1).isInstanceOf[None[BigInt]]) && (this.contents contains (res._1).getOrElse(0)) ) // string in and Some(n)
	}
	
	// insert new string/value; if already in, then update value
	def insert(s: List[Bit], n: BigInt): BitTrie = {
		require(n > 0 && this.positiveValues && !(this.contents contains n) && this.allLeafsAreWords /* && this.noDuplicateValues */)
		this match{
		  case Empty =>
		    s match{
		      case Nil() => Node(Empty, Some(n), Empty)
		      case Cons(Zero, t) => Node(Empty.insert(t, n), None(), Empty)
		      case Cons(One, t) => Node(Empty, None(), Empty.insert(t, n))
		    }
		  case Node(l, v, r) =>
		    s match{
		      case Nil() => Node(l, Some(n), r)     // case internal/leaf node and no more string: update the value
		      case Cons(Zero, t) => Node(l.insert(t, n), v, r)  // case internal/leaf node and more string: continue in the child
		      case Cons(One, t) => Node(l, v, r.insert(t, n))   //                        << >>
		    }
		}
  }ensuring {res => ((res.findValue(s))._1).getOrElse(0) == n && 
                    res.allLeafsAreWords && 
                    res.positiveValues && 
                    // (res.contentPairs(Nil()) contains (s,n)) &&
                    // this.noDuplicateValues &&
                    (res.contents contains n) &&
                    (res.size() >= this.size()) // &&
                   // (res.numOfWords >= this.numOfWords()) &&
                   // (res.numOfWords() <= this.numOfWords() + 1) &&
                   // ( ((this.findValue(s))._2 == false && res.contents == this.contents ++ Set(n)) 
                   // || ((this.findValue(s))._2 == true && n != ((this.findValue(s))._1).getOrElse(0) && res.contents == this.contents ++ Set(n) -- Set(((this.findValue(s))._1).getOrElse(0))) 
                   // || ((this.findValue(s))._2 == true && n == ((this.findValue(s))._1).getOrElse(0) && res.contents == this.contents )  )
            }
	
	def DELETE(s: List[Bit]): BitTrie = {
	  val output = delete(s, this, List(s.head), 0, this)
	  output._2 match{
	    case None() => output._1
	    case Some((t, l)) => killPath(t, l)
	  }
	}
	
	def delete(s: List[Bit], lastWordOrBranch: BitTrie, path: List[Bit], count: BigInt, start: BitTrie): (BitTrie, Option[(BitTrie, List[Bit])]) = {
	  require(s.size >= 1)
//	  require(s.size >= 1 && ((count > 0 && lastWordOrBranch != Empty) || (lastKey == s.head && lastWordOrBranch == this && count == 0))/* && allLeafsAreWords*/) // initially - maybe use count
		s match{
		    case Cons(Zero, Nil()) => 
		    this match {
		      case Empty => (Empty, None()) // string is not in the tree
		      case Node(l, v, r) => 
		            l match{
		              case Empty => (Node(l, v, r), None())
		              case Node(Empty, v1, Empty) => (Node(Node(Empty, None(), Empty), v, r), Some((start, path)))
		              case Node(l2, v2, r2) => (Node(Node(l2, None(), r2), v, r), None())
		            }
		    } 
		    case Cons(One, Nil()) => 
		    this match {
		      case Empty => (Empty, None()) // string is not in the tree
		      case Node(l, v, r) => 
		            r match{
		              case Empty => (Node(l, v, r), None())
		              case Node(Empty, v1, Empty) => (Node(l, v, Node(Empty, None(), Empty)), Some((start, path)))
		              case Node(l2, v2, r2) => (Node(l, v, Node(l2, None(), r2)), None())
		            }
		     } 
		   case Cons(Zero, t) => 
		    this match{
		      case Empty => (Empty, None()) // string is not in the tree
		      case Node(l, Some(v), r) => 
		        val child = l.delete(t, Node(l, Some(v), r), path ++ List(Zero), 1, start)
		        (Node(child._1, Some(v), r), child._2)
		      case Node(l, None(), Empty) => 
		        val child = l.delete(t, lastWordOrBranch, path, 1, start)
		        (Node(child._1, None(), Empty), child._2)
		      case Node(l, None(), r) => 
		        val child = l.delete(t, Node(l, None(), r), path ++ List(Zero), 1, start)
		        (Node(child._1, None(), r), child._2)
		    }
		  case Cons(One, t) => 
		    this match{
		      case Empty => (Empty, None()) // string is not in the tree
		      case Node(l, Some(v), r) => 
		        val child = r.delete(t, Node(l, Some(v), r), path ++ List(One), 1, start)
		        (Node(l, Some(v), child._1), child._2)
		      case Node(Empty, None(), r) => 
		        val child = r.delete(t, lastWordOrBranch, path, 1, start)
		        (Node(Empty, None(), child._1), child._2)
		      case Node(l, None(), r) => 
		        val child = r.delete(t, Node(l, None(), r), path ++ List(One), 1, start)
		        (Node(l, None(), child._1), child._2)
		    }
		  }	
	      
//	} ensuring { res => 
//	  !(res.allWords(Nil()) contains s) &&
//	  (res.numOfWords() <= this.numOfWords()) &&
 //   (res.numOfWords() >= this.numOfWords() - 1) // &&allLeafsAreWords
	}
  
  
  
  def killPath(s: BitTrie, path: List[Bit]): BitTrie = {
 //   require(path.size >= 1 && s != Empty)
    s match{
      case Node(l, v, r) =>
        path match{
          case Cons(Zero, Nil()) => Node(Empty, v, r)
          case Cons(One, Nil()) => Node(l, v, Empty)
          case Cons(Zero, t) => Node(killPath(l, t), v, r)
          case Cons(One, t) => Node(l, v, killPath(r, t))        
        }
    } 
  }
  
  // ---------------------------------------------------------------------------------------------------------------------
	// Functions gathering content
	
	def contents(): Set[BigInt] = {
	  this match{
	    case Empty => Set()
	    case Node(l, v, r) =>
		v match{
			case None() => l.contents() ++ r.contents()
			case Some(vl) => Set(vl) ++ l.contents() ++ r.contents()
		}
	  }
	}
	
	def contentsList(): List[BigInt] = {
	  this match{
	    case Empty => Nil()
	    case Node(l, v, r) =>
		  v match{
			  case None() => l.contentsList() ++ r.contentsList()
			  case Some(vl) => List(vl) ++ l.contentsList() ++ r.contentsList()
		  }
	  }
	}
	
	def allWords(prefix: List[Bit]): List[List[Bit]] = {
	  this match{
	    case Empty => List()
	    case Node(l, None(), r) =>  l.allWords(prefix ++ List(Zero)) ++ r.allWords(prefix ++ List(One))
	    case Node(l, Some(v), r) => List(prefix) ++ l.allWords(prefix ++ List(Zero)) ++ r.allWords(prefix ++ List(One))
	  }
	}
	
	def contentPairs(prefix: List[Bit]): Set[(List[Bit], BigInt)] = {
	  this match{
	    case Empty => Set() //
	    case Node(l, None(), r) => l.contentPairs(prefix ++ List(Zero)) ++ r.contentPairs(prefix ++ List(One))
	    case Node(l, Some(v), r) => Set((prefix, v)) ++ l.contentPairs(prefix ++ List(Zero)) ++ r.contentPairs(prefix ++ List(One))
	  }
	}
	
	def numOfWords(): BigInt = {
	  setToList(this.contents).size
	}
	
	def size(): BigInt = {
   this match {
     case Empty => BigInt(0)
     case Node(l, v, r) => BigInt(1) + l.size + r.size
     }
   }
	
	// -------------------------------------------------------------------------------------------------------------------------------
  // Properties' functions
  
  def allLeafsAreWords(): Boolean = {
    this match{
      case Empty => true
      case Node(Empty, v, Empty) =>
        v match{
          case None() => false
          case Some(v) => true
        }
      case Node(l, v, r) => l.allLeafsAreWords && r.allLeafsAreWords
    }
  }
  
  def positiveValues(): Boolean = {
     this match{
       case Empty => true
       case Node(l, None(), r) => l.positiveValues && r.positiveValues
       case Node(l, Some(v), r) => (v > 0) && l.positiveValues && r.positiveValues
     }
   }
   
   def noDuplicateValues(): Boolean = {
     (this.contentsList.size == setToList(this.contents).size)
   }
}

// Data types definitions

case object Empty extends BitTrie
case class Node(l: BitTrie, v: Option[BigInt], r: BitTrie) extends BitTrie // v is None() for root and (some) intermediate nodes

abstract class Bit
case object One extends Bit
case object Zero extends Bit
}
