package scalare.regex.pderiv

import collection.immutable.IntMap
import annotation.tailrec


object PDeriv {

abstract class RE {
}

case object Phi extends RE 

case object Empty extends RE

case class Label(c: Char) extends RE

case class Choice(r1: RE, r2: RE) extends RE 

case class Pair(r1: RE, r2: RE) extends RE
case class Star(r:RE) extends RE

// check whether \epsilon \in r
def isEmpty(r:RE) : Boolean = r match {
  case Phi           => false
  case Empty         => true
  case Label(_)      => false
  case Choice(r1,r2) => isEmpty(r1) || isEmpty(r2)
  case Pair(r1,r2)   => isEmpty(r1) && isEmpty(r2)
  case Star(r) 	     => true
}

// partial derivative
def pderiv (c:Char) (r:RE) : List[RE] = r match {
  case Phi   => List()
  case Empty => List()
  case Label(c_) => if (c == c_) List(Empty) else List()
  case Choice(r1,r2) => pderiv(c)(r1) ++ pderiv(c)(r2)
  case Pair(r1,r2) => 
    if (isEmpty(r1)) {
      (for (r1_ <- pderiv(c)(r1))
      yield Pair(r1_,r2) ) ++ (pderiv(c)(r2))
    } else {
      (for (r1_ <- pderiv(c)(r1))
      yield Pair(r1_,r2) ) 
    }
  case Star(r) => 
    for (r_ <- pderiv(c)(r)) yield Pair(r_,Star(r))
}

// partial derivative for list of RE
def pderivList (c:Char) (rs:List[RE]) : List[RE] = 
  rs.flatMap( r => pderiv(c)(r) ) // flatMap is like concatMap in Haskell

// (a|b)*
val r = Star(Choice(Label('a'),Label('b')))

def isIn(s:String)(r:RE) : Boolean = {
  val fins  = (List(r) /: s.toList) ((x,y) => pderivList(y)(x))
  fins.exists( x => isEmpty(x))
}

// computes the set of symbols in a regular expression
def sigmaRE(r:RE):Set[Char] = r match {
  case Phi           => Set()
  case Empty         => Set()
  case Label(c)      => Set(c)
  case Choice(r1,r2) => sigmaRE(r1) ++ sigmaRE(r2)
  case Pair(r1,r2)   => sigmaRE(r1) ++ sigmaRE(r2)
  case Star(r)       => sigmaRE(r)
}

abstract class Pat {
}

case class PVar(v:Int, w:List[(Int,Int)], p:Pat) extends Pat

case class PRE(r:RE)  extends Pat 

case class PChoice(p1:Pat, p2:Pat) extends Pat

case class PPair(p1:Pat, p2:Pat) extends Pat

case class PStar(p:Pat) extends Pat 

case class PEmpty(p:Pat) extends Pat


// turns pattern into regular expression
def strip(p : Pat) : RE = p match {
  case PVar(_, _, p) => strip(p)
  case PRE(r) => r
  case PPair(p1,p2) => Pair(strip(p1), strip(p2))
  case PStar(p) => Star(strip(p))
  case PChoice(p1,p2) => Choice(strip(p1),strip(p2))
  case PEmpty(_) => Empty
}

def mkEmpty(p: Pat) : Pat = p match {
  case PVar(v, r, p) => PVar(v,r,mkEmpty(p))
  case PRE(r) => if (isEmpty(r)) { PRE(Empty) } else { PRE(Phi) }
  case PPair(p1,p2) => PPair(mkEmpty(p1), mkEmpty(p2))
  case PStar(p) => PRE(Empty)
  case PChoice(p1,p2) => PChoice(mkEmpty(p1),mkEmpty(p2))
  case PEmpty(_) => p  
}

def include(rs:List[(Int,Int)])(idx:Int) : List[(Int,Int)] = rs match {
  case Nil => List((idx,idx))
  case ((b,e)::rest) => 
    if (idx == (e + 1)) { (b,e+1)::rest } else { (idx,idx)::rs }
} 

def nub[A](l:List[A]) : List[A] = l.toSet.toList


// only computes the symbol partial derivatives
def pdPat(l:(Char,Int)) (p:Pat) : List[Pat] = l match {
  case (c,idx) => 
    p match {
      case PVar(v, r, p) => 
	val pds = pdPat(l)(p)
	for (pd <- pds) yield PVar(v, include(r)(idx), pd)
      case PRE(r) => 
	val pds = pderiv(c)(r)
        for (pd <- pds) yield PRE(pd)
      case PPair(p1,p2) =>
	if (isEmpty(strip(p1))) {
	  val ep1 = mkEmpty(p1)
	  nub((for (p1p <- pdPat(l)(p1)) yield PPair(p1p,p2)) 
	      ++
	      (for (p2p <- pdPat(l)(p2)) yield PPair(ep1,p2p)))
	} else {
	  (for (p1p <- pdPat(l)(p1)) yield PPair(p1p,p2))
	}
      case PStar(q) =>
	val pds = pdPat(l)(q)
	for (pd <- pds) yield PPair(pd,p)
      case PChoice(p1,p2) =>
	nub(pdPat(l)(p1) ++ pdPat(l)(p2))
    }
} 

case class Binder(m:IntMap[List[(Int,Int)]]) 


def fst[A,B](p:(A,B)):A = p match {
  case (x,y) => x 
}

// nubBy the first component
def nub2[A,B](pfs:List[(A,B)]) : List[(A,B)] = {
  val (l,_) = (((List():List[(A,B)]),(Map():Map[A,B])) /: pfs) ((lm, pf) => (lm,pf) match {  // the type annotation List[(A,B)] is necessary
      case ((l,m),(p,f)) => 
	if (m.contains(p)) (l,m)
	else (l++List((p,f)), m.+((p,f)))
    })
  l
}

// todo  : try mutable Map
@inline def updateByIndex(x:Int)(pos:Int)(b:Binder) : Binder = b match {
  
  case Binder(m) => 
    val r = m.get(x) match {
      case None => List( (pos,pos) )
      case Some(l) => l match {
	case (b,e)::rs => 
	  if (pos == (e + 1)) (b,pos)::rs
	  else (if (pos > (e + 1)) (pos,pos)::l 
	       else sys.error("updateByIndex: this is not possible.")) 
	case Nil =>
	  (pos,pos)::l
      }
    }
    val n = m.updated(x,r)
    Binder(n) 
    // m.put(x,r)
    // Binder(m)
} 


def pdPat0(l:(Char,Int)) (p:Pat) : List[(Pat,Int => Binder => Binder)] = l match {
  case (c,idx) => 
    p match {
      case PVar(v, r, p) => 
	val pdfs = pdPat0(l)(p)
        def g(j:Int):Binder=>Binder = (b:Binder) => updateByIndex(v)(j)(b)
	for ((pd,f) <- pdfs) yield (PVar(v, r, pd), (i:Int) => ((b:Binder) => f(i)(g(i)(b)))) // \i -> (f i) . (g i)
      case PRE(r) => 
	val pds = pderiv(c)(r)
        for (pd <- pds) yield (PRE(pd), ((i:Int) => (b:Binder) => b))
      case PPair(p1,p2) =>
	if (isEmpty(strip(p1))) {
	  val ep1 = mkEmpty(p1)
	  nub2((for ((p1p,f) <- pdPat0(l)(p1)) yield (PPair(p1p,p2),f)) 
	      ++
	      pdPat0(l)(p2))
	} else {
	  (for ((p1p,f) <- pdPat0(l)(p1)) yield (PPair(p1p,p2),f))
	}
      case PStar(q) =>
	val pdfs = pdPat0(l)(q)
	for ((pd,f) <- pdfs) yield (PPair(pd,p),f)
      case PChoice(p1,p2) =>
	nub2(pdPat0(l)(p1) ++ pdPat0(l)(p2))
    }
} 


// collect sub string from the input string based on the range
def rg_collect(w:String)(r:(Int,Int)):String = r match {
  case (i,j) => w.drop(i).take(j - i + 1)
}

/*
 * We compile all the possible partial derivative operation into a table.
 * The table maps key to a set of target interger states and their corresponding binder update functions
 * */
// the pd table
type PdPatTable = Map[(Int,Char),List[(Int, Int => Binder => Binder)]]


// Some helper functions used in buildPdPat0Table

def builder(sig:Set[(Char,Int)]) (acc_states:List[Pat]) (acc_delta:List[(Pat,(Char,Int), List[(Pat,Int=>Binder=>Binder)])]) (curr_states:List[Pat]) (dict:Map[Pat,Int]) (max_id:Int) : (List[Pat], List[(Pat,(Char,Int), List[(Pat,Int=>Binder=>Binder)])], Map[Pat,Int]) = curr_states match {
  case Nil => (acc_states, acc_delta, dict)
  case _   => 
    val all_states_sofar = acc_states ++ curr_states
    val new_delta = for (s <- curr_states; l <- sig) yield (s,l, pdPat0(l)(s))
    val new_states = nub(for ((_,_,sfs) <- new_delta; (s,f) <- sfs; if !(dict.contains(s))) yield s)
    val acc_delta_next = acc_delta ++ new_delta
    val (dictp,max_idp) = ( (dict,max_id) /: new_states ) ( 
	  (did, p) => did match { case (d,id) => (d.updated(p,id), id+1) }
	)
    builder(sig)(all_states_sofar)(acc_delta_next)(new_states)(dictp)(max_idp)
}

def mapping(dictionary:Map[Pat,Int])(x:Pat):Int = {
  dictionary.get(x) match {
    case None => sys.error("mapping: key missed, this should not happen." ++ "\n" ++ dictionary.toString ++ "\n" ++ x.toString)
    case Some(i) => i
  }
}
  

// a function that builds the above table from the pattern

def buildPdPatTable(init:Pat):(PdPatTable, List[Int]) = {
  val sig = sigmaRE(strip(init)).map(x => (x,0))
  val init_dict = Map( init -> 0 )
  val (all, delta, dictionary) = builder(sig)(List())(List())(List(init))(init_dict)(1) // all states and delta
  val finals = for (s <- all; if isEmpty(strip(s))) yield s
  val sfinals = finals.map(p => mapping(dictionary)(p))
  val lists = for ((p,l,qfs) <- delta; 
		   val i = mapping(dictionary)(p); 
		   val jfs = qfs.map( qf => qf match 
				     { case (q,f) => (mapping(dictionary)(q), f) } )) 
	      yield (i,l,jfs) 
  val hash_table = ((Map():PdPatTable) /: lists) ( (dict, pxq) => pxq match 
				     { case (p,x,q) => 
				       val k = (p,fst(x))
				       dict.get(k) match 
				       { case None => dict.updated(k,q)
					 case Some(ps) => sys.error("buildPdPatTable: found a duplicate key in the pdPatTable, this should not happen.")
				       }
				     } )
  (hash_table,sfinals)
}

/* Optimized lookup pdpat table.
 * build a hash table that map [ Int ]  states + label  to [ Int ] states where 
 * the resulting [ Int ] is already nubbed and join, hence there is no need to run the pairing and nubbing on the fly.
 * This would cause some compile time overhead and trading space with time.
 */

type NFAStates = List[Int]

/*
type DPatTable = Map[(Int,Char), (Int, NFAStates, Map[Int, List[Int => Binder => Binder]])]
type DPKey = (Int,Char)
@inline def mhash(p:(Int,Char)):DPKey = p
@inline def emptyDPT:DPatTable = Map()
@inline def getDPT(d:DPatTable)(k:DPKey):Option[(Int, NFAStates, Map[Int, List[Int => Binder => Binder]])] = { 
  d.get(k) 
}
@inline def updateDPT(d:DPatTable)(k:DPKey)(v:(Int, NFAStates, Map[Int, List[Int => Binder => Binder]])):DPatTable = {
  d.updated(k, v)
}
*/


type DPatTable = IntMap[(Int, NFAStates, Map[Int, List[Int => Binder => Binder]])]
type DPKey = Int
@inline def mhash(p:(Int,Char)):DPKey = p match {
  case (i,c) => i + c.toInt * 256
}
@inline def emptyDPT:DPatTable = IntMap()
@inline def getDPT(d:DPatTable)(k:DPKey):Option[(Int, NFAStates, Map[Int, List[Int => Binder => Binder]])] = { 
  d.get(k) 
}
@inline def updateDPT(d:DPatTable)(k:DPKey)(v:(Int, NFAStates, Map[Int, List[Int => Binder => Binder]])):DPatTable = {
  d.updated(k, v)
}
/* minor speed up
import java.util.HashMap
type DPatTable = HashMap[Int, (Int, NFAStates, Map[Int, List[Int => Binder => Binder]])]
type DPKey = Int
@inline def mhash(p:(Int,Char)):DPKey = p match {
  case (i,c) => i + c.toInt * 256
}
@inline def emptyDPT:DPatTable = new HashMap()

@inline def getDPT(d:DPatTable)(k:DPKey):Option[(Int, NFAStates, Map[Int, List[Int => Binder => Binder]])] = { 
  if (d.containsKey(k)) {
    Some(d.get(k))
  } else {
    None
  }
}
@inline def updateDPT(d:DPatTable)(k:DPKey)(v:(Int, NFAStates, Map[Int, List[Int => Binder => Binder]])):DPatTable = {
  d.put(k,v)
  d
}
*/
def mappingp(dictionary:Map[NFAStates, Int])(x:NFAStates) : Int = {
  dictionary.get(x) match {
    case Some(i) => i
    case None => sys.error("mappingp:key missed.")
  }
}

def lookupPdPat(hash_table:PdPatTable)(i:Int)(li:(Char,Int)): List[(Int,(Int, Int=>Binder=>Binder))] = li match 
{ 
  case (l,j) =>
    val k = (i,l)
    hash_table.get(k) match {
      case Some(pairs) =>
	pairs.map( jop => jop match 
		  { case (j,op) => (j, (i, op))
		  } )
      case None => List()
    }
} 

def builderp(pdStateTable:PdPatTable)(sig:Set[(Char,Int)])(acc_states:List[NFAStates])(acc_delta:List[(NFAStates, (Char,Int), NFAStates, Map[Int, List[Int => Binder => Binder]])])(curr_states:List[NFAStates])(dict:Map[NFAStates,Int])(max_id:Int) : (List[NFAStates], List[(NFAStates,(Char,Int),NFAStates,Map[Int,List[Int => Binder => Binder]])], Map[NFAStates,Int]) = curr_states match 
{
  case Nil => (acc_states,acc_delta,dict)
  case _   => 
    val all_states_sofar = acc_states ++ curr_states
    def insert(k:Int)(f:Int => Binder => Binder)(im:Map[Int, List[Int => Binder => Binder]]) = im.get(k) match {
      case None => im.updated(k,List(f))
      case Some(fs) => im.updated(k,fs++List(f))
    }
    val (new_delta:List[(NFAStates, (Char,Int), NFAStates, Map[Int, List[Int => Binder => Binder]])]) = curr_states.flatMap( curr_state => 
      sig.map( l => { 
	val pairs = nub2(curr_state.flatMap( n_state => lookupPdPat(pdStateTable)(n_state)(l)))
	val (next_state, (curr_state_and_f_pairs:List[(Int,Int=>Binder=>Binder)])) = pairs.unzip
	val f_dict = ((Map():Map[Int, List[Int => Binder => Binder]]) /: curr_state_and_f_pairs)( (im, lf) => 
	  lf match {
	    case (l,f) => insert(l)(f)(im)
	  })
	(curr_state, l, next_state, f_dict)}))
    val new_states = nub(for ((_,_,next_state,_) <- new_delta; if !(dict.contains(next_state))) yield next_state)
    val acc_delta_next = acc_delta ++ new_delta
    val (dictp,max_idp) = ((dict,max_id) /: new_states) ( (did,p) =>
      did match {
	case (d,id) => (d.updated(p,id), id + 1)
      })
    builderp(pdStateTable)(sig)(all_states_sofar)(acc_delta_next)(new_states)(dictp)(max_idp)
}

// todo optimization
def buildDPatTable(init:Pat):(DPatTable,List[Int]) = {
  val sig = sigmaRE(strip(init)).map(x => (x,0))
  val init_dict = Map( init -> 0 )
  val (all, delta, dictionary) = builder(sig)(List())(List())(List(init))(init_dict)(1) // all states and delta
  val finals = for (s <- all; if isEmpty(strip(s))) yield s
  val sfinals = finals.map(p => mapping(dictionary)(p))
  val lists = for ((p,l,qfs) <- delta; 
		   val i = mapping(dictionary)(p); 
		   val jfs = qfs.map( qf => qf match 
				     { case (q,f) => (mapping(dictionary)(q), f) } )) 
	      yield (i,l,jfs) 
  val hash_table = ((Map():PdPatTable) /: lists) ( (dict, pxq) => pxq match 
				     { case (p,x,q) => 
				       val k = (p,fst(x))
				       dict.get(k) match 
				       { case None => dict.updated(k,q)
					 case Some(ps) => sys.error("buildPdPatTable: found a duplicate key in the pdPatTable, this should not happen.")
				       }
				     } )
  // building the DFA
  val initp = List(0)
  val init_dictp = Map(initp -> 0)
  val (allp, deltap, dictionaryp) = builderp(hash_table)(sig)(List())(List())(List(initp))(init_dictp)(1)
  val listp = deltap.map( clnf => clnf match {
    case (c,l,n,f) =>
      val i = mappingp(dictionaryp)(c)
      val j = mappingp(dictionaryp)(n)
      (i,l,j,n,f)
  })
  val hash_tablep = (emptyDPT /: listp)( (dictp,iljnf) => iljnf match {
    case (i,l,j,n,f) => 
      val k = mhash((i,fst(l)))
      getDPT(dictp)(k) match {
	case Some(ps) => sys.error("buildPdPatTable: found a duplicate key in the pdPatTable, this should not happen.")
	case None => updateDPT(dictp)(k)((j,n,f))
      }
  })
  (hash_tablep, sfinals)
}


@inline def computeBinders(currNfaStateBinders:List[(Int,Binder)])(fDict:Map[Int,List[Int=>Binder=>Binder]])(cnt:Int):List[Binder] = {
  @inline def k(a:List[Binder])(imb:(Int,Binder)):List[Binder] = imb match {
    case (m,b) => fDict.get(m) match {
      case None => a
      case Some(gs) => a ++ (gs.map(g => g(cnt)(b)))
    }
  }
  @inline def cm(bs:List[(Int,Binder)]):List[Binder] = ((List():List[Binder]) /: bs)((x,y) => k(x)(y))
  cm(currNfaStateBinders)
}



@tailrec
def patMatches(cnt:Int)(dStateTable:DPatTable)(wp:String)(currDfaNfaStateBinders:(Int,List[(Int,Binder)])) : (Int,List[(Int,Binder)]) = { 
  currDfaNfaStateBinders  match 
  {
    case (i,Nil) => (i,Nil)
      case (i,currNfaStateBinders)   => 
	if (wp.length == 0) { currDfaNfaStateBinders } 
	else {
	  val l = wp.head /* slow:  val l = wp.toList.head */
	  val w = wp.substring(1)
	  val k = mhash((i,l))
	  getDPT(dStateTable)(k) match {
	    case None => (i,List()) // "key missing" which mans some letter exists in wp but not in pattern p
	    case Some((j,next_nfaStates,fDict)) =>
	      val binders = computeBinders(currNfaStateBinders)(fDict)(cnt)
	      val nextDfaNfaStateBinders = (j,next_nfaStates.zip(binders))
	      val cntp = cnt + 1
	    patMatches(cntp)(dStateTable)(w)(nextDfaNfaStateBinders)
	  }
	}
  }
} 


type Range = (Int,Int)

type Env = List[(Int,String)]

def collectPatMatchFromBinder(w:String)(b:Binder):Env = {
  def listify(b:Binder):List[(Int,List[Range])] = b match {
    case Binder(m) => 
      m.toList.sortWith( (x,y) => fst(x) < fst(y) )
  }
  def collectPatMatchFromBinderp(w:String)(xs:List[(Int,List[Range])]):Env = xs match {
    case Nil => Nil
    case ((x,rs)::rest) => rs match {
      case Nil => (x,"")::(collectPatMatchFromBinderp(w)(rest))
      case _   => (x, ("" /: rs.reverse.map(r => rg_collect(w)(r)))((x,y) => x ++ y))::(collectPatMatchFromBinderp(w)(rest))
    }
  }
  collectPatMatchFromBinderp(w)(listify(b))
}


def toBinder(p:Pat):Binder = {
  def toBinderList(p:Pat):List[(Int,List[Range])] = p match {
    case PVar(i,rs,p) => List((i,rs)) ++ toBinderList(p)
    case PPair(p1,p2) => toBinderList(p1) ++ toBinderList(p2)
    case PStar(p1)    => toBinderList(p1)
    case PRE(r)       => List()
    case PChoice(p1,p2) => toBinderList(p1) ++ toBinderList(p2)
  }
  // Binder(Map() ++ toBinderList(p).toMap)
  Binder(IntMap(toBinderList(p).map( xy => xy match { case (x,y) => x -> y }): _*))
}

def patMatch(p:Pat)(w:String):List[Env] = {
  val (dStateTable,sfinal) = buildDPatTable(p)
  val s = 0
  val b = toBinder(p)
  val e = (s,List((s,b)))
  val (_,allbindersp) = patMatches(0)(dStateTable)(w)(e)
  val allbinders = for (x <- allbindersp; val (i,b) = x; if sfinal.contains(i)) yield b
  allbinders.map(b => collectPatMatchFromBinder(w)(b))
}



def first[A](x:List[A]):Option[A] = 
  x match {
    case Nil => None
    case _   => Some(x.head)
  }


def greedyPatMatch(p:Pat)(w:String):Option[Env] = {
  first(patMatch(p)(w))
}


// our favorite example (x :: (A|AB), y :: (BAA|A), z :: (AC|C))
val p = {
  val px = PVar(1,List(),PRE(Choice(Label('A'),Pair(Label('A'),Label('B')))))
  val py = PVar(2,List(),PRE(Choice(Pair(Label('B'),Pair(Label('A'),Label('A'))), Label('A'))))
  val pz = PVar(3,List(),PRE(Choice(Pair(Label('A'),Label('C')), Label('C'))))
  PPair(px, PPair(py, pz))
}


// Copmilation

def compilePat(p:Pat):(DPatTable,List[Int],Binder) = {
  val (dStateTable,sfinal) = buildDPatTable(p)
  val b = toBinder(p)
  (dStateTable, sfinal, b)
}


def compiledPatMatch(tlb:(DPatTable,List[Int],Binder))(w:String):List[Env] = {
  val (dStateTable,sfinal,b) = tlb
  val s = 0
  val e = (s,List((s,b)))
  val (_,allbindersp) = patMatches(0)(dStateTable)(w)(e)
  val allbinders = for (x <- allbindersp; val (i,b) = x; if sfinal.contains(i)) yield b
  allbinders.map(b => collectPatMatchFromBinder(w)(b))
}

def compiledGreedyPatMatch(tlb:(DPatTable,List[Int],Binder))(w:String):Option[Env] = {
  first(compiledPatMatch(tlb)(w))
}


def charSet(cs:List[Char]):RE = cs.toList match {
  case Nil => Phi
  case x::xs => ((Label(x):RE) /: xs)( (r,c) => Choice(r,Label(c)) )
}


def charRangeList(l:Int)(u:Int):List[Char] = {
  (for (i <- l to u) yield i.toChar).toList
  // ((l to u) map (i => i.toChar)).toList
  /*
  var lst:List[Char] = Nil
  var i = u
  while (i >= u) {
    lst = (i.toChar)::lst
    i= i-1
  }
  lst */
}

val dot = charSet(charRangeList(0)(255)) 

val digit = charSet(charRangeList(48)(57)) 

val char  = charSet(charRangeList(65)(90) ++ charRangeList(97)(122)) 

def repeatPair(r:RE)(n:Int):RE = n match {
  case 0 => Phi
  case 1 => r
  case _ => Pair(r,(repeatPair(r)(n-1)))
}

val usPat = {
  val pSpace = PVar (-1, List(), PRE(Label(' ')))
  val p1 = PVar (1,List(), PRE(Star(dot)))
  val p2 = PVar (2,List(), PRE(Pair(char,char)))
  val p3 = PVar (3,List(), PRE(repeatPair(digit)(5)))
  val p4 = PVar (4,List(), PRE(Choice(Empty, Pair(Label('-'), repeatPair(digit)(4)))))
  PPair(p1,PPair(pSpace,PPair(p2,PPair(pSpace, PPair(p3,p4)))))
}

val s = "Mountain View CA 90410"

}

/*
object Main {
  import PDeriv._
  def main(args:Array[String]) = {
    val lines = scala.io.Source.fromFile(args(0), "utf-8").getLines
    val cp = compilePat(usPat)
    /*
    for (l <- lines) {
      println(compiledGreedyPatMatch(cp)(l))
    }
    */
    while (lines.hasNext) {
      println(compiledGreedyPatMatch(cp)(lines.next()))
    }
  }
}
*/
