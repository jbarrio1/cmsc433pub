// ASSIGNMENT 1 (100 Points)
// Due September 23th 11:59PM

// ----------------------------------------
// PART ONE : DAFNY PROGRAMMING (20 Points)
// ----------------------------------------

// Question 1 (10 points)
//
// You are given the following Dafny datatype, which is equivalent
// to the following OCaml tree type:
//
// type 'a tree = Leaf | Node of ('a * 'a tree * 'a tree)

datatype Tree<T> =
  | Leaf
  | Node (data:T, left: Tree<T>, right:Tree<T>)

/* Implement the `map` and `fold` functions over these trees.

For reference, the OCaml definition would be:

let rec mapTree f t = 
  match t with
  | Leaf -> Leaf
  | Node (x,l,r) -> Node (f x, mapTree f l, mapTree f r)

let rec foldTree f e t = 
  match t with
  | Leaf -> e 
  | Node (x,l,r) -> f x (foldTree f e l) (foldTree f e r)

Here is the stub for map:

*/
function mapTree<A,B> (f: A -> B, t: Tree<A>): Tree<B> {
  // Replace with your implementation
  match t { case Leaf => Leaf case Node(x,l,r) => Node (f(x),mapTree(f,l),mapTree(f,r))}
}

/* Fill in your own template for fold, with the same argument order as the OCaml code. */
function foldTree<A,B> (f: (A -> B -> B -> B), acc: B, t: Tree<A>): B
{
  match t {case Leaf => acc case Node(x,l,r) => f(x)(foldTree(f,acc,l))(foldTree(f,acc,r))   }
}


// Question 2 (10 points)

// You are given the following MapSet wrapper arround Dafny's maps, which
// fixes the type of the "values" to be booleans. As a result,
// one can think of a MapSet as a set, where an element is considered
// to be in the MapSet iff it maps to true in the wrapped map.

// Implement the following set API calls in terms of this
// wrapper, by invoking Dafny map functions as seen on the slides.

datatype MapSet<T> = MapSet (s : map<T,bool>)

predicate member<T> (m:MapSet<T>, x:T) {
  // Replace with your definition
  match m { case MapSet(s) => if x in s then s[x] == true else false}
}
function createValuesSet<T>(m: MapSet<T>) : (r:set<T>)
{
  set x | x in m.s.Keys && m.s[x] == true
}
//coming back to this - idea is going to make a new set
function size<T> (m:MapSet<T>): (r:int)
{
  // Replace with your definition
  match m { case MapSet(s) => if s == map[] then 0 else |createValuesSet(m)| }
}

function insert<T> (m:MapSet<T>, x:T): MapSet<T> {
  // Replace with your definition
  match m { case MapSet(s) => MapSet(s[x:=true])}
}

function delete<T> (m:MapSet<T>, x:T): MapSet<T> {
  // Replace with your definition
  match m { case MapSet(s) => MapSet(s[x:=false])}
}



// // -------------------------------------------------
// // Part TWO : REQUIRES & ENSURES CLAUSES (20 Points)
// // -------------------------------------------------

// // Question 1 (4 points)
// //
// // Fill in a requires clause that enables Dafny to verify
// // method PlusOne

method PlusOne (x : int) returns (y : int)
  requires x >=0
  ensures y > 0
{
  y := x+1;
}

// // Question 2 (4 points)
// //
// // Fill in requires clause(s) that enable(s) Dafny to verify the array bounds
// // in method Swap (which swaps elements i and j in array a).

method Swap (a : array<int>, i : int, j : int)
  requires 0 <= i < a.Length && 0 <= j < a.Length // done
  modifies a
{
  var tmp : int := a[i];
  a[i] := a[j];
  a[j] := tmp;
}

// // Question 3 (4 points)
// //
// // Give ensures clause(s) asserting that d is the result, and r the
// // remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// // the Dafny division and mod operators, respectively). By definition, the
// // remainder must be non-negative.

method IntDiv (m : int, n : int) returns (d : int, r : int)
  requires n > 0
  ensures r >= 0 // done?
{
  d := m / n;
  r := m % n;
}

// // Question 4 (4 points)
// //
// // Fill in requires and ensures clauses for method Abs,
// // which computes the absolute value of x.

method Abs(x: int) returns (a: int)
  requires x is int // what else could this be?
  ensures a >= 0// abs cannot be negative
{
  if x >= 0 {
    a := x;
  } else {
    a := -x;
  }
}

// // Question 5 (4 points)
// //
// // Add an ensures clause for MaxSum, returning s as the sum of x and y,
// // and m is the maximum of x and y.

method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y // TODO
  ensures m >=y || m>= x
{
  s := x + y;
  if x < y {
    m := y;
  } else {
    m := x;
  }
}



// // --------------------------------------------
// // PART THREE : ADVANCED CHALLENGES (30 Points)
// // --------------------------------------------

// // Question 1 (10 Points)
// //
// // These two functions return the Min and Max of a sequence. Fill in both
// // function shells and the requires and ensures clauses that correspond to both.

function findMin(s: seq<int>): int
  requires s != []
  ensures s is seq<int>
{
  if |s| == 1 then
    s[0]
  else
    var rest_min := findMin(s[1..]);
    if s[0] < rest_min then s[0] else rest_min
}

function findMax(s: seq<int>): int
  requires s != []
  ensures s is seq<int>
{
  if |s| == 1 then
    s[0]
  else
    var rest_max := findMax(s[1..]);
    if s[0] < rest_max then rest_max else s[0]
}


// // Question 2 (10 points)
// //
// // This method returns a new sequence that is the reverse of the input sequence.
// // Use an approach similar to findMin and findMax to write the function and its
// // ensures statement.

function rhelper(s: seq<int>) : (r:seq<int>)
  requires s != []
  ensures |s| == |r|
{                                     //[2]   [7,5,2] len 3 elem 1
  if |s| == 1 then s else [s[|s|-1]] + rhelper(s[..|s|-1])
}


method Reverse(s: seq<int>) returns (r: seq<int>)
  ensures |s| == |r|
{
  if s == [] {
    return  s;
  }else {
    r := rhelper(s);
  }
}

// // Question 3 (10 points)
// //
// // This method converts a sequence (immutable array) into a finite map,
// // keyed off of integer indices within the original sequence. Use an
// // approach similar to findMin and findMax to write the function and its
// // ensures statement.


function shelper( s: seq<int>, i: int ) :(m:map<int,int>)
  decreases |s|
{
  if s == [] then map[] else  map[i := s[0]] + shelper(s[1..],i+1)
}

method SeqToMap(s: seq<int>) returns (m: map<int, int>)
  ensures m is map<int,int>
  decreases |s|  // Termination measure for recursion
{
  return shelper(s,0);
}



// // ------------------------------
// // PART FOUR : LEMMAS (30 Points)
// // ------------------------------

// // The following function definitions will be used to prove the lemmas below.

function Fib(n: int): int {
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}

function Fib3(n: int): int {
  if n < 3 then n else Fib3(n - 3) + Fib3(n - 2) + Fib3(n - 1)
}

function Fibly(n: int): int {
  if n < 2 then n else Fibly(n - 2) - Fibly(n - 1)
}

// Function `Pow(n)` computes `2^n` (that is, 2 to the power of `n`).
function Pow(n: nat): int
{
  if n == 0 then 1 else 2 * Pow(n - 1)
}

// A quicker way to compute `2^n` squares intermediate results.
function FastPow(n: nat): int
{
  if n == 0 then
    1
  else
    var half := n / 2;
    var p := FastPow(half);
    if n % 2 == 0 then
      p * p
    else
      2 * p * p
}

// // Use the above functions to prove the lemmas below.

lemma {:induction false} Fib3GetsLarger(n: int)
  ensures n <= Fib3(n)
{
  //base case
  if n < 3 {
    assert n == Fib3(n);
    assert n == n;
  } else  {
    // what I want to prove is n <=Fib3(n)
    // ih: n -1 <= fib3(n-1)

    Fib3GetsLarger(n-1); // This allows us to say line 294 is true and is our inductive hypo
    assert Fib3(n) == Fib3(n - 3) + Fib3(n - 2) + Fib3(n - 1);

    {Fib3GetsLarger(n - 3); Fib3GetsLarger(n - 2); Fib3GetsLarger(n - 1);} // again using our ih
    assert Fib3(n - 3) + Fib3(n - 2) + Fib3(n - 1) >= (n-3) + (n-2) + (n -1);
  }
}

lemma {:induction false} FibFibly(n: nat)
  ensures n % 2 == 0 ==> Fib(n) == -Fibly(n)
  ensures n % 2 != 0 ==> Fib(n) == Fibly(n)
{
  if n < 2 {
    assert n == Fib(n);
    assert n == Fibly(n);
  }else {
    FibFibly(n-1);
    assert Fib(n) == Fib(n - 2) + Fib(n - 1);
    if n % 2 == 0 {
      {FibFibly(n-2); FibFibly(n-1);}
      assert Fib(n - 2) + Fib(n - 1) == -Fibly(n-2) + Fibly(n-1);

    }else {
      {FibFibly(n-2); FibFibly(n-1);}
      assert Fib(n - 2) + Fib(n - 1) == Fibly(n-2) - Fibly(n-1);

    }
  }

}

lemma {:induction false} Squaring(m: nat, n: nat)
  ensures Pow(m + n) == Pow(m) * Pow(n)
{
  if m  + n == 0 {
    assert Pow (m + n) == 1;
    assert Pow(m) * Pow(n) ==1;
    assert Pow (m) * Pow(n) ==  Pow(m+n);
  }else if m ==0 || n == 0{

  }else
  {
    Squaring(m-1,n-1);
    assert Pow(m+n) == 2 * Pow(m+n-1);
  }
}

//even :  FastPow(n/2) * FastPow(n/2) odd :  2* FastPow(n/2) * FastPow(n/2)
// p = FastPow(n-1/2)
lemma {:induction false} FastPowCorrect(n: nat)
  ensures Pow(n) == FastPow(n)
{
  if n == 0{

  }else {
    FastPowCorrect(n-1);
    if n  % 2 == 0 {
      assert FastPow(n) ==  FastPow(n/2) * FastPow(n/2);
      FastPowCorrect(n/2);
      assert FastPow(n/2) * FastPow(n/2) == Pow(n/2) * Pow(n/2);
      Squaring(n/2,n/2);

    }else {
      assert FastPow(n) == 2*  FastPow(n/2) * FastPow(n/2);
      FastPowCorrect(n/2);
      assert FastPow(n/2) * FastPow(n/2) == Pow(n/2) * Pow(n/2);
    }

    // assert Pow(n) == 2* Pow(n-1);
    // assert 2 * Pow(n-1)== 2* FastPow(n-1);
    // var half := (n-1) /2;
    // var p := FastPow(half);
    // if (n-1) % 2 == 0 {
    //   assert 2 * FastPow(n-1) == 2 * p * p;
    //   assert FastPow(n-1) == p * p;

    // }else{
    //   assert 2 * FastPow(n - 1) == 2* 2* p * p;
    //   assert 2 * p * p == FastPow(n-1);
    // }

  }
}