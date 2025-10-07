// ASSIGNMENT 2
// CMSC 433 FALL 2025
// PERFECT SCORE:  150 POINTS
//
// You should include your solutions in a single Dafny file and submit
// it using Gradescope.

// ----------------------------------------------------------
// PART ONE: Invariants (50 points)
// ----------------------------------------------------------

// Helpers For Question 1: 

predicate sorted(c:array<int>)
  reads(c)
{
  forall t :: 0 <= t < c.Length-1 ==> c[t] <= c[t+1]
}
lemma SliceFull<T>(a: array<T>)
  ensures a[..] == a[..a.Length]
{}

// Question 1 (10 Points)
// 
// Give invariant(s) that enable(s) Dafny to verify the following program, which
// merges two sorted arrays in to one sorted array

// method merge_sorted_arrays1(a: array<int>, b: array<int>) returns (c: array<int>)
//   requires sorted(a)
//   requires sorted(b)
//   ensures  c.Length == a.Length + b.Length
//   ensures sorted(c)
//   ensures sorted(c)
//   ensures  multiset(c[..]) == multiset(old(a[..])) + multiset(old(b[..]))
// {
//   c := new int[a.Length + b.Length];
//   var i := 0;
//   var j := 0;
//   var k := 0;
//   // some ideas are that at every step c has to be sorted
//   while i < a.Length || j < b.Length
//     decreases (a.Length - i) + (b.Length - j)
//     invariant i <= a.Length &&  j <=  b.Length
//     invariant a.Length  + b.Length == c.Length
//     invariant 0 <= k <= a.Length + b.Length
//     invariant i + j <= k  
//     invariant multiset(c[..k]) == multiset((a[..i])) + multiset((b[..j]))  
//     invariant forall 
  
//     {
//     if i < a.Length && (j >= b.Length || a[i] <= b[j]) {
//       c[k] := a[i]; // k = 0, i = 0 
//       i := i + 1; // 0,1,2,3,4,5
//     } else {
//       c[k] := b[j];
//       j := j + 1; //0,1,2,3,4,5
//     }
//     k := k + 1; //0,1,2,3,4,5
//   }

//   SliceFull(a);
//   SliceFull(b);
//   SliceFull(c);
// }

// Question 2 (10 Points)
//
// Give invariant(s) that enable(s) Dafny to verify the following program, which
// concatenates two arrays in to one array

method concat(a: array<int>, b: array<int>) returns (c: array<int>)
  ensures a[..] + b[..] == c[..]
{
  c := new int[a.Length + b.Length];

  // Copy a into c
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c[..i] == a[..i]
    
  {
    c[i] := a[i]; // after 1 it c[a[0]] -> c[a[0], a[1]]
    i := i + 1;
  }

  // Copy b into c after a's elements
  var j := 0;
  while j < b.Length
    invariant 0 <= j<= b.Length 
    invariant c[..a.Length] == a[..]
    invariant c[..a.Length+j] == c[..a.Length] + b[..j] // a[1,2] b [] c [1,2] 
  {
    c[a.Length + j] := b[j]; // c[1,2,3] b[4,5,6]
    j := j + 1;               // c[1,2,3,4] , j =1 -> c[1,2,3,4,5] ==
  }
}

// // Question 3 (10 Points)
// //
// // Give invariant(s) that enable(s) Dafny to verify the following program, which
// // checks if the sequence has duplicate items

// method containsDuplicate(nums: seq<int>) returns (d: bool)
//   ensures d ==> exists i,j :: 0 <= i < j < |nums| && nums[i] == nums[j]
// {
//   var numSet: set<int> := {};
//   for i:= 0 to |nums|
//     // TO DO
//   {
//     if nums[i] in numSet {
//       return true;
//     }
//     //+ is overloaded to set union
//     numSet := numSet + {nums[i]};
//   }
//   return false;
// }

// // Question 4 (10 Points)
// // 
// // Given that three sorted arrays share some common element, find the indices
// // where it appears.

// ghost predicate Ascending(arr: array<int>) 
//     reads arr
//   {
//     forall i, j :: 0 <= i <= j < arr.Length ==> arr[i] <= arr[j]
//   }

// method FindCommonElement(f: array<int>, g: array<int>, h: array<int>) returns (x: nat, y: nat, z: nat)
//     requires Ascending(f) && Ascending(g) && Ascending(h)
//     requires exists i, j, k :: 0 <= i < f.Length && 0 <= j < g.Length && 0 <= k < h.Length && f[i] == g[j] == h[k]
//     ensures 0 <= x < f.Length
//     ensures 0 <= y < g.Length
//     ensures 0 <= z < h.Length
//     ensures f[x] == g[y] == h[z]
//   {
//     x, y, z := 0, 0, 0;
//     while true // FILL IN
//     {
//       if f[x] < g[y] {
//         x := x + 1;
//       } else if g[y] < h[z] {
//         y := y + 1;
//       } else if h[z] < f[x] {
//         z := z + 1;
//       } else {
//         return;
//       }
//     }
//   }

// // Question 5 (10 Points)
// // 
// // The following method finds the longest ascending subsequence within an
// // array and returns the start and end indices of that subsequence.
// // Verify that the subsequence is both ascending and the longest (i.e.
// // every other ascending subsequence is not longer than the returned one).

// ghost predicate AscendingInRange(arr: array<int>, i: int, j: int) 
//     reads arr
//     requires 0 <= i <= j < arr.Length
//   {
//     forall k, l :: i <= k <= l <= j ==> arr[k] <= arr[l]
//   }

// method LongestAscending(arr: array<int>) returns (i: nat, j: nat)
//     requires arr.Length > 0
//     ensures 0 <= i <= j < arr.Length
//     ensures AscendingInRange(arr, i, j)
//     ensures forall k, l :: 0 <= k <= l < arr.Length && AscendingInRange(arr, k, l) ==> l - k <= j - i
//   {
//     i, j := 0, 0;
//     var i', j' := 0, 0;
//     while j' < arr.Length - 1
//     {
//       if arr[j'] <= arr[j' + 1] {
//         j' := j' + 1;
//       } else {
//         if j' - i' > j - i {
//           j := j';
//           i := i';
//         }
//         j' := j' + 1;
//         i' := j';
//       }
//     }
//     if j' - i' > j - i {
//       j := j';
//       i := i';
//     }
//   }



// // ----------------------------------------------------------
// // PART TWO: Writing Methods (30 points)
// // ----------------------------------------------------------

// // For all the methods, you are not allowed to call the method inside the method itself. 
// // Recursive methods are not allowed.
// // You must implemenet the methods using loops. 

// // Question 1 (10 points)
// //
// // Implement, and have Dafny verify, the method IsPrime below, which returns true
// // if and only if the given positive integer is prime.

// method IsPrime (m : int) returns (isPrime : bool)
//     requires m > 0
//     ensures isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0)
// {
//     // Your implementation here
// }

// // Question 2 (10 points)
// //
// // Implement, and have Dafny verify, the method TwoSum below, which returns
// // two distinct indices i and j such that the sum of the elements at these
// // indices in the given array equals the target value. It is guaranteed that
// // such a pair of indices exists.

// method TwoSum(arr: array<int>, target: int) returns (i: int, j: int)
//   requires arr.Length >= 2
//   requires exists k, l :: 0 <= k < l < arr.Length && arr[k] + arr[l] == target
//   ensures // FILL THIS IN
// {
//   // Your implementation here
// } 

// // Question 3 (10 points)
// //
// // // Implement, and have Dafny verify, the method Join below, which 
// // returns a join of two given arrays.  
// // To create a new array of ints use the Dafny command "new int[...]", 
// // where "..." is the number of elements in the array.

// //join([4,6,8], [4,7,5,9]) returns [4,6,8,4,7,5,9]

// method Join(a:array<int>,b:array<int>) returns (c:array<int>)
//   ensures a[..] + b[..] == c[..]
//   ensures multiset(a[..] + b[..]) == multiset(c[..])
//   ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
//   ensures a.Length + b.Length == c.Length
// {
//   c := new int[a.Length + b. Length];
//   var i := 0;
//    // FILL THIS IN
// }



// // ----------------------------------------------------------
// // PART THREE: Nat & Bin (40 points)
// // ----------------------------------------------------------

// // Let's define binary numbers from first principles!
// // Specifically, a binary number is just a list of bits
// // (Booleans: 'true' for 1, 'false' for 0).

// // There is still some ambiguity in this choice of type.
// // Please represent binary numbers such that the least-significant bit appears
// // first.  This would be the bit that appears *last* in conventional notation,
// // so we are effectively storing binary numbers in *reverse order* to simplify
// // your job.  (You may see how it helps, as you proceed through the
// // assignment.)

// datatype list<T> = Nil | Cons(head: T, tail: list<T>)

// function Length<T>(l: list<T>): nat {
//   match l
//   case Nil => 0
//   case Cons(_, l') => 1 + Length(l')
// }
// type binary = list<bool>

// // Your first challenge: implement both of these conversions between our
// // binary-numbers type and the built-in natural-number type.
// function BinaryToNat(b: binary): nat

// // method Test1(){
// //   assert BinaryToNat(Nil) == 0;
// //   assert BinaryToNat(Cons(true, Nil)) == 1;
// //   assert BinaryToNat(Cons(true,Cons(true, Nil))) == 3;
// //   assert BinaryToNat(Cons(false, Cons(false, Cons(true, Nil)))) == 4;
// // }

// function NatToBinary(n: nat): binary

// // method Test2(){
// //   assert NatToBinary(0) == Cons(false,(Nil));
// //   assert NatToBinary(1) == (Cons(true, Nil));
// //   assert NatToBinary(2) == (Cons(false,Cons(true, Nil)));
// //   assert NatToBinary(3) == (Cons(true,Cons(true, Nil)));
// //   assert NatToBinary(6) == Cons(false,(Cons(true,Cons(true, Nil))));
// // }

// // Your second challenge: prove this lemma about round-tripping in one order.
// lemma NatToBinary_and_back(n: nat)
//   ensures BinaryToNat(NatToBinary(n)) == n

// // Next, we would like to prove the round-tripping law in the other order.
// // However, it is not literally true!  (At least, it isn't with the
// // implementations we chose.)  Define a predicate to capture when a binary
// // number is *well-formed*.  HINT: we can use well-formedness to be sure there
// // are not multiple ways to write the same number.  Make sure this predicate
// // accepts just one *canonical* binary representation per number.
// predicate WellFormedBinary(b: binary)

// // method Test3(){
// //   assert  WellFormedBinary(Nil) == false;
// //   assert WellFormedBinary(Cons(true, Nil)) == true;
// //   assert WellFormedBinary(Cons(true,Cons(true, Nil)));
// //   assert WellFormedBinary(Cons(false,Cons(true, Nil)));
// //   assert WellFormedBinary(Cons(false,Nil));
// //   assert WellFormedBinary(Cons(true, Nil));
// //   assert WellFormedBinary(Cons(false,Cons(true, Nil)));
// //   assert WellFormedBinary(Cons(true,Cons(true, Nil)));
// //   assert !WellFormedBinary(Cons(false,Cons(false, Nil)));
// // }

// // Then you should be able to prove the remaining round-tripping law.
// lemma BinaryToNat_and_back(b: binary)
//   requires WellFormedBinary(b)
//   ensures NatToBinary(BinaryToNat(b)) == b

// // Also, show that your own translation respects this well-formedness notion.
// lemma NatToBinary_WellFormed(n: nat)
//   ensures WellFormedBinary(NatToBinary(n))

// // The last subchallenge: define *addition* on binary numbers.
// // For full credit, DO NOT use your translations back and forth with 'nat',
// // and indeed don't use any translations of whole bitstrings to normal number
// // types.  Try to write code that operates as directly on the binary
// // representation as possible!
// // HINT: you will probably find it useful to define multiple helper functions,
// // some of which may get their own correctness lemmas.
// function Add(n: binary, m: binary): binary
//   requires Length(n) == Length(m)

// // Finally, prove your implementation correct.
// lemma Add_correct(n: binary, m: binary)
//   requires Length(n) == Length(m)
//   ensures BinaryToNat(Add(n, m)) == BinaryToNat(n) + BinaryToNat(m)



// // ----------------------------------------------------------
// // PART FOUR: Hoare Logic (30 points)
// // ----------------------------------------------------------

// // Question 1 (15 points)

// /*
//     Here is a program that computes the series:
//     [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

//     x := 0;
//     y := 1;
//     z := 1;
//     while x != m {
//       z := 2 * z;
//       y := y + z;
//       x := x + 1;
//     }
//     end

//     Fill in the following decorated program - you can use the following
//     function in your assertions and invariants. Do NOT remove the numbers or
//     change anything else about the programs. Only replace "FILL_IN_HERE" with
//     your assertions---they should be valid Dafny propositions.
// */

// function pow2(n : nat) : nat {
//   match n 
//   case 0 => 1
//   case _ => 2 * (pow2 (n-1))
// }

// /* 
//     { true } ->
// (1)    {}
//       x := 0;
// (2)    {}
//       y := 1;
// (3)    {}
//       z := 1;
// (4)    {}
//       while x != n {
// (5)       {} ->
// (6)       {}
//         z := 2 * z;
// (7)       {}
//         y := y + z;
// (8)       {}
//         x := x + 1;
// (9)       {}
//       }
// (10)  {} ->
//       {}
// */


// // Question 2 (15 points)
// /*
//     Here is a pretty inefficient way of adding 3 numbers:

//      x := 0;
//      y := 0;
//      z := c;
//      while x != a {
//        x := x + 1;
//        z := z + 1;
//      };
//      while y <> b {
//        y := y + 1;
//        z := z + 1;
//      }

//     Show that it does what it should by completing the
//     following decorated program. Again, do NOT remove the letters or
//     change anything else about the programs. Only replace "FILL_IN_HERE" with
//     your assertions---they should be valid Dafny propositions.
// */

// /*
//     { true } ->
// (a) {}
//       x := 0;
// (b)                {}
//       y := 0;
// (c)                {}
//       z := c;
// (d)                {}
//       while x != a {
// (e)                {} ->
// (f)                {}
//         x := x + 1;
// (g)                {}
//         z := z + 1;
// (h)                {}
//       end;
// (i)                {} ->
// (j)                {}
//       while y != b {
// (k)                {} ->
// (l)                {}
//         y := y + 1;
// (m)                {}
//         z := z + 1;
// (n)                {}
//       }
// (o) {} ->
//     {}
// */
