(*
2.1. Our Own Lists

Of course SML comes with a decent list library. However, as an exercise implement your own
list datatype and implement the following list operations for your own datatype:
• length
• append (@)
• rev
• revAppend
• exists
If you don’t know what these functions should do, you can find documentation of the Standard
ML Basis Library at e.g. http://sml-family.org.

In addition implement a function replicate : ’a -> int -> ’a list, which is supposed to
construct a list of the given length that only contains the given element. For example
replicate "a" 3 should return the list ["a", "a", "a"].
*)

fun length [] = 0
  | length (x::xs) = length(xs) + 1

fun append xs [] = xs
  | append [] ys = ys
  | append (x::xs) ys = x::(append xs ys)

fun rev [] = []
  | rev (x::xs) = append (rev xs) [x]

fun revAppend(xs, ys) = append (rev xs) ys

fun exists f [] = false
  | exists f (x::xs) = f(x) orelse exists f xs

fun replicate x 0 = []
  | replicate x n = x::(replicate x (n-1))

(*
2.1.1. Prove that for your implementation append l [] = l holds for all l.

Well... It holds by definition.

The first pattern of the function isn't mandatory and can be removed. But
then the function will rebuild the left list even if the right one is empty.
Defining this pattern hence optimizes the function.

Without it, we have to prove `append l [] = l` for all l, using:
fun append [] [] = []
  | append (x::xs) [] = x::(append xs [])

The induction proof is immediate: the first pattern is the base case and
the second one the induction step.


2.1.2. Similarly, prove ∀l1 l2. length (append l1 l2) = length l1 + length l2.

We can immediately prove that length is correct, because it is the immediate
implementation of its definition.

Then, we want to go from `length (append l1 l2)` to `length (append [] l2)`
that we know equal to `length l2 = length [] + length l2`. This is the base
case of the induction proof.

Now, we want to prove `length (append (x::xs) l2) = length xs + 1 + length l2`
given that `length (append xs l2) = length xs + length l2`.

length (append (x::xs) l2)
  = length (x::(append xs l2))
  = length (append xs l2) + 1
  = length xs + 1 + length l2

2.1.3. There are strong connections between append, revAppend and rev. One can
      for example define revAppend by revAppend l1 l2 = append (rev l1) l2.
      Write down similar definitions for rev and append using only revAppend.
*)

fun rev l = revAppend(l, [])
fun append l1 l2 = revAppend( revAppend(l1, []), l2 )

(*
2.2 Making Change
In the following, let’s use the standard list library again. Write a program that given the coins
and notes you have in your wallet, lists all the possible ways to pay a certain amount. Represent
the coins you have as a list of integers. If a number occurs twice in this list, you have two coins
with this value. The result should be returned in the form of a list of lists. For simplicity, the
output may contain duplicates.
An example implementation of the function `make_change : int list -> int -> int list list`
should shows for example the following outputs.  Notice however, that the output of your
implementation is allowed to contain duplicates and use a different order of the lists.
• make_change [5,2,2,1,1,1] 6 = [[5, 1], [2, 2, 1, 1]]
• make_change [5,2,2,1,1,1] 15 = []
• make_change [10,5,5,5,2,2,1,1,1] 10 = [[10], [5, 5], [5, 2, 2, 1], [5, 2, 1, 1, 1]]

Write down as formally as you can some properties of make_change. An example property is
∀cs n. n > sum cs ==> make_change cs n = [] where sum is defined by val sum = foldl (op+) 0 and
we assume that cs contains no number less than 0.

*)

fun make_change [] 0 = [[]]
  | make_change [] x = []
  | make_change (v::vs) x =
    if v > x then make_change vs x
    else (List.map (fn change => v::change) (make_change vs (x - v)))
       @ (make_change vs x)

make_change [5,2,2,1,1,1] 6 (* [[5, 1], [2, 2, 1, 1]] *)
make_change [5,2,2,1,1,1] 15 (* [] *)
make_change [10,5,5,5,2,2,1,1,1] 10 (* [[10], [5, 5], [5, 2, 2, 1], []] *)

