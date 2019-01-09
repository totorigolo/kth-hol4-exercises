structure e4_arraysLib :> e4_arraysLib =
struct

open HolKernel Parse bossLib dot_graphsLib
open e4_arraysTheory 


(* Example

val ag = let
  val ag = new_array_graph 
  val ag = add_node ag 1 NONE
  val ag = add_node ag 2 NONE
  val ag = add_node ag 3 NONE
  val ag = add_node ag 4 (SOME ``A /\ B``)
  val ag = add_node ag 5 NONE
  val ag = add_node_link ag 1 2 "a";
  val ag = add_node_link ag 1 3 "b";
  val ag = add_node_link ag 3 4 "c";
  val ag = add_node_link ag 4 5 "d";
in
  ag
end

val _ = (dot_binary := "/usr/bin/dot");


val _ = print_graph ag
val _ = show_graph ag


*)

fun simple_array n = let
  val n_t = numSyntax.term_of_int n
  val thm = EVAL ``FOLDL (\a n. UPDATE n a n) EMPTY_ARRAY (COUNT_LIST ^n_t)``
in
  rhs (concl thm)
end

fun sparse_array n = let
  val n_t = numSyntax.term_of_int n
  val thm = EVAL ``FOLDL (\a n. UPDATE n a (n*3)) EMPTY_ARRAY (COUNT_LIST ^n_t)``
in
  rhs (concl thm)
end

val a1 = simple_array 10;
val a2 = sparse_array 10;
val a3 = simple_array 20;
val a4 = simple_array 100;


