(* vim: ts=2:sw=2:textwidth=100
 * 
 * Exercise 5
 *
 *)

open boolLib listTheory rich_listTheory;

val IGNORE_ME = "vim's syntax highlighter is buggy";

(* Define some test tools *)

fun test_rhs_is thm r description = let
  (* Named "test_" because it doesn't return the given theorem. *)
  val _ = assert_exn (fn th => (rhs (concl th)) = r) thm
          (Fail ("test failed: " ^ description));
in ("test passed: " ^ description) end;

(* 1. Multiple Definitions / Formal Sanity
 * 
 * |- !l1 l2. IS_SUBLIST l1 l2 <=> ?l l’. l1 = l ++ (l2 ++ l’)
 *)

(* 1.1 Recursive Definition *)

val IS_WEAK_SUBLIST_REC_def = Define `
    (IS_WEAK_SUBLIST_REC l1 [] = T)
  ∧ (IS_WEAK_SUBLIST_REC [] (_::_) = F)
  ∧ (IS_WEAK_SUBLIST_REC (x::t1) (y::t2)
      = (  ((x = y) ∧ IS_WEAK_SUBLIST_REC t1 t2))
         ∨ ((x ≠ y) ∧ IS_WEAK_SUBLIST_REC t1 (y::t2)))`;

test_rhs_is (EVAL ``IS_WEAK_SUBLIST_REC [] []``) T "[] and []";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_REC [_;_;_] []``) T "non-[] and []";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;5;6]``) T "T case";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;6;5]``) F "F case";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4;5;6;7] [2;5;6;8]``) F "F case";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4] [1;2;3;4]``) T "Same lists";

fun IWSR_METIS_TAC thms = METIS_TAC (IS_WEAK_SUBLIST_REC_def::thms);

val MUST_BE_SMALLER_TO_BE_WEAK_SUBLIST_REC = prove (
  ``!l1 l2. (LENGTH l1 < LENGTH l2) ==> ¬(IS_WEAK_SUBLIST_REC l1 l2)``,
  Induct_on `l1` >> Induct_on `l2` >>
  FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_REC_def]
);

val EACH_MEM_OF_SUBLIST_ARE_IN_LIST_REC = prove (
  ``!l1 l2. (IS_WEAK_SUBLIST_REC l1 l2) ==> (!x. (MEM x l2 ==> MEM x l1))``,
  Induct_on `l1` >> Induct_on `l2` >>
  IWSR_METIS_TAC[MEM]
);

val WEAK_SUBLIST_ADD_HEAD_LEFT_REC = prove (
  ``!h l1 l2. IS_WEAK_SUBLIST_REC l1 l2 ==> IS_WEAK_SUBLIST_REC (h::l1) l2``,
  Induct_on `l1` >> Induct_on `l2` >>
  IWSR_METIS_TAC[]
);

val WEAK_SUBLIST_PREPEND_LIST_LEFT_REC = prove (
  ``!l1 l2 l. IS_WEAK_SUBLIST_REC l1 l2 ==> IS_WEAK_SUBLIST_REC (l ++ l1) l2``,
  Induct_on `l` >>
  FULL_SIMP_TAC list_ss [WEAK_SUBLIST_ADD_HEAD_LEFT_REC]
);

val WEAK_SUBLIST_ADD_TAIL_LEFT_REC = prove (
  ``!t l1 l2. IS_WEAK_SUBLIST_REC l1 l2 ==> IS_WEAK_SUBLIST_REC (l1 ++ [t]) l2``,
  Induct_on `l1` >> Induct_on `l2` >>
  FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_REC_def] >>
  IWSR_METIS_TAC[]
);

val WEAK_SUBLIST_INSERT_MIDDLE_LEFT_REC = prove (
  ``!l1a l1b x l2. IS_WEAK_SUBLIST_REC (l1a ++ l1b) l2
      ==> IS_WEAK_SUBLIST_REC (l1a ++ [x] ++ l1b) l2``,
  Induct_on `l1a` >> Induct_on `l1b` >> Induct_on `l2` >>
  FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_REC_def] >>
  IWSR_METIS_TAC[
    WEAK_SUBLIST_ADD_HEAD_LEFT_REC,
    WEAK_SUBLIST_PREPEND_LIST_LEFT_REC,
    WEAK_SUBLIST_ADD_TAIL_LEFT_REC
  ]
);

val WEAK_SUBLIST_APPEND_LIST_LEFT_REC = prove (
  ``!l1 l2 l. IS_WEAK_SUBLIST_REC l1 l2 ==> IS_WEAK_SUBLIST_REC (l1 ++ l) l2``,
  Induct_on `l1` >> Induct_on `l2` >> Induct_on `l` >>
  FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_REC_def] >>
  IWSR_METIS_TAC[WEAK_SUBLIST_ADD_TAIL_LEFT_REC]
);

val WEAK_SUBLIST_MIDDLE_LEFT_REC = prove (
  ``!l1a l1 l1b l2. IS_WEAK_SUBLIST_REC l1 l2
      ==> IS_WEAK_SUBLIST_REC (l1a ++ l1 ++ l1b) l2``,
  Induct_on `l1` >> Induct_on `l2` >>
  FULL_SIMP_TAC list_ss [
    IS_WEAK_SUBLIST_REC_def,
    WEAK_SUBLIST_PREPEND_LIST_LEFT_REC,
    WEAK_SUBLIST_APPEND_LIST_LEFT_REC
  ]
);

val WS_COMPOSE_L1_REC = prove (
  ``!l1a l1b l2a t2. IS_WEAK_SUBLIST_REC l1a l2a ==> IS_WEAK_SUBLIST_REC l1b [t2]
      ==> IS_WEAK_SUBLIST_REC (l1a ++ l1b) (l2a ++ [t2])``,
  Induct_on `l2a` >> Induct_on `l1a` >>
  FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_REC_def] >>
  REPEAT (RW_TAC bool_ss [])
);

val WEAK_SUBLIST_REMOVE_HEAD_RIGHT = prove (
  ``!l1 l2 h. IS_WEAK_SUBLIST_REC l1 (h::l2) ==> IS_WEAK_SUBLIST_REC l1 l2``,
  Induct_on `l1` >> Induct_on `l2` >>
  IWSR_METIS_TAC[]
);

val APPEND_CONS_APPEND = prove (
  ``!l1 l2 x. l1 ++ (x::l2) = l1 ++ [x] ++ l2``,
  REPEAT STRIP_TAC >>
  `x::l2 = [x] ++ l2` by FULL_SIMP_TAC list_ss [] >>
  ONCE_ASM_REWRITE_TAC[] >>
  FULL_SIMP_TAC list_ss []
);

val WEAK_SUBLIST_COMPOSE_REC = prove (
  ``!l1a l1b l2a l2b. IS_WEAK_SUBLIST_REC l1a l2a ==> IS_WEAK_SUBLIST_REC l1b l2b
      ==> IS_WEAK_SUBLIST_REC (l1a ++ l1b) (l2a ++ l2b)``,
  Induct_on `l1a` >> Induct_on `l1b` >> Induct_on `l2a` >> Induct_on `l2b` >>
  FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_REC_def] >| [
    `!l1 l2 h. l1 ++ h::l2 = (l1 ++ [h]) ++ l2`
        by FULL_SIMP_TAC list_ss [Once APPEND_CONS_APPEND] >>
    REPEAT STRIP_TAC >| [
      ALL_TAC,
      `IS_WEAK_SUBLIST_REC l1b l2b`
          by IWSR_METIS_TAC[WEAK_SUBLIST_REMOVE_HEAD_RIGHT]
    ] >>
    IWSR_METIS_TAC[WEAK_SUBLIST_PREPEND_LIST_LEFT_REC],

    IWSR_METIS_TAC[WEAK_SUBLIST_APPEND_LIST_LEFT_REC],

    `!l1 l2 h. h::(l1 ++ l2) = h::l1 ++ l2`
        by SIMP_TAC list_ss [] >>
    `!l1 l2 h. h::(l1 ++ h::l2) = (h::l1) ++ (h::l2)`
        by ASM_REWRITE_TAC[] >>
    IWSR_METIS_TAC[WEAK_SUBLIST_PREPEND_LIST_LEFT_REC]
  ]
);

val WEAK_SUBLIST_SELF_REC = prove (
  ``!l. IS_WEAK_SUBLIST_REC l l``,
  Induct_on `l` >>
  ASM_REWRITE_TAC[IS_WEAK_SUBLIST_REC_def]
);

val WEAK_SUBLIST_TRANSITIVE = prove (
  ``!l1 l2 l3. IS_WEAK_SUBLIST_REC l1 l2
           ==> IS_WEAK_SUBLIST_REC l2 l3
           ==> IS_WEAK_SUBLIST_REC l1 l3``,
  Induct_on `l1` >> Induct_on `l2` >> Induct_on `l3` >>
  IWSR_METIS_TAC[WEAK_SUBLIST_ADD_HEAD_LEFT_REC, WEAK_SUBLIST_COMPOSE_REC]
);

val WEAK_SUBLIST_BOTH_DIR_EQ = prove (
  ``!l1 l2. IS_WEAK_SUBLIST_REC l1 l2
        ==> IS_WEAK_SUBLIST_REC l2 l1
        ==> (l1 = l2)``,
  Induct_on `l1` >> Induct_on `l2` >>
  IWSR_METIS_TAC[WEAK_SUBLIST_ADD_HEAD_LEFT_REC, WEAK_SUBLIST_COMPOSE_REC]
);

(* 1.2 Filter Definition *)


































