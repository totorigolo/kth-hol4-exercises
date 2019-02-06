(* vim: ts=2:sw=2:textwidth=100
 * 
 * Exercise 5
 *
 *)

open boolLib listTheory rich_listTheory pairTheory pairSyntax;
open bossLib;
open listLib; (* For SNOC_INDUCT_TAC *)

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
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_REC [1;2;2;4] [2;2]``) T "T with duplicates";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_REC [1;2;3;4] [2;2]``) F "F with duplicates";

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

(** 1.4 Properties **)

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

val WEAK_SUBLIST_REMOVE_HEAD_RIGHT_REC = prove (
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
          by IWSR_METIS_TAC[WEAK_SUBLIST_REMOVE_HEAD_RIGHT_REC]
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

val WEAK_SUBLIST_TRANSITIVE_REC = prove (
  ``!l1 l2 l3. IS_WEAK_SUBLIST_REC l1 l2
           ==> IS_WEAK_SUBLIST_REC l2 l3
           ==> IS_WEAK_SUBLIST_REC l1 l3``,
  Induct_on `l1` >> Induct_on `l2` >> Induct_on `l3` >>
  IWSR_METIS_TAC[WEAK_SUBLIST_ADD_HEAD_LEFT_REC, WEAK_SUBLIST_COMPOSE_REC]
);

val WEAK_SUBLIST_BOTH_DIR_EQ_REC = prove (
  ``!l1 l2. IS_WEAK_SUBLIST_REC l1 l2
        ==> IS_WEAK_SUBLIST_REC l2 l1
        ==> (l1 = l2)``,
  Induct_on `l1` >> Induct_on `l2` >>
  IWSR_METIS_TAC[WEAK_SUBLIST_ADD_HEAD_LEFT_REC, WEAK_SUBLIST_COMPOSE_REC]
);

val WEAK_SUBLIST_EMPTY_REC = prove (
  ``!l. IS_WEAK_SUBLIST_REC l []``,
  Induct_on `l` >>
  IWSR_METIS_TAC[]
);

(* 1.2 Filter Definition *)

val MASK_FILTER_def = Define `
  MASK_FILTER mask l = MAP SND (FILTER FST (ZIP (mask, l)))
`;

val MASK_FILTER_REWR = prove (
  ``  (MASK_FILTER [] [] = [])
    ∧ (!m mt h lt. MASK_FILTER (m::mt) (h::lt) =
                   if m then (h::MASK_FILTER mt lt)
                        else (   MASK_FILTER mt lt))``,
  REWRITE_TAC[MASK_FILTER_def, MAP, FILTER, FST, ZIP] >>
  Cases_on `m` >>
  REWRITE_TAC[MAP]
);

test_rhs_is (EVAL ``MASK_FILTER [T;T;T;T] [1;2;3;4]``) ``[1;2;3;4]`` "keep all";
test_rhs_is (EVAL ``MASK_FILTER [F;F;F;F] [1;2;3;4]``) ``[]: num list`` "keep none";
test_rhs_is (EVAL ``MASK_FILTER [F;T;F;T] [1;2;3;4]``) ``[2;4]`` "keep some 1";
test_rhs_is (EVAL ``MASK_FILTER [T;F;T;F] [1;2;3;4]``) ``[1;3]`` "keep some 2";
test_rhs_is (EVAL ``MASK_FILTER [T;F;F;F] [1;2;3;4]``) ``[1]`` "keep first";
test_rhs_is (EVAL ``MASK_FILTER [F;F;F;T] [1;2;3;4]``) ``[4]`` "keep last";

val IS_WEAK_SUBLIST_FILTER_def = Define `
    IS_WEAK_SUBLIST_FILTER l1 l2 = (?mask. (LENGTH mask = LENGTH l1)
                                         ∧ (l2 = MASK_FILTER mask l1))
`;

g `IS_WEAK_SUBLIST_FILTER [1;2;3;4] [1;3]`;
e (REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def]);
e (EXISTS_TAC ``[T;F;T;F]``);
e (SIMP_TAC list_ss [MASK_FILTER_def]);
drop ();

(*
 * I hate you, HOL.

fun prove_IWS_FILTER_num l1 l2 mask = prove (
  mk_anylet ([(``l1: num list``, l1), (``l2: num list``, l2)],
             ``IS_WEAK_SUBLIST_FILTER (l1: num list) (l2: num list)``),
  REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
  SIMP_TAC std_ss [LET_THM] (* removes the let *) >>
  EXISTS_TAC mask >>
  SIMP_TAC list_ss [MASK_FILTER_def]
);

fun tg term = set_goal ([], term);
tg (mk_anylet ([(``l1: num list``, ``[1;2;3;4]``), (``l2: num list``, ``[1;3]``)],
               ``IS_WEAK_SUBLIST_FILTER (l1: num list) (l2: num list)``));
list_mk_comb (``IS_WEAK_SUBLIST_FILTER``, [``[1;2;3;4]: num list``, ``[1;3]: num list``]);
prove_IWS_FILTER ``[1;2;3;4]: num list`` ``[1;3]: num list`` ``[T;F;T;F]: bool list``;
*)

EVAL ``IS_WEAK_SUBLIST_FILTER [1;2;3;4] [1;3]``;

(*
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_FILTER [] []``) T "[] and []";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_FILTER [_;_;_] []``) T "non-[] and []";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_FILTER [1;2;3;4;5;6;7] [2;5;6]``) T "T case";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_FILTER [1;2;3;4;5;6;7] [2;6;5]``) F "F case";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_FILTER [1;2;3;4;5;6;7] [2;5;6;8]``) F "F case";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_FILTER [1;2;3;4] [1;2;3;4]``) T "Same lists";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_FILTER [1;2;2;4] [2;2]``) T "T with duplicates";
test_rhs_is (EVAL ``IS_WEAK_SUBLIST_FILTER [1;2;3;4] [2;2]``) F "F with duplicates";
*)

fun IWSF_METIS_TAC thms = METIS_TAC (IS_WEAK_SUBLIST_FILTER_def::thms);

val MUST_BE_SMALLER_TO_BE_WEAK_SUBLIST_FILTER = prove (
  ``!l1 l2. (LENGTH l1 < LENGTH l2) ==> ¬(IS_WEAK_SUBLIST_FILTER l1 l2)``,
  SIMP_TAC bool_ss [IS_WEAK_SUBLIST_FILTER_def] >>
  Induct_on `l1` >> Induct_on `l2` >| [
    SIMP_TAC list_ss [MASK_FILTER_def],
    SIMP_TAC list_ss [MASK_FILTER_def],
    SIMP_TAC list_ss [MASK_FILTER_def],
    REPEAT STRIP_TAC >>
    Induct_on `mask` >| [
      SIMP_TAC list_ss [MASK_FILTER_def],
      REWRITE_TAC[MASK_FILTER_REWR] >>
      Cases >>
      FULL_SIMP_TAC list_ss [MASK_FILTER_REWR] >| [
        METIS_TAC[],
        RES_TAC >>
        `LENGTH mask ≠ LENGTH l1 ∨ l2 ≠ MASK_FILTER mask l1`
            by ASM_REWRITE_TAC[] >>
        METIS_TAC[]
      ]
    ]
  ]
);

val WEAK_SUBLIST_EMPTY_FILTER = prove (
  ``!l. IS_WEAK_SUBLIST_FILTER l []``,
  Induct_on `l` >| [
    SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
    STRIP_TAC >>
    ASSUME_TAC IS_WEAK_SUBLIST_FILTER_def >>
    RES_TAC >>
    EXISTS_TAC ``F::mask`` >>
    SIMP_TAC list_ss [MASK_FILTER_REWR] >>
    ASM_REWRITE_TAC[]
  ]
);

val WEAK_SUBLIST_OF_EMPTY_FILTER = prove (
  ``!l. l ≠ [] ==> ¬(IS_WEAK_SUBLIST_FILTER [] l)``,
  Induct_on `l` >| [
    REWRITE_TAC[],
    SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def]
  ]
);

val MASK_FILTER_SHORTER = prove (
  ``!mask l1. (LENGTH mask = LENGTH l1)
             ⇒ LENGTH (MASK_FILTER mask l1) ≤ LENGTH l1
  ``,
  Induct_on `l1` >> Induct_on `mask` >>
  SIMP_TAC list_ss [LENGTH, MASK_FILTER_REWR] >>
  REPEAT STRIP_TAC >>
  Cases_on `h` >>
  FULL_SIMP_TAC list_ss [] >>
  RES_TAC >>
  DECIDE_TAC
);

val MASK_FILTER_SHORTER2 = prove (
  ``!m l1 l2. (LENGTH m = LENGTH l1)
          ==> (MASK_FILTER m l1 = l2)
          ==> (LENGTH l2 <= LENGTH l1)
  ``,
  Induct_on `l1` >- FULL_SIMP_TAC list_ss [MASK_FILTER_def] >>
  Induct_on `l2` >- FULL_SIMP_TAC list_ss [MASK_FILTER_def] >>
  Induct_on `m` >- FULL_SIMP_TAC list_ss [MASK_FILTER_def] >>
  REPEAT STRIP_TAC >>
  `LENGTH m = LENGTH l1` by FULL_SIMP_TAC list_ss [] >>
  Cases_on `h` >| [
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR] >>
    `LENGTH (MASK_FILTER m l1) = LENGTH l2`
        by FULL_SIMP_TAC list_ss [] >>
    `LENGTH (MASK_FILTER m l1) ≤ LENGTH l1`
        by FULL_SIMP_TAC list_ss [MASK_FILTER_SHORTER] >>
    DECIDE_TAC,
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR] >>
    `LENGTH (MASK_FILTER m l1) = LENGTH (h'::l2)`
        by FULL_SIMP_TAC list_ss [] >>
    `LENGTH (MASK_FILTER m l1) ≤ LENGTH l1`
        by FULL_SIMP_TAC list_ss [MASK_FILTER_SHORTER] >>
    `LENGTH (h'::l2) ≤ LENGTH (MASK_FILTER m l1)`
        by FULL_SIMP_TAC list_ss [] >>
    `LENGTH l2 < LENGTH (h'::l2)`
        by FULL_SIMP_TAC list_ss [] >>
    `LENGTH l2 < LENGTH (MASK_FILTER m l1)`
        by DECIDE_TAC >>
    DECIDE_TAC
  ]
);

val MASK_FILTER_IS_WEAK_SUBLIST_FILTER = prove (
  ``!m l. (LENGTH m = LENGTH l) ==> IS_WEAK_SUBLIST_FILTER l (MASK_FILTER m l)``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def] >>
  EXISTS_TAC ``m: bool list`` >>
  DECIDE_TAC
);

(** 1.4 Properties **)

val WEAK_SUBLIST_ADD_HEAD_LEFT_FILTER = prove (
  ``!l1 l2 h. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER (h::l1) l2``,
  Cases_on `l1` >> Cases_on `l2` >| [
    REWRITE_TAC[WEAK_SUBLIST_EMPTY_FILTER], 
    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    REWRITE_TAC[WEAK_SUBLIST_EMPTY_FILTER], 
    GEN_TAC >>
    SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def] >>
    REPEAT STRIP_TAC >>
    EXISTS_TAC ``F::mask`` >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR]
  ]
);

val WEAK_SUBLIST_PREPEND_LIST_LEFT_FILTER = prove (
  ``!l1 l2 l. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER (l ++ l1) l2``,
  Induct_on `l` >>
  FULL_SIMP_TAC list_ss [WEAK_SUBLIST_ADD_HEAD_LEFT_FILTER]
);

val WEAK_SUBLIST_ADD_AT_END_LEFT_FILTER = prove (
  ``!l1 l2 t. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER (l1 ++ [t]) l2``,
  Cases_on `l1` >> Cases_on `l2` >| [
    REWRITE_TAC[WEAK_SUBLIST_EMPTY_FILTER], 
    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    REWRITE_TAC[WEAK_SUBLIST_EMPTY_FILTER], 
    GEN_TAC >>
    SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def] >>
    REPEAT STRIP_TAC >>
    EXISTS_TAC ``mask ++ [F]`` >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_def] >>
    `h::(t ++ [t'']) = (h::t) ++ [t'']`
        by FULL_SIMP_TAC list_ss [] >>
    ASM_REWRITE_TAC[] >>
    `LENGTH mask = LENGTH (h::t)` by FULL_SIMP_TAC list_ss [] >>
    `ZIP (mask ++ [F], (h::t) ++ [t'']) = (ZIP (mask, h::t)) ++ (ZIP ([F], [t'']))`
      by FULL_SIMP_TAC list_ss [ZIP_APPEND] >>
    ASM_REWRITE_TAC[] >>
    REWRITE_TAC[FILTER_APPEND] >>
    SIMP_TAC list_ss []
  ]
);

val WEAK_SUBLIST_SNOC_LEFT_FILTER = prove (
  ``!l1 l2 t. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER (SNOC t l1) l2``,
  SIMP_TAC list_ss [WEAK_SUBLIST_ADD_AT_END_LEFT_FILTER, SNOC_APPEND]
);

val WEAK_SUBLIST_APPEND_LIST_LEFT_FILTER = prove (
  ``!l l1 l2. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER (l1 ++ l) l2``,
  SNOC_INDUCT_TAC >| [
    SIMP_TAC list_ss [],
    REWRITE_TAC[APPEND_SNOC] >>
    FULL_SIMP_TAC list_ss [WEAK_SUBLIST_SNOC_LEFT_FILTER]
  ]
);

val WEAK_SUBLIST_MIDDLE_LEFT_FILTER = prove ( (* 1.4.1 *)
  ``!l1a l1 l1b l2. IS_WEAK_SUBLIST_FILTER l1 l2
      ==> IS_WEAK_SUBLIST_FILTER (l1a ++ l1 ++ l1b) l2``,
  SIMP_TAC list_ss [
    WEAK_SUBLIST_PREPEND_LIST_LEFT_FILTER,
    WEAK_SUBLIST_APPEND_LIST_LEFT_FILTER
  ]
);

val MASK_FILTER_APPEND = prove (
  ``!m1 m2 l1 l2. ((LENGTH m1 = LENGTH l1) ∧ (LENGTH m2 = LENGTH l2))
               ==> ((MASK_FILTER m1 l1) ++ (MASK_FILTER m2 l2)
                   = MASK_FILTER (m1 ++ m2) (l1 ++ l2))``,
  REWRITE_TAC[MASK_FILTER_def] >>
  REPEAT STRIP_TAC >>
  `MAP SND (FILTER FST (ZIP (m1 ++ m2, l1 ++ l2)))
    = MAP SND (FILTER FST ((ZIP (m1, l1)) ++ (ZIP (m2, l2))))`
    by FULL_SIMP_TAC list_ss [ZIP_APPEND] >>
  ASM_SIMP_TAC list_ss [MAP_APPEND, FILTER_APPEND]
);

val WEAK_SUBLIST_COMPOSE_FILTER = prove ( (* 1.4.2 *)
  ``!l1a l1b l2a l2b. IS_WEAK_SUBLIST_FILTER l1a l2a ==> IS_WEAK_SUBLIST_FILTER l1b l2b
      ==> IS_WEAK_SUBLIST_FILTER (l1a ++ l1b) (l2a ++ l2b)``,
  REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
  REPEAT STRIP_TAC >>
  EXISTS_TAC ``(mask ++ mask'): bool list`` >>
  ASM_SIMP_TAC list_ss [] >> (* proves the LENGTHS *)
  FULL_SIMP_TAC list_ss [MASK_FILTER_APPEND]
);

val WEAK_SUBLIST_SELF_FILTER = prove ( (* 1.4.3 *)
  ``!l. IS_WEAK_SUBLIST_FILTER l l``,
  REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
  Induct >| [
    EXISTS_TAC ``[]: bool list`` >>
    SIMP_TAC list_ss [MASK_FILTER_REWR],
    STRIP_TAC >>
    RW_TAC std_ss [] >> (* Removes the ∃mask. in the assumtions. *)
    EXISTS_TAC ``T::mask`` >>
    ASM_SIMP_TAC list_ss [MASK_FILTER_REWR]
  ]
);

val SPECIAL_MAP_def = Define `
    (SPECIAL_MAP [] l = l)
  ∧ (SPECIAL_MAP _ [] = [])
  ∧ (SPECIAL_MAP (v::l1) (T::l2) = v::(SPECIAL_MAP l1 l2))
  ∧ (SPECIAL_MAP (v::l1) (F::l2) = F::(SPECIAL_MAP (v::l1) l2))
`;

val SPECIAL_MAP_EMPTY = prove (
  ``!m. SPECIAL_MAP m [] = []``,
  Cases >>
  FULL_SIMP_TAC list_ss [SPECIAL_MAP_def]
);

EVAL ``SPECIAL_MAP [T;F;T;T] [T;T;T;F;F;T]``;
EVAL ``SPECIAL_MAP [F;F;F;F] [T;T;T;F;F;T]``;
EVAL ``SPECIAL_MAP [T;T;T;T] [T;T;T;F;F;T]``;
EVAL ``SPECIAL_MAP [T;T;T;T;T] [T;T;T;F;F;T]``;

val SPECIAL_MAP_LENGTH = prove (
  ``!l1 l2. LENGTH (SPECIAL_MAP l1 l2) = LENGTH l2``,
  Induct_on `l1` >> Induct_on `l2` >>
  REPEAT Cases >>
  FULL_SIMP_TAC list_ss [SPECIAL_MAP_def]
);

val SPECIAL_MAP_WORKS = prove (
  ``!l m1 m2. (LENGTH l = LENGTH m1)
        ==> (LENGTH (MASK_FILTER m1 l) = LENGTH m2)
        ==> (MASK_FILTER (SPECIAL_MAP m2 m1) l
           = MASK_FILTER m2 (MASK_FILTER m1 l))``,
  Induct_on `m1` >> Induct_on `m2` >> Induct_on `l` >>
  REPEAT STRIP_TAC >| [
    FULL_SIMP_TAC list_ss [SPECIAL_MAP_def],
    FULL_SIMP_TAC list_ss [SPECIAL_MAP_def],
    FULL_SIMP_TAC list_ss [EVAL ``LENGTH (MASK_FILTER [] [])``],
    FULL_SIMP_TAC list_ss [EVAL ``LENGTH (MASK_FILTER [] [])``],
    FULL_SIMP_TAC list_ss [EVAL ``LENGTH (MASK_FILTER [] [])``],
    Cases_on `h'` >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR, SPECIAL_MAP_def] >>
    REV_FULL_SIMP_TAC list_ss [MASK_FILTER_def] >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    Cases_on `h''` >>
    FULL_SIMP_TAC list_ss [SPECIAL_MAP_def, MASK_FILTER_REWR]
  ]
);

val WEAK_SUBLIST_TRANSITIVE_FILTER = prove ( (* 1.4.4 *)
  ``!l1 l2 l3. IS_WEAK_SUBLIST_FILTER l1 l2
           ==> IS_WEAK_SUBLIST_FILTER l2 l3
           ==> IS_WEAK_SUBLIST_FILTER l1 l3``,
  REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
  REPEAT STRIP_TAC >>
  (* HOL is nice enough to let us work with that, to have an idea of the shape
   * of f. :)
  EXISTS_TAC ``(MAP (f (mask: bool list) (mask': bool list)) mask): bool list`` >>
  Q.REFINE_EXISTS_TAC `(MAP (f (mask: bool list) (mask': bool list)) mask): bool list` >>
  *)
  EXISTS_TAC ``(SPECIAL_MAP (mask': bool list) (mask: bool list)): bool list`` >>
  ASM_REWRITE_TAC[SPECIAL_MAP_LENGTH] (* proves the LENGTHS *) >>
  FULL_SIMP_TAC list_ss [SPECIAL_MAP_WORKS]
);

val MASK_FILTER_ALL_TRUE_1 = prove (
  ``!m l. (LENGTH m = LENGTH l) ==> (MASK_FILTER m l = l) ==> EVERY ($= T) m``,
  Induct_on `m` >> Induct_on `l` >| [
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR, EVERY_MEM],
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR, EVERY_MEM] >>
    RW_TAC list_ss [] >| [
      METIS_TAC[],
      `LENGTH (MASK_FILTER m l) ≤ LENGTH l` by METIS_TAC[MASK_FILTER_SHORTER] >>
      `LENGTH (h::l) = SUC (LENGTH l)` by FULL_SIMP_TAC list_ss [] >>
      `LENGTH (MASK_FILTER m l) < LENGTH (h::l)` by DECIDE_TAC >>
      `LENGTH (MASK_FILTER m l) ≠ LENGTH (h::l)` by DECIDE_TAC >>
      `!l1 l2. LENGTH l1 ≠ LENGTH l2 ==> l1 ≠ l2` by METIS_TAC[LIST_EQ] >>
      METIS_TAC[]
    ]
  ]
);

val MASK_FILTER_ALL_TRUE_2 = prove (
  ``!m l. (LENGTH m = LENGTH l) ==> (EVERY ($= T) m) ==> (MASK_FILTER m l = l)``,
  Induct_on `m` >> Induct_on `l` >>
  FULL_SIMP_TAC list_ss [MASK_FILTER_REWR]
);

val MASK_FILTER_ALL_TRUE = prove (
  ``!m l. (LENGTH m = LENGTH l) ==> ((MASK_FILTER m l = l) <=> EVERY ($= T) m)``,
  METIS_TAC[MASK_FILTER_ALL_TRUE_1, MASK_FILTER_ALL_TRUE_2]
);

val MASK_FILTER_MEM_F_EQ_NON_EQ = prove (
  ``!m l. (LENGTH m = LENGTH l) ==> (MEM F m <=> (MASK_FILTER m l ≠ l))``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC MASK_FILTER_ALL_TRUE >>
  RES_TAC >>
  FULL_SIMP_TAC list_ss [EVERY_MEM, EXISTS_MEM]
);

val MASK_FILTER_INJ = prove (
  ``!m l1 l2. (LENGTH l1 = LENGTH m) ==> (LENGTH l2 = LENGTH m)
          ==> (MASK_FILTER m l1 = l2) ==> (l1 = l2)``,
  Induct_on `l1` >> Induct_on `l2` >> Induct_on `m` >>
  NTAC 7 (FULL_SIMP_TAC list_ss [MASK_FILTER_REWR]) >>
  REPEAT STRIP_TAC >| [
    Cases_on `h` >>
    FULL_SIMP_TAC list_ss [] >>
    `LENGTH (MASK_FILTER m l1) ≤ LENGTH l1` by METIS_TAC[MASK_FILTER_SHORTER] >>
    `LENGTH (h'::l2) = SUC (LENGTH l1)` by FULL_SIMP_TAC list_ss [] >>
    `LENGTH (MASK_FILTER m l1) ≠ LENGTH (h'::l2)` by DECIDE_TAC >>
    `!l1 l2. LENGTH l1 ≠ LENGTH l2 ==> l1 ≠ l2` by METIS_TAC[LIST_EQ] >>
    METIS_TAC[],
    RES_TAC >>
    Cases_on `h` >| [
      FULL_SIMP_TAC list_ss [] >>
      `LENGTH (MASK_FILTER m l1) = LENGTH m`
          by FULL_SIMP_TAC list_ss [] >>
      METIS_TAC[],
      FULL_SIMP_TAC list_ss [] >>
      `LENGTH (MASK_FILTER m l1) ≤ LENGTH l1`
          by FULL_SIMP_TAC list_ss [MASK_FILTER_SHORTER] >>
      `LENGTH (h'::l2) = SUC (LENGTH l1)` by ASM_SIMP_TAC list_ss [] >>
      `LENGTH (MASK_FILTER m l1) ≠ LENGTH (h'::l2)` by DECIDE_TAC >>
      METIS_TAC[LIST_EQ]
    ]
  ]
);

val LIST_HAVE_UNIQUE_LENGTH = prove (
  ``!l. (!m: bool list. LENGTH m = LENGTH l) ==> F``,
  REPEAT STRIP_TAC >>
  `LENGTH [T] = LENGTH l` by METIS_TAC[] >>
  `LENGTH [T;T] = LENGTH l` by METIS_TAC[] >>
  ASSUME_TAC (EVAL ``LENGTH [T]``) >>
  ASSUME_TAC (EVAL ``LENGTH [T;T]``) >>
  `1 = 2` by DECIDE_TAC >>
  FULL_SIMP_TAC arith_ss []
);

val MASK_FILTER_TWICE_EQ_IMP_EQ = prove (
  ``!m1 m2 l. (LENGTH m1 = LENGTH (MASK_FILTER m2 l)) ==> (LENGTH m2 = LENGTH l) ==> (LENGTH m1 = LENGTH l)
          ==> (MASK_FILTER m1 (MASK_FILTER m2 l) = l) ==> (MASK_FILTER m2 l = l)``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC MASK_FILTER_ALL_TRUE >>
  FULL_SIMP_TAC list_ss [EVERY_MEM] >>
  CCONTR_TAC >>
  FULL_SIMP_TAC list_ss [] >>
  `MASK_FILTER m2 l ≠ l` by METIS_TAC[MASK_FILTER_MEM_F_EQ_NON_EQ] >>
  SUBGOAL_THEN ``MASK_FILTER m2 l = l`` ASSUME_TAC >- (
    ASSUME_TAC MASK_FILTER_INJ >>
    `LENGTH (MASK_FILTER m2 l) = LENGTH m1` by FULL_SIMP_TAC list_ss [] >>
    METIS_TAC[]
  ) >>
  METIS_TAC[]
);

val WEAK_SUBLIST_BOTH_DIR_EQ_FILTER = prove ( (* 1.4.5 *)
  ``!l1 l2. IS_WEAK_SUBLIST_FILTER l1 l2
        ==> IS_WEAK_SUBLIST_FILTER l2 l1
        ==> (l1 = l2)``,
  REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
  REPEAT STRIP_TAC >>
  `LENGTH l1 ≤ LENGTH l2` by METIS_TAC[MASK_FILTER_SHORTER2] >>
  `LENGTH l2 ≤ LENGTH l1` by METIS_TAC[MASK_FILTER_SHORTER2] >>
  `LENGTH l1 = LENGTH l2` by DECIDE_TAC >>
  `MASK_FILTER mask' l2 = l2` suffices_by FULL_SIMP_TAC list_ss [] >>
  `EVERY ($<=> T) mask'` suffices_by METIS_TAC[MASK_FILTER_ALL_TRUE] >>
  SIMP_TAC list_ss [EVERY_MEM] >>
  CCONTR_TAC >>
  `MEM F mask'` by FULL_SIMP_TAC list_ss [] >>
  `MASK_FILTER mask' l2 ≠ l2` by METIS_TAC[MASK_FILTER_MEM_F_EQ_NON_EQ] >>
  `l2 = MASK_FILTER mask (MASK_FILTER mask' l2)` by RW_TAC list_ss [] >>
  `LENGTH (MASK_FILTER mask' l2) = LENGTH mask` by RW_TAC list_ss [] >>
  `l2 = MASK_FILTER mask' l2` by METIS_TAC[MASK_FILTER_TWICE_EQ_IMP_EQ] >>
  METIS_TAC[]
);

(* 1.3. Equivalence Proof *)

val WEAK_SUBLIST_REMOVE_HEAD_LEFT_FILTER = prove (
  ``!h h' l1 l2. h ≠ h' ==> IS_WEAK_SUBLIST_FILTER (h::l1) (h'::l2)
                        ==> IS_WEAK_SUBLIST_FILTER     l1  (h'::l2)``,
  REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_REWR] >>
  REPEAT STRIP_TAC >>
  Cases_on `mask` >| [
    FULL_SIMP_TAC list_ss [EVAL ``LENGTH []``],

    EXISTS_TAC ``t: bool list`` >>
    `LENGTH t = LENGTH l1` by FULL_SIMP_TAC list_ss [] >>
    ASM_REWRITE_TAC[] >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR] >>
    Cases_on `h''` >> RW_TAC list_ss [] >>
    FULL_SIMP_TAC list_ss []
  ]
);

val IS_WEAK_SUBLIST_REC_EQ_FILTER = prove (
  ``IS_WEAK_SUBLIST_REC = IS_WEAK_SUBLIST_FILTER``,
  REWRITE_TAC[FUN_EQ_THM] >>
  Induct_on `x` >> Induct_on `x'` >| [
    EQ_TAC >>
    SIMP_TAC list_ss [
      IS_WEAK_SUBLIST_REC_def, IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_REWR],

    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_REC_def] >>
    METIS_TAC[WEAK_SUBLIST_ADD_HEAD_LEFT_FILTER],

    FULL_SIMP_TAC list_ss [
      IS_WEAK_SUBLIST_REC_def, IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_REWR],

    REPEAT STRIP_TAC >>
    EQ_TAC >| [
      REWRITE_TAC[IS_WEAK_SUBLIST_REC_def] >>
      REPEAT STRIP_TAC >| [
        RES_TAC >>
        FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_REWR] >>
        EXISTS_TAC ``T::mask`` >>
        FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_REWR],

        RES_TAC >>
        FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_REWR] >>
        EXISTS_TAC ``F::mask`` >>
        FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_REWR]
      ],

      REPEAT STRIP_TAC >>
      `?mask. (LENGTH mask = LENGTH (h::x')) ∧ (h'::x = MASK_FILTER mask (h::x'))`
          by METIS_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
      Cases_on `mask` >- FULL_SIMP_TAC list_ss [EVAL ``LENGTH []``] >>
      rename1 `MASK_FILTER (hm::tm) (h::x')` >>
      Cases_on `hm` >| [
        `(x = MASK_FILTER tm x') ∧ (LENGTH tm = LENGTH x')`
            by FULL_SIMP_TAC list_ss [MASK_FILTER_REWR] >>
        ASSUME_TAC IS_WEAK_SUBLIST_FILTER_def >>
        `IS_WEAK_SUBLIST_FILTER x' x` by METIS_TAC[] >>
        `IS_WEAK_SUBLIST_REC x' x` by METIS_TAC[] >>
        Cases_on `h = h'` >| [
          `IS_WEAK_SUBLIST_REC [h] [h']`
              by FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_REC_def] >>
          `IS_WEAK_SUBLIST_REC ([h] ++ x') ([h'] ++ x)`
              by METIS_TAC[WEAK_SUBLIST_COMPOSE_REC] >>
          FULL_SIMP_TAC list_ss [],
          ASSUME_TAC WEAK_SUBLIST_REMOVE_HEAD_LEFT_FILTER >>
          RES_TAC >>
          `IS_WEAK_SUBLIST_REC x' (h'::x)` by METIS_TAC[] >>
          `IS_WEAK_SUBLIST_REC (h::x') (h'::x)`
              by METIS_TAC[WEAK_SUBLIST_ADD_HEAD_LEFT_REC]
        ],
        `(h'::x = MASK_FILTER tm x') ∧ (LENGTH tm = LENGTH x')`
            by FULL_SIMP_TAC list_ss [MASK_FILTER_REWR] >>
        ASSUME_TAC IS_WEAK_SUBLIST_FILTER_def >>
        `IS_WEAK_SUBLIST_FILTER x' (h'::x)` by METIS_TAC[] >>
        `IS_WEAK_SUBLIST_REC x' (h'::x)` by METIS_TAC[] >>
        Cases_on `h = h'` >>
        METIS_TAC[WEAK_SUBLIST_ADD_HEAD_LEFT_REC]
      ]
    ]
  ]
);

