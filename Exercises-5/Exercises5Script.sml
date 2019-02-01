(* vim: ts=2:sw=2:textwidth=100
 * 
 * Exercise 5
 *
 *)

open boolLib listTheory rich_listTheory pairTheory pairSyntax;
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

(*
 *      --- ---    --- ---
 *  5. mask = [T;t;t;t;t]
 *)


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
        `LENGTH mask ≠ LENGTH l1 ∨ l2 ≠ MASK_FILTER mask l1` by ASM_REWRITE_TAC[] >>
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
  ``!mask l1. (LENGTH mask = LENGTH l1) ⇒ LENGTH (MASK_FILTER mask l1) ≤ LENGTH l1``,
  Induct_on `l1` >> Induct_on `mask` >>
  SIMP_TAC list_ss [LENGTH, MASK_FILTER_REWR] >>
  REPEAT STRIP_TAC >>
  Cases_on `h` >>
  FULL_SIMP_TAC list_ss [] >>
  RES_TAC >>
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
    `h::(t ++ [t'']) = (h::t) ++ [t'']` by FULL_SIMP_TAC list_ss [] >>
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

val MAP_IMP = prove (
  ``!f l1 l2. (l1 = l2) ==> ((MAP f l1) = (MAP f l2))``,
  SIMP_TAC list_ss []
);

val FILTER_IMP = prove (
  ``!f l1 l2. (l1 = l2) ⇒ ((FILTER f l1) = (FILTER f l2))``,
  SIMP_TAC list_ss []
);

val ZIP_IMP = prove (
  ``!x1 x2 y1 y2. ((x1, y1) = (x2, y2)) ⇒ ((ZIP (x1, y1)) = (ZIP (x2, y2)))``,
  SIMP_TAC list_ss []
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

EVAL ``MASK_FILTER (T::m2) []``;

val SPECIAL_MAP_WORKS = prove (
  ``!l m1 m2. (LENGTH l = LENGTH m1)
        ==> (LENGTH m)
        ==> (MASK_FILTER (SPECIAL_MAP m2 m1) l
           = MASK_FILTER m2 (MASK_FILTER m1 l))``,
  Induct_on `l` >> Induct_on `m1` >> Induct_on `m2` >>
  FULL_SIMP_TAC list_ss [
    MASK_FILTER_REWR,
    SPECIAL_MAP_def,
    EVAL ``LENGTH (MASK_FILTER [] [])``,
    SPECIAL_MAP_EMPTY
  ]
  RW_TAC list_ss []
);

val WEAK_SUBLIST_TRANSITIVE_FILTER = prove ( (* TODO: 1.4.4 *)
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
  REWRITE_TAC[MASK_FILTER_def] >>
  Induct_on `mask` >> Induct_on `mask'` >> Induct_on `l1` >>
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




    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR] >>
    (* Cases_on `h'` >> *)
    Cases_on `h''` >>
    FULL_SIMP_TAC list_ss [SPECIAL_MAP_def] >| [
      Cases_on `h'` >>
      RW_TAC list_ss [SPECIAL_MAP_def, MASK_FILTER_REWR, MASK_FILTER_def] >>

    ]

    RW_TAC list_ss []
    REV_FULL_SIMP_TAC list_ss [MASK_FILTER_def]
    RES_TAC

    cheat
  ]
);

val WEAK_SUBLIST_BOTH_DIR_EQ_FILTER = prove ( (* TODO: 1.4.5 *)
  ``!l1 l2. IS_WEAK_SUBLIST_FILTER l1 l2
        ==> IS_WEAK_SUBLIST_FILTER l2 l1
        ==> (l1 = l2)``,
  cheat
);

(* 1.3. Equivalence Proof *)

(*
val IS_WEAK_SUBLIST_REC_EQ_FILTER = prove (
  ``IS_WEAK_SUBLIST_REC = IS_WEAK_SUBLIST_FILTER``,
  (* REWRITE_TAC[FUN_EQ_THM] >> *)
  METIS_TAC[
    IS_WEAK_SUBLIST_FILTER_def,
    IS_WEAK_SUBLIST_REC_def,
    WEAK_SUBLIST_SELF_FILTER, (* faster with it *)
    MASK_FILTER_REWR,
    MASK_FILTER_REMOVE_HEAD
  ]
);
*)




















