(* vim: ts=2:sw=2:textwidth=100
 * 
 * Exercise 5
 *
 *)

open boolLib listTheory rich_listTheory pairTheory pairSyntax;

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

val MASK_FILTER_REMOVE_HEAD = prove (
  ``!hm mask h1 l1 h2 l2. (MASK_FILTER (hm::mask) (h1::l1) = (h2::l2))
                      ==> (MASK_FILTER      mask       l1  =      l2)``,
  Induct_on `l1` >> Induct_on `l2` >> Induct_on `mask` >| [
    SIMP_TAC list_ss [MASK_FILTER_def],
    REPEAT STRIP_TAC >>
    RW_TAC (srw_ss()) [MASK_FILTER_REWR]
    SIMP_TAC (srw_ss()) [MASK_FILTER_def]
  ]
);

val WEAK_SUBLIST_REC_FILTER = prove (
  ``!x y t1 t2. IS_WEAK_SUBLIST_FILTER (x::t1) (y::t2)
                  = (  ((x = y) ∧ IS_WEAK_SUBLIST_FILTER t1 t2))
                     ∨ ((x ≠ y) ∧ IS_WEAK_SUBLIST_FILTER t1 (y::t2))``,
  RW_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def] >>
  EQ_TAC >>
  Cases_on `x = y` >>
  ASM_REWRITE_TAC[] >>
  REPEAT STRIP_TAC >| [
    EXISTS_TAC ``(TL_T mask): bool list`` >>
    Induct_on `mask` >| [
      FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
      GEN_TAC >>
      DISCH_TAC >>
      FULL_SIMP_TAC list_ss []
      RW_TAC list_ss [TL_T_def]
      FULL_SIMP_TAC list_ss [MASK_FILTER_REWR]
    ]
    cheat,
    cheat,
    EXISTS_TAC ``T::mask`` >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    EXISTS_TAC ``F::mask`` >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR]
  ]
);

val WEAK_SUBLIST_REMOVE_HEAD_RIGHT_FILTER = prove (
  ``!l1 l2 t. IS_WEAK_SUBLIST_FILTER l1 (t::l2) ==> IS_WEAK_SUBLIST_FILTER l1 l2``,
  cheat
);
  Induct_on `l1` >> Induct_on `l2` >| [
    SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    ASM_REWRITE_TAC[WEAK_SUBLIST_EMPTY_FILTER],
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_REWR]
    `LENGTH mask > 0` by ASM_SIMP_TAC list_ss [] >>



    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def]
    
    `h::l2 = MAP SND (FILTER FST (ZIP (mask',h'::l1)))`
        by FULL_SIMP_TAC list_ss [MAP_FILTER_REMOVE_HEAD]


    (*
     *  ****** t *** :: *** h **** :: ----------------------------l2
     *  h'::----------------------------------------------------------- l1
     *
     *)


    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def] >>
    REPEAT STRIP_TAC >>
    `LENGTH mask > 0` by ASM_SIMP_TAC list_ss [] >>
    SUBGOAL_THEN ``?m: bool tmask. mask = m::tmask`` ASSUME_TAC >> (
      Cases_on `mask` >| [
        FULL_SIMP_TAC list_ss [],
        (* Q.MATCH_RENAME_TAC `?m tmask. h::t = m::tmask` *)
        EXISTS_TAC ``h'': bool`` >>
        EXISTS_TAC ``t': bool list`` >>
        REWRITE_TAC[]
      ]
    ) >>
    RW_TAC std_ss [] >>
    EXISTS_TAC ``F::tmask`` >>
    EXISTS_TAC ``m::tmask: bool list`` >>
    SIMP_TAC list_ss [MASK_FILTER_REWR] >>




    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def] >>
    REPEAT STRIP_TAC >>
    `LENGTH mask > 0` by ASM_SIMP_TAC list_ss [] >>
    Q.REFINE_EXISTS_TAC `m::(TL mask)` >>


    EXISTS_TAC ``F: bool`` >>
    ASM_SIMP_TAC list_ss [MASK_FILTER_REWR] >>



    EXISTS_TAC ``F: bool`` >>
    ASM_SIMP_TAC list_ss [MASK_FILTER_REWR] >>
    (*
    SUBGOAL_THEN ``?m: bool tmask. mask = m::tmask`` ASSUME_TAC >> (
      Cases_on `mask` >| [
        FULL_SIMP_TAC list_ss [],
        EXISTS_TAC ``h'': bool`` >>
        EXISTS_TAC ``t': bool list`` >>
        REWRITE_TAC[]
      ]
    ) >>
    *)
    Q.REFINE_EXISTS_TAC `m::mask` >>
    EXISTS_TAC ``F: bool`` >>
    ASM_SIMP_TAC list_ss [] >>

    METIS_TAC[]
  ]
);

val MASK_FILTER_REMOVE_HEAD = prove (
  ``!hm mask h1 l1 h2 l2. (LENGTH mask = LENGTH l1)
      ==> (MASK_FILTER (hm::mask) (h1::l1) = (h2::l2)) ==> (MASK_FILTER mask l1 = l2)``,
  Induct_on `l1` >> Induct_on `l2` >>
  Induct_on `mask` >>
  FULL_SIMP_TAC list_ss [LENGTH, MASK_FILTER_REWR] >>
  RW_TAC list_ss [MASK_FILTER_REWR, MASK_FILTER_def, MASK_FILTER_SHORTER] >>
  FULL_SIMP_TAC list_ss [LENGTH, MASK_FILTER_REWR] >>
  cheat
  METIS_TAC[]

  
  REWRITE_TAC[MASK_FILTER_REWR]
  Cases_on `hm` >| [
    ASM_REWRITE_TAC[] >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC list_ss [],
    ASM_REWRITE_TAC[] >>
    REPEAT STRIP_TAC >>
    ASM_REWRITE_TAC[]
    `F` by cheat
  ]
);

val MASK_FILTER_TL = prove (
  ``!mask h1 l1 h2 l2. ((LENGTH mask = SUC (LENGTH l1)) ∧ (MASK_FILTER mask (h1::l1) = (h2::l2)))
            ==> (MASK_FILTER (TL mask) l1 = l2)``,
  Induct_on `l1` >> Induct_on `l2` >> Induct_on `mask` >| [
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    SIMP_TAC list_ss [] >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_SHORTER] >>
    RW_TAC list_ss [MASK_FILTER_REWR, MASK_FILTER_def, MASK_FILTER_SHORTER] >>
    cheat,
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    cheat,
    FULL_SIMP_TAC list_ss [MASK_FILTER_REWR],
    cheat
  ]
);

val WEAK_SUBLIST_REMOVE_HEAD_BOTH_FILTER = prove (
  ``!h1 l1 h2 l2. IS_WEAK_SUBLIST_FILTER (h1::l1) (h2::l2) <=> IS_WEAK_SUBLIST_FILTER l1 l2``,
  cheat
);

val WEAK_SUBLIST_FILTER_FILTER = prove (
  ``!l1 l2 P. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER l1 (FILTER P l2)``,
  Induct_on `l1` >> Induct_on `l2` >| [
    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    REWRITE_TAC[FILTER] >>
    REPEAT STRIP_TAC >>
    Cases_on `P h` >>
    RW_TAC bool_ss [] >>
    `IS_WEAK_SUBLIST_FILTER (h'::l1) l2`
        by METIS_TAC[WEAK_SUBLIST_REMOVE_HEAD_RIGHT_FILTER] >>
    RES_TAC >- (
      Cases_on `h' = h` >>
      FULL_SIMP_TAC list_ss [] >>
      `IS_WEAK_SUBLIST_FILTER l1 (FILTER P l2)`
          by METIS_TAC[WEAK_SUBLIST_REMOVE_HEAD_BOTH_FILTER] >>
			cheat
    ) >>
    METIS_TAC[]
  ]
);

(** 1.4 Properties **)

val WEAK_SUBLIST_ADD_HEAD_LEFT_FILTER = prove (
  ``!l1 l2 h. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER (h::l1) l2``,
  Induct_on `l1` >> Induct_on `l2` >| [
    REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
    FULL_SIMP_TAC list_ss [MASK_FILTER_def] >>
    REPEAT STRIP_TAC >>
    EXISTS_TAC ``[F]`` >>
    SIMP_TAC list_ss [],

    FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def, MASK_FILTER_def],
    ASM_REWRITE_TAC[WEAK_SUBLIST_EMPTY_FILTER],
    (* SNOC MASK THM (reverse?) *)
    REPEAT STRIP_TAC >>
    UNDISCH_TAC ``IS_WEAK_SUBLIST_FILTER (h'::l1) (h::l2)`` >>
    SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def] >>
    REPEAT STRIP_TAC >>
    EXISTS_TAC ``F::mask`` >>
    SIMP_TAC list_ss [MASK_FILTER_REWR] >>
    ASM_REWRITE_TAC[]
  ]
);

val WEAK_SUBLIST_PREPEND_LIST_LEFT_FILTER = prove (
  ``!l1 l2 l. IS_WEAK_SUBLIST_FILTER l1 l2 ==> IS_WEAK_SUBLIST_FILTER (l ++ l1) l2``,
  cheat
);

val WEAK_SUBLIST_MIDDLE_LEFT_FILTER = prove ( (* TODO *)
  ``!l1a l1 l1b l2. IS_WEAK_SUBLIST_FILTER l1 l2
      ==> IS_WEAK_SUBLIST_FILTER (l1a ++ l1 ++ l1b) l2``,
  Induct_on `l1` >> Induct_on `l2` >>
  FULL_SIMP_TAC list_ss [] >>
  FULL_SIMP_TAC list_ss [IS_WEAK_SUBLIST_FILTER_def] >>
  cheat
);

val WEAK_SUBLIST_COMPOSE_FILTER = prove ( (* TODO *)
  ``!l1a l1b l2a l2b. IS_WEAK_SUBLIST_FILTER l1a l2a ==> IS_WEAK_SUBLIST_FILTER l1b l2b
      ==> IS_WEAK_SUBLIST_FILTER (l1a ++ l1b) (l2a ++ l2b)``,
  (* TODO: Use WEAK_SUBLIST_MIDDLE_LEFT_FILTER *)
  cheat
);

val WEAK_SUBLIST_SELF_FILTER = prove (
  ``!l. IS_WEAK_SUBLIST_FILTER l l``,
  REWRITE_TAC[IS_WEAK_SUBLIST_FILTER_def] >>
  Induct >| [
    EXISTS_TAC ``[]: bool list`` >>
    SIMP_TAC list_ss [MASK_FILTER_REWR],
    STRIP_TAC >>
    RW_TAC std_ss [] >>
    EXISTS_TAC ``T::mask`` >>
    ASM_SIMP_TAC list_ss [MASK_FILTER_REWR]
  ]
);

val WEAK_SUBLIST_TRANSITIVE_FILTER = prove ( (* TODO *)
  ``!l1 l2 l3. IS_WEAK_SUBLIST_FILTER l1 l2
           ==> IS_WEAK_SUBLIST_FILTER l2 l3
           ==> IS_WEAK_SUBLIST_FILTER l1 l3``,
  cheat
);

val WEAK_SUBLIST_BOTH_DIR_EQ_FILTER = prove ( (* TODO *)
  ``!l1 l2. IS_WEAK_SUBLIST_FILTER l1 l2
        ==> IS_WEAK_SUBLIST_FILTER l2 l1
        ==> (l1 = l2)``,
  cheat
);

(* 1.3. Equivalence Proof *)

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




















