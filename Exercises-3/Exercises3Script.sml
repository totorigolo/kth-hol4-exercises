(*
 * Exercise 3
 *)

open listTheory rich_listTheory;

(*
 * 2.1 Replay Proofs from Lecture
 *
 * Tactical Proof Examples - Part VIII
 * Examples from the course slides.
 *)

(* We want to prove !l. LENGTH (APPEND l l) = 2 * LENGTH l *)

val LENGTH_APPEND_SAME = prove (
  ``!l: 'a list. LENGTH (APPEND l l) = 2 * LENGTH l``,
    REWRITE_TAC[LENGTH_APPEND] >>
    REWRITE_TAC[arithmeticTheory.TIMES2]
  );

(* Now, we want to show something more complicated. *)

val NOT_ALL_DISTINCT_LEMMA = prove (
  ``!x1 x2 x3 l1 l2 l3.
    (MEM x1 l1 /\ MEM x2 l2 /\ MEM x3 l3) /\
    ((x1 <= x2) /\ (x2 <= x3) /\ x3 <= SUC x1) ==>
    ~(ALL_DISTINCT (l1 ++ l2 ++ l3))``,
    REPEAT GEN_TAC >> STRIP_TAC >>
    REWRITE_TAC[ALL_DISTINCT_APPEND] >>
    REWRITE_TAC[MEM_APPEND] >>
    `(x2 = x1) ∨ (x2 = x3)` by DECIDE_TAC >>
    (* Easily solved by first-order reasoning *)
    ( METIS_TAC [] )
  );

(*
 * Induction Proof Examples - Part IX
 * Examples from the course slides.
 *)

val REVERSE_APPEND = prove (
  ``!l1 l2: 'a list. REVERSE (l1 ++ l2) = REVERSE l2 ++ REVERSE l1``,
  Induct >| [
    REWRITE_TAC[REVERSE_DEF, APPEND, APPEND_NIL],
    ASM_REWRITE_TAC[REVERSE_DEF, APPEND, APPEND_ASSOC]
  ]);

val REVERSE_REVERSE = prove (
  ``!l: 'a list. REVERSE (REVERSE l) = l``,
  Induct >| [
    REWRITE_TAC[REVERSE_DEF],
    ASM_REWRITE_TAC[REVERSE_DEF, REVERSE_APPEND, APPEND]
  ]);

(*
 * 2.2 Formalise Induction Proofs from Exercise 1
 *)

(* Prove !l. l ++ [] = l via induction using the definition of APPEND (++). *)

val APPEND_NIL_SAME = prove (
  ``!l: 'a list. l ++ [] = l``,
  Induct >> (
    ASM_REWRITE_TAC[APPEND]
  ));

(* Prove the associativity of APPEND, i.e. prove !l1 l2 l3. l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3. *)

val APPEND_ASSOC = prove (
  ``!l1 l2 l3: 'a list. l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3``,
  Induct >> (
    ASM_REWRITE_TAC[APPEND]
  ));

(*
 * 2.3 Reverse
 *)

(* Prove the lemma !l1 l2. LENGTH (REV l1 l2) = (LENGTH l1 + LENGTH l2). *)

val LENGTH_CONS_EQ_PLUS_ONE = prove (
  ``!h: 'a l: 'a list. LENGTH (h::l) = 1 + LENGTH l``,
  ASM_REWRITE_TAC[LENGTH] >>
  DECIDE_TAC
  );

val LENGTH_REV_IS_LENGTH_OF_ARGS = prove (
  ``!l1 l2: 'a list. LENGTH (REV l1 l2) = (LENGTH l1 + LENGTH l2)``,
  Induct >| [
    REWRITE_TAC[REV_DEF] >>
    ASM_REWRITE_TAC[listLib.LENGTH_CONV ``LENGTH ([]: 'a list)``] >>
    DECIDE_TAC,
    ASM_REWRITE_TAC[REV_DEF] >>
    REWRITE_TAC[LENGTH_CONS_EQ_PLUS_ONE] >>
    DECIDE_TAC
  ]);

(* Prove !l1 l2. REV l1 l2 = REVERSE l1 ++ l2. *)

val REVERSE_REV_bis = prove (
  ``!l1 l2: 'a list. REV l1 l2 = REVERSE l1 ++ l2``,
  Induct >| [
    REWRITE_TAC[REV_DEF, REVERSE_DEF, APPEND],
    ASM_REWRITE_TAC[REV_DEF] >>
    ASM_REWRITE_TAC[REVERSE_DEF] >>
    `!h l2. h::l2 = [h] ++ l2` by ASM_REWRITE_TAC[APPEND] >>
    ONCE_ASM_REWRITE_TAC[] >>
    (* PAT_X_ASSUM ``!h. _ = _`` (fn th => ALL_TAC) *)
    REWRITE_TAC[APPEND_ASSOC, APPEND_NIL]
  ]);

(* Prove !l. REVERSE l = REV l []. *)

val REV_REVERSE_LEM = prove (
  ``!l: 'a list. REVERSE l = REV l []``,
  Induct >| [
    REWRITE_TAC[REV_DEF, REVERSE_DEF, APPEND],
    REWRITE_TAC[REVERSE_REV_bis, APPEND_NIL]
  ]);

(*
 * 2.4 Length of Drop
 *)

(* Prove !l1 l2. LENGTH (DROP (LENGTH l2) (l1 ++ l2)) = LENGTH l1. *)

val LENGTH_DROP_bis = prove (
  ``!l1 l2: 'a list. LENGTH (DROP (LENGTH l2) (l1 ++ l2)) = LENGTH l1``,
  Induct_on `l2` >| [
    (* Base case *)
    `LENGTH [] = 0` by REWRITE_TAC[LENGTH_NIL] >>
    ASM_REWRITE_TAC[APPEND_NIL, DROP],
    (* Induction step *)
    Cases_on `l1` >| [
      (* Empty l1 *)
      REWRITE_TAC[APPEND_NIL, DROP_LENGTH_NIL],
      (* l1 of the form h::t *)
      GEN_TAC >>
      REWRITE_TAC[LENGTH] >>
      REWRITE_TAC[APPEND] >>
      REWRITE_TAC[DROP] >>
      `t ++ h' :: l2 = (t ++ [h']) ++ l2` by REWRITE_TAC[APPEND, GSYM APPEND_ASSOC] >>
      (** applies ^ and induction hypothesis **)
      ASM_REWRITE_TAC[] >>
      REWRITE_TAC[LENGTH_APPEND, LENGTH] >>
      DECIDE_TAC
    ]
  ]);

(* 2.5 Making Change *)

val MAKE_CHANGE_def = Define `
  (MAKE_CHANGE [] a = if (a = 0) then [[]] else []) ∧
  (MAKE_CHANGE (c::cs) a = (
    (if (c <= a ∧ 0 < a) then
      (MAP (λl. c::l) (MAKE_CHANGE cs (a - c)))
    else []) ++ (MAKE_CHANGE cs a)))`;

EVAL ``MAKE_CHANGE [4;3;3;1;1;1;1;1;1] 6``;

(* Prove that !cs. MAKE_CHANGE cs 0 = [[]]. *)

val MAKE_CHANGE_ZERO = prove (
  ``!cs. MAKE_CHANGE cs 0 = [[]]``,
  Induct >| [
    ASM_REWRITE_TAC[MAKE_CHANGE_def],
    ASM_REWRITE_TAC[MAKE_CHANGE_def] >>
    ASM_REWRITE_TAC[prim_recTheory.LESS_REFL] >>
    ASM_REWRITE_TAC[APPEND_NIL]
  ]);

(* Prove that !cs a l. MEM l (MAKE_CHANGE cs a) ==> (SUM l = a). *)

val MAKE_CHANGE_CORRECT = prove (
  ``!cs a l. MEM l (MAKE_CHANGE cs a) ==> (SUM l = a)``,
  Induct_on `cs` >| [
    (* ∀a l. MEM l (MAKE_CHANGE [] a) ⇒ (SUM l = a) *)
    ASM_REWRITE_TAC[MAKE_CHANGE_def] >>
    Cases_on `a` >| [
      (* ∀l. MEM l (if 0 = 0 then [[]] else []) ⇒ (SUM l = 0) *)
      REWRITE_TAC[Once EQ_REFL] >>
      REWRITE_TAC[MEM] >>
      GEN_TAC >> DISCH_TAC >>
      ASM_REWRITE_TAC[SUM],
      (* ∀l. MEM l (if SUC n = 0 then [[]] else []) ⇒ (SUM l = SUC n) *)
      ASM_REWRITE_TAC[numTheory.NOT_SUC] >>
      REWRITE_TAC[MEM]
    ],
    (* Induction step *)
    REPEAT GEN_TAC >>
    REWRITE_TAC[MAKE_CHANGE_def] >>
    Cases_on `h ≤ a ∧ 0 < a` >| [
      ASM_REWRITE_TAC[MEM_APPEND, MEM_MAP] >>
      BETA_TAC >>
      REPEAT STRIP_TAC >| [
        ASM_REWRITE_TAC[SUM] >>
        Q.SUBGOAL_THEN `SUM y = a - h` (fn th => ASM_REWRITE_TAC[th]) >>
          UNDISCH_TAC ``MEM y (MAKE_CHANGE cs (a − h))`` >>
          ASM_REWRITE_TAC[]
         >>
        DECIDE_TAC,
        UNDISCH_TAC ``MEM l (MAKE_CHANGE cs a)`` >>
        ASM_REWRITE_TAC[]
      ],
      ASM_REWRITE_TAC[MEM_APPEND, MEM]
    ]
  ]);

