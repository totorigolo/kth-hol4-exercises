(* vim: ts=2:sw=2:textwidth=100
 *)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "e4_arrays";


(**************************************************)
(* Provided part                                  *)
(**************************************************)

val num2boolList_def = Define `
  (num2boolList 0 = []) /\
  (num2boolList 1 = []) /\
  (num2boolList n = (EVEN n) :: num2boolList (n DIV 2))`

(* The resulting definition is hard to apply and
   rewriting with it loops easily. So let's provide
   a decent lemma capturing the semantics *)

val num2boolList_REWRS = store_thm ("num2boolList_REWRS",
 ``(num2boolList 0 = []) /\
   (num2boolList 1 = []) /\
   (!n. 2 <= n ==> ((num2boolList n = (EVEN n) :: num2boolList (n DIV 2))))``,
  REPEAT STRIP_TAC >| [
    REWRITE_TAC[num2boolList_def],
    REWRITE_TAC[num2boolList_def],
  
    `n <> 0 /\ n <> 1` by DECIDE_TAC >>
    METIS_TAC[num2boolList_def]
  ]);


(* It is aslo useful to show when the list is empty *)
val num2boolList_EQ_NIL = store_thm ("num2boolList_EQ_NIL",
  ``!n. (num2boolList n = []) <=> ((n = 0) \/ (n = 1))``,
  GEN_TAC >> EQ_TAC >| [
    DISCH_TAC >>
    CCONTR_TAC >>
    FULL_SIMP_TAC list_ss [num2boolList_REWRS],
  
    REPEAT STRIP_TAC >> (
      ASM_SIMP_TAC std_ss [num2boolList_REWRS]
    )
  ]);


(* Now the awkward arithmetic part. Let's show that num2boolList is injective *)

(* For demonstration, let's define our own induction theorem *)
val MY_NUM_INDUCT = store_thm ("MY_NUM_INDUCT",
  ``!P. P 1 /\ (!n. (2 <= n /\ (!m. (m < n /\ m <> 0) ==> P m)) ==> P n) ==> (!n. n <> 0 ==> P n)``,
  REPEAT STRIP_TAC >>
  completeInduct_on `n` >>
  Cases_on `n` >- ( FULL_SIMP_TAC arith_ss [] ) >>
  Cases_on `n'` >> ASM_SIMP_TAC arith_ss []
  )

val num2boolList_INJ = store_thm ("num2boolList_INJ",
  ``!n. n <> 0 ==> !m. m <> 0 ==> (num2boolList n = num2boolList m) ==> (n = m)``,
  HO_MATCH_MP_TAC MY_NUM_INDUCT >>
  CONJ_TAC >- (
    SIMP_TAC list_ss [num2boolList_REWRS, num2boolList_EQ_NIL]
  ) >>
  GEN_TAC >> STRIP_TAC >> GEN_TAC >> STRIP_TAC >>
  Cases_on `m = 1` >- (
    ASM_SIMP_TAC list_ss [num2boolList_REWRS]
  ) >>
  ASM_SIMP_TAC list_ss [num2boolList_REWRS] >>
  REPEAT STRIP_TAC >>
  `n DIV 2 = m DIV 2` by (
    `(m DIV 2 <> 0) /\ (n DIV 2 <> 0) /\ (n DIV 2 < n)` suffices_by METIS_TAC[] >>
  
    ASM_SIMP_TAC arith_ss [arithmeticTheory.NOT_ZERO_LT_ZERO,
      arithmeticTheory.X_LT_DIV]
  ) >>
  `n MOD 2 = m MOD 2` by (
    ASM_SIMP_TAC std_ss [arithmeticTheory.MOD_2]
  ) >>
  `0 < 2` by DECIDE_TAC >>
  METIS_TAC[arithmeticTheory.DIVISION]
  );



(* Shifting the keys by one is trivial and by this we get rid of the
   preconditions of the injectivity theorem *)
val num2arrayIndex_def = Define `num2arrayIndex n = (num2boolList (SUC n))`
val num2arrayIndex_INJ = store_thm ("num2arrayIndex_INJ",
  ``!n m. (num2arrayIndex n = num2arrayIndex m) <=> (n = m)``,
  REWRITE_TAC[num2arrayIndex_def] >>
  METIS_TAC [numTheory.NOT_SUC, num2boolList_INJ, numTheory.INV_SUC]);


(* Now let's define the inverse operation *)
val boolList2num_def = Define `
  (boolList2num [] = 1) /\
  (boolList2num (F::idx) = 2 * boolList2num idx + 1) /\
  (boolList2num (T::idx) = 2 * boolList2num idx)`

(* We can show that the inverse is never 0 ... *)
val boolList2num_GT_0 = prove (``!idx. 0 < boolList2num idx``,
  Induct >- SIMP_TAC arith_ss [boolList2num_def] >>
  Cases >> ASM_SIMP_TAC arith_ss [boolList2num_def]);

(* ... so we can subtract 1 for the index shift *)
val arrayIndex2num_def = Define `arrayIndex2num idx = PRE (boolList2num idx)`



(* Now a fiddly prove that we indeed defined the inverse *)
val boolList2num_inv = prove (``!idx. num2boolList (boolList2num idx) = idx``,
  Induct >- (
    SIMP_TAC arith_ss [boolList2num_def, num2boolList_REWRS]
  ) >>
  `0 < boolList2num idx` by METIS_TAC[boolList2num_GT_0] >>
  `0 < 2` by DECIDE_TAC >>
  Cases >| [
    `!x. (2 * x) MOD 2 = 0` by
       METIS_TAC[arithmeticTheory.MOD_EQ_0, arithmeticTheory.MULT_COMM] >>
    `!x. (2 * x) DIV 2 = x` by
       METIS_TAC[arithmeticTheory.MULT_DIV, arithmeticTheory.MULT_COMM] >>
    ASM_SIMP_TAC list_ss [boolList2num_def, num2boolList_REWRS,
      arithmeticTheory.EVEN_MOD2],
  
    `!x y. (2 * x + y) MOD 2 = (y MOD 2)` by
       METIS_TAC[arithmeticTheory.MOD_TIMES, arithmeticTheory.MULT_COMM] >>
    `!x y. (2 * x + y) DIV 2 = x + y DIV 2` by
       METIS_TAC[arithmeticTheory.ADD_DIV_ADD_DIV, arithmeticTheory.MULT_COMM] >>
    ASM_SIMP_TAC list_ss [boolList2num_def, num2boolList_REWRS,
      arithmeticTheory.EVEN_MOD2]
  ]);

(* Shifting is easy then *)
val arrayIndex2num_inv = store_thm ("arrayIndex2num_inv",
  ``!idx. num2arrayIndex (arrayIndex2num idx) = idx``,
  GEN_TAC >>
  REWRITE_TAC[num2arrayIndex_def, arrayIndex2num_def] >>
  `0 < boolList2num idx` by METIS_TAC[boolList2num_GT_0] >>
  FULL_SIMP_TAC arith_ss [arithmeticTheory.SUC_PRE] >>
  ASM_SIMP_TAC std_ss [boolList2num_inv]
  );


(* It is also very easy to derive other useful properties. *)
val num2arrayIndex_inv = store_thm ("num2arrayIndex_inv",
  ``!n. arrayIndex2num (num2arrayIndex n) = n``,
  METIS_TAC[ num2arrayIndex_INJ, arrayIndex2num_inv]);

val arrayIndex2num_INJ = store_thm ("arrayIndex2num_INJ",
  ``!idx1 idx2. (arrayIndex2num idx1 = arrayIndex2num idx2) <=> (idx1 = idx2)``,
  METIS_TAC[ num2arrayIndex_INJ, arrayIndex2num_inv]);


(* A rewrite for the top-level inverse might be handy *)
val num2arrayIndex_REWRS = store_thm ("num2arrayIndex_REWRS", ``
  !n. num2arrayIndex n =  if (n = 0) then [] else
                          ODD n :: num2arrayIndex ((n - 1) DIV 2)``,
  REWRITE_TAC[num2arrayIndex_def] >>
  Cases >> SIMP_TAC arith_ss [num2boolList_REWRS] >>
  SIMP_TAC arith_ss [arithmeticTheory.ODD, arithmeticTheory.EVEN,
    arithmeticTheory.ODD_EVEN] >>
  `(!x r. (2 * x + r) DIV 2 = x + r DIV 2) /\ (!x. (2*x) DIV 2 = x)` by (
    `0 < 2` by DECIDE_TAC >>
    METIS_TAC[arithmeticTheory.ADD_DIV_ADD_DIV, arithmeticTheory.MULT_COMM,
      arithmeticTheory.MULT_DIV]
  ) >>
  Cases_on `EVEN n'` >> ASM_REWRITE_TAC[] >| [
    `?m. n' = 2* m` by METIS_TAC[arithmeticTheory.EVEN_ODD_EXISTS] >>
    ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD1],
  
    `?m. n' = SUC (2* m)` by METIS_TAC[arithmeticTheory.EVEN_ODD_EXISTS,
      arithmeticTheory.ODD_EVEN] >>
    ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD1]
  ]);


(**************************************************)
(* YOU SHOULD WORK FROM HERE ON                   *)
(**************************************************)

open simpLib;

(* Define a datatype for arrays storing values of type 'a. *)
val _ = Datatype `array = Leaf | Node array ('a option) array`

(* Define a new, empty array *)
val EMPTY_ARRAY_def = Define `EMPTY_ARRAY : 'a array = Leaf`

(* Define ILOOKUP, IUPDATE and IREMOVE *)
val IGUPDATE_def = Define `
  (IGUPDATE v Leaf [] = Node Leaf v Leaf) ∧
  (IGUPDATE v Leaf (F::idx) = Node (IGUPDATE v Leaf idx) NONE Leaf) ∧
  (IGUPDATE v Leaf (T::idx) = Node Leaf NONE (IGUPDATE v Leaf idx)) ∧
  (IGUPDATE v (Node l _ r) [] = Node l v r) ∧
  (IGUPDATE v (Node l n r) (F::idx) = Node (IGUPDATE v l idx) n r) ∧
  (IGUPDATE v (Node l n r) (T::idx) = Node l n (IGUPDATE v r idx)) `
val IUPDATE_def = Define `
  IUPDATE v a idx = IGUPDATE (SOME v) a idx`
val ILOOKUP_def = Define `
  (ILOOKUP Leaf _ = NONE) ∧
  (ILOOKUP (Node _ v _) [] = v) ∧
  (ILOOKUP (Node l _ _) (F::idx) = ILOOKUP l idx) ∧
  (ILOOKUP (Node _ _ r) (T::idx) = ILOOKUP r idx)`
val IREMOVE_def = Define `
  IREMOVE a idx = IGUPDATE NONE a idx`

(* With these, we can define the lifted operations *)
val LOOKUP_def = Define `LOOKUP a n = ILOOKUP a (num2arrayIndex n)`
val UPDATE_def = Define `UPDATE v a n = IUPDATE v a (num2arrayIndex n)`
val REMOVE_def = Define `REMOVE a n = IREMOVE a (num2arrayIndex n)`;

(* Store the definitions together for easy rewriting *)
val idef_thms = [
  EMPTY_ARRAY_def,
  IREMOVE_def,
  IGUPDATE_def, IUPDATE_def,
  ILOOKUP_def
];
val idef_ss = list_ss ++ (rewrites idef_thms);
val def_thms = [LOOKUP_def, UPDATE_def, REMOVE_def];
val def_ss = idef_ss ++ (rewrites def_thms);

(* Helper definitions & theorems *)
val VAL_OF_ROOT_def = Define `(VAL_OF_ROOT Leaf = NONE) ∧ (VAL_OF_ROOT (Node _ root _) = root)`;
val ILOOKUP_ROOT = store_thm ("ILOOKUP_ROOT",
  ``!a. ILOOKUP a [] = VAL_OF_ROOT a``,
  Cases_on `a` >> REWRITE_TAC[ILOOKUP_def, VAL_OF_ROOT_def]
  );

val GEN_GET_SUBARRAY_def = Define `
    (GEN_GET_SUBARRAY _ Leaf         = Leaf)
  ∧ (GEN_GET_SUBARRAY F (Node l _ _) = l   )
  ∧ (GEN_GET_SUBARRAY T (Node _ _ r) = r   )
`;
val ILOOKUP_SUBARRAY = store_thm ("ILOOKUP_SUBARRAY",
  ``!a i idx. ILOOKUP a (i::idx) = ILOOKUP (GEN_GET_SUBARRAY i a) idx``,
  Cases_on `a` >>
  Cases_on `i` >>
  REWRITE_TAC[GEN_GET_SUBARRAY_def, ILOOKUP_def]
);

val helper_thms = [
  VAL_OF_ROOT_def, ILOOKUP_ROOT,
  GEN_GET_SUBARRAY_def, ILOOKUP_SUBARRAY
]
val helper_ss = def_ss ++ (rewrites helper_thms);

(* Show a few properties *)
(** First, we prove some lemmatas **)

val num2arrayIndex_boolList_DIFF_EQ = store_thm ("num2arrayIndex_boolList_DIFF_EQ",
  ``!n m. (n ≠ m) ⇔ (num2arrayIndex n ≠ num2arrayIndex m)``,
  REPEAT GEN_TAC >>
  EQ_TAC >| [
    REWRITE_TAC[CONTRAPOS (fst (EQ_IMP_RULE (SPEC_ALL num2arrayIndex_INJ)))],
    REWRITE_TAC[CONTRAPOS (snd (EQ_IMP_RULE (SPEC_ALL num2arrayIndex_INJ)))]
]);

(*
val ARRAY_EQ = store_thm ("ARRAY_EQ", ``
  !l1 l2 r1 r2 v1 v2. ((l1 = l2) ∧ (r1 = r2) ∧ (v1 = v2)) 
                    ⇔ ((Node l1 v1 r1) = (Node l2 v2 r2))``,
  REPEAT STRIP_TAC >>
  EQ_TAC >| [
    Cases_on 
  ]
);
*)

val lemmatas_thms = [
  num2arrayIndex_boolList_DIFF_EQ
]
val lemmatas_ss = helper_ss ++ (rewrites lemmatas_thms);

(** Then, we prove some theorems in the not-lifted definitions **)

val ILOOKUP_EMPTY = store_thm ("ILOOKUP_EMPTY",
  ``!idx. ILOOKUP EMPTY_ARRAY idx = NONE``,
  SIMP_TAC lemmatas_ss []
);

val ILOOKUP_UPDATE_SAME = store_thm ("ILOOKUP_UPDATE_SAME",
  ``!v a idx. ILOOKUP (IGUPDATE v a idx) idx = v``,
  Induct_on `idx` >> Induct_on `a` >>
  TRY (Cases_on `h`) >>
  FULL_SIMP_TAC lemmatas_ss []
);

val ILOOKUP_UPDATE_DIFF = store_thm ("ILOOKUP_UPDATE_DIFF",
  ``!v a idx idx'. (idx ≠ idx' ⇒ (ILOOKUP (IGUPDATE v a idx) idx' = ILOOKUP a idx'))``,
  Induct_on `idx` >> Induct_on `idx'` >> Induct_on `a` >>
  TRY (Cases_on `h`) >> TRY (Cases_on `h'`) >>
  FULL_SIMP_TAC lemmatas_ss []
);

val ILOOKUP_IUPDATE = store_thm ("ILOOKUP_IUPDATE",
  ``!idx idx' v a. ILOOKUP (IGUPDATE v a idx) idx' =
      (if (idx = idx') then v else ILOOKUP a idx')``,
  NTAC 2 GEN_TAC >>
  Cases_on `idx = idx'` >>
  FULL_SIMP_TAC lemmatas_ss [ILOOKUP_UPDATE_SAME, ILOOKUP_UPDATE_DIFF]
);

val ILOOKUP_IREMOVE_SAME = store_thm ("ILOOKUP_IREMOVE_SAME",
  ``!idx a. ILOOKUP (IREMOVE a idx) idx = NONE``,
  Induct_on `idx` >> Induct_on `a` >>
  TRY (Cases_on `h`) >>
  FULL_SIMP_TAC lemmatas_ss []
);

val ILOOKUP_IREMOVE_DIFF = store_thm ("ILOOKUP_IREMOVE_DIFF",
  ``!idx idx' a. idx ≠ idx' ⇒ (ILOOKUP (IREMOVE a idx) idx' = ILOOKUP a idx')``,
  Induct_on `idx` >> Induct_on `idx'` >> Induct_on `a` >>
  TRY (Cases_on `h`) >>
  TRY (Cases_on `h'`) >>
  FULL_SIMP_TAC lemmatas_ss []
);

val ILOOKUP_IREMOVE = store_thm ("ILOOKUP_IREMOVE",
  ``!idx idx' a. ILOOKUP (IREMOVE a idx) idx' =
       (if (idx = idx') then NONE else ILOOKUP a idx')``,
  NTAC 2 GEN_TAC >>
  Cases_on `idx = idx'` >>
  ASM_SIMP_TAC list_ss [] >> (* TODO: (remove) Needed because of rewrite orders (I think) *)
  FULL_SIMP_TAC lemmatas_ss [ILOOKUP_IREMOVE_SAME, ILOOKUP_IREMOVE_DIFF]
);

val IUPDATE_TWICE_EQ = store_thm ("IUPDATE_TWICE_EQ",
  ``(!v1 v2 idx a. IGUPDATE v1 (IGUPDATE v2 a idx) idx = IGUPDATE v1 a idx)``,
  Induct_on `idx` >> Induct_on `a` >>
  TRY (Cases_on `h`) >>
  FULL_SIMP_TAC lemmatas_ss []
);

val IUPDATE_IREMOVED_EQ = store_thm ("IUPDATE_IREMOVED_EQ",
  ``(!v idx a. IGUPDATE v (IREMOVE a idx) idx = IGUPDATE v a idx)``,
  Induct_on `idx` >> Induct_on `a` >>
  TRY (Cases_on `h`) >>
  FULL_SIMP_TAC lemmatas_ss []
);

val IREMOVE_IUPDATED_EQ = store_thm ("IREMOVE_IUPDATED_EQ",
  ``(!v idx a. IREMOVE (IGUPDATE v a idx) idx = IREMOVE a idx)``,
  Induct_on `idx` >> Induct_on `a` >>
  TRY (Cases_on `h`) >>
  FULL_SIMP_TAC lemmatas_ss []
);

val IUPDATE_IREMOVE_EQ = store_thm ("IUPDATE_IREMOVE_EQ", ``
    (!v w idx a. IGUPDATE v (IGUPDATE w a idx) idx = IGUPDATE v a idx)
  ∧ (!v   idx a. IGUPDATE v (IREMOVE    a idx) idx = IGUPDATE v a idx)
  ∧ (!v   idx a. IREMOVE    (IGUPDATE v a idx) idx = IREMOVE    a idx)``,
  SIMP_TAC lemmatas_ss [IUPDATE_TWICE_EQ, IUPDATE_IREMOVED_EQ, IREMOVE_IUPDATED_EQ]
);

val IUPDATE_DIFF_EQ = store_thm ("IUPDATE_DIFF_EQ",
  ``(!v w a idx idx'. idx ≠ idx'
    ⇒ ((IGUPDATE v (IGUPDATE w a idx') idx) = (IGUPDATE w (IGUPDATE v a idx) idx')))``,
  (* Induct_on `idx` >> Induct_on `idx'` >> Induct_on `a` >> *)
  Induct_on `a` >> Induct_on `idx` >> Induct_on `idx'` >>
  TRY (Cases_on `h`) >>
  TRY (Cases_on `h'`) >>
  FULL_SIMP_TAC lemmatas_ss [] >>
  SPEC_TAC (``idx': bool list``, ``idx': bool list``)
  

  (*
  UNDISCH_TAC ``idx ≠ idx': bool list``
  SPEC_TAC (``idx': bool list``, ``idx': bool list``)
  ASM_REWRITE_TAC[]
  REWRITE_TAC[]
  RW_TAC lemmatas_ss []
  *)
);

val IUPDATE_IREMOVE_NEQ = store_thm ("IUPDATE_IREMOVE_NEQ",
  ``(!v a n m. n ≠ m ⇒ ((IGUPDATE v (IREMOVE a m) n) = (IREMOVE (IGUPDATE v a n) m)))``,
  FULL_SIMP_TAC lemmatas_ss [...]
);

val IUPDATE_IREMOVE_NEQ = store_thm ("IUPDATE_IREMOVE_NEQ", ``
  ``(!v w a n m. n ≠ m ⇒ ((IGUPDATE v (IGUPDATE w a m) n) = (IGUPDATE w (IGUPDATE v a n) m)))``,
  FULL_SIMP_TAC lemmatas_ss [...]
);

val IUPDATE_IREMOVE_NEQ = store_thm ("IUPDATE_IREMOVE_NEQ", ``
    (!v w a n m. n ≠ m ⇒ ((IGUPDATE v (IGUPDATE w a m) n) = (IGUPDATE w (IGUPDATE v a n) m)))
  ∧ (!v   a n m. n ≠ m ⇒ ((IGUPDATE v (IREMOVE    a m) n) = (IREMOVE    (IGUPDATE v a n) m)))
  ∧ (!    a n m. n ≠ m ⇒ ((IREMOVE    (IREMOVE    a m) n) = (IREMOVE    (IREMOVE    a n) m)))``,
  SIMP_TAC lemmatas_ss [...]
);

val non_lifted_thms = [
  ILOOKUP_EMPTY,
  ILOOKUP_UPDATE_SAME, ILOOKUP_UPDATE_DIFF, ILOOKUP_IUPDATE,
  ILOOKUP_IREMOVE_SAME, ILOOKUP_UPDATE_DIFF, ILOOKUP_IREMOVE,
  IUPDATE_TWICE_EQ, IUPDATE_IREMOVED_EQ, IREMOVE_IUPDATED_EQ, IUPDATE_IREMOVE_EQ
]
val non_lifted_ss = lemmatas_ss ++ (rewrites non_lifted_thms);

(** Finally, the lifted theorems **)
val LOOKUP_EMPTY = store_thm ("LOOKUP_EMPTY",
  ``!n. LOOKUP EMPTY_ARRAY n = NONE``,
  FULL_SIMP_TAC non_lifted_ss []
);

val LOOKUP_UPDATE = store_thm ("LOOKUP_UPDATE",
  ``!n n' v a. LOOKUP (UPDATE v a n) n' =
       (if (n = n') then SOME v else LOOKUP a n')``,
  REWRITE_TAC def_thms >>
  NTAC 2 GEN_TAC >>
  Cases_on `n = n'` >>
  (* TODO: Use REVERSE + THEN1/>- ? *)
  TRY (`num2arrayIndex n ≠ num2arrayIndex n'` by FULL_SIMP_TAC non_lifted_ss []) >>
  ASM_SIMP_TAC non_lifted_ss [num2arrayIndex_boolList_DIFF_EQ]
);

val LOOKUP_REMOVE = store_thm ("LOOKUP_REMOVE",
  ``!n n' a. LOOKUP (REMOVE a n) n' =
      (if (n = n') then NONE else LOOKUP a n')``,
  REWRITE_TAC def_thms >>
  NTAC 2 GEN_TAC >>
  Cases_on `n = n'` >>
  (* TODO: Use REVERSE + THEN1/>- ? *)
  TRY (`num2arrayIndex n ≠ num2arrayIndex n'` by FULL_SIMP_TAC non_lifted_ss []) >>
  ASM_SIMP_TAC non_lifted_ss [num2arrayIndex_boolList_DIFF_EQ]
);

val UPDATE_REMOVE_EQ = store_thm ("UPDATE_REMOVE_EQ", ``
    (!v w n a. UPDATE v (UPDATE w a n) n = UPDATE v a n)
  ∧ (!v   n a. UPDATE v (REMOVE   a n) n = UPDATE v a n)
  ∧ (!v   n a. REMOVE   (UPDATE v a n) n = REMOVE   a n)``,
  SIMP_TAC non_lifted_ss []
);

val UPDATE_REMOVE_NEQ = store_thm ("UPDATE_REMOVE_NEQ", ``
    (!v w a n m. n ≠ m ⇒ ((UPDATE v (UPDATE w a m) n) = (UPDATE w (UPDATE v a n) m)))
  ∧ (!v   a n m. n ≠ m ⇒ ((UPDATE v (REMOVE   a m) n) = (REMOVE   (UPDATE v a n) m)))
  ∧ (!    a n m. n ≠ m ⇒ ((REMOVE   (REMOVE   a m) n) = (REMOVE   (REMOVE   a n) m)))``,
  SIMP_TAC non_lifted_ss []
);


val _ = export_theory();

