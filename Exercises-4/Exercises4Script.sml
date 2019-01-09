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

(* Helper definitions & functions *)
val LOOKUP_LEAF = store_thm ("LOOKUP_LEAF",
  ``!n. LOOKUP Leaf n = NONE``,
  REWRITE_TAC[LOOKUP_def, ILOOKUP_def]
  );

val VAL_OF_ROOT_def = Define `(VAL_OF_ROOT Leaf = NONE) ∧ (VAL_OF_ROOT (Node _ root _) = root)`;
val ILOOKUP_ROOT = store_thm ("ILOOKUP_ROOT",
  ``!a. ILOOKUP a [] = VAL_OF_ROOT a``,
  Cases_on `a` >> REWRITE_TAC[ILOOKUP_def, VAL_OF_ROOT_def]
  );

val GEN_GET_SUBARRAY_def = Define `
  (GEN_GET_SUBARRAY _ Leaf = Leaf)
  ∧ (GEN_GET_SUBARRAY F (Node l _ _) = l)
  ∧ (GEN_GET_SUBARRAY T (Node _ _ r) = r)`;
val ILOOKUP_SUBARRAY = store_thm ("ILOOKUP_SUBARRAY",
  ``!a i idx. ILOOKUP a (i::idx) = ILOOKUP (GEN_GET_SUBARRAY i a) idx``,
  Cases_on `a` >| [
    REWRITE_TAC[GEN_GET_SUBARRAY_def, ILOOKUP_def],
    Cases_on `i` >>
    REWRITE_TAC[GEN_GET_SUBARRAY_def, ILOOKUP_def]
  ]
  );

val ILOOKUP_ONLY_LEAF_IS_NONE = store_thm ("ILOOKUP_ONLY_LEAF_IS_NONE",
  ``∀v h. ILOOKUP (Node Leaf (SOME v) Leaf) (h::_) = NONE``,
  Cases_on `h` >> REWRITE_TAC[ILOOKUP_def]
  );

(*
val SUC_SUBST_ONE = store_thm ("SUC_SUBST_ONE",
  ``!n. n > 0 ==> SUC (n - 1) = n``,
  SIMP_TAC arith_ss []
  );
*)

open arithmeticTheory;
val ARRAY_INDEX_INJ_NUM = store_thm ("ARRAY_INDEX_INJ_NUM",
  ``∀s. ?n. s = num2arrayIndex n``,
  REWRITE_TAC[num2arrayIndex_def] >>
  Induct_on `s` >| [
    EXISTS_TAC ``0`` >>
    SIMP_TAC arith_ss [EVAL ``num2boolList 1``],
    Cases_on `h` >| [
      Q.REFINE_EXISTS_TAC `2 * n - 1` >>
      SIMP_TAC arith_ss [EVAL ``SUC (m - 1)``]
      EVAL ``SUC (n - 1)``

      EXISTS_TAC ``1``
      REWRITE_TAC[EVAL ``SUC 1``]
      REWRITE_TAC[EVAL ``num2boolList 2``]
      FULL_SIMP_TAC list_ss []

      SUBGOAL_THEN ``num2boolList (SUC 0) = []`` (fn th => ASSUME_TAC th) >> (
        SIMP_TAC list_ss [num2boolList_REWRS]
      ) >>
      RES_TAC
      FULL_SIMP_TAC list_ss []

      REWRITE_TAC[num2boolList_REWRS]
      
    ]
  ]
  );

(* Show a few properties *)
(* val EMPTY_ARRAY_def = Define `EMPTY_ARRAY : 'a array = Node Leaf NONE Leaf`
val LOOKUP_EMPTY = store_thm ("LOOKUP_EMPTY",
  ``!k. LOOKUP EMPTY_ARRAY k = NONE``,
  REWRITE_TAC[EMPTY_ARRAY_def, LOOKUP_def, ILOOKUP_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `(num2arrayIndex k)` >| [
    REWRITE_TAC[ILOOKUP_def],
    Cases_on `h` >>
    REWRITE_TAC[ILOOKUP_def]
  ]); *)
val LOOKUP_EMPTY = store_thm ("LOOKUP_EMPTY",
  ``!k. LOOKUP EMPTY_ARRAY k = NONE``,
  REWRITE_TAC[EMPTY_ARRAY_def, LOOKUP_def, ILOOKUP_def]
  );

val LOOKUP_UPDATE_SIMPLE = store_thm ("LOOKUP_UPDATE_SIMPLE",
  ``!v a idx. LOOKUP (UPDATE v a idx) idx = SOME v``,
  REWRITE_TAC[LOOKUP_def, UPDATE_def, IUPDATE_def] >>
  REWRITE_TAC[num2arrayIndex_def] >>
  Induct_on `a` >| [
    (* ∀v idx. LOOKUP (UPDATE v Leaf idx) idx = SOME v *)
    Cases_on `(num2boolList (SUC idx))` >| [
      REWRITE_TAC[IUPDATE_def, ILOOKUP_def, IGUPDATE_def],
      Cases_on `h` >> REWRITE_TAC[IUPDATE_def, IGUPDATE_def, ILOOKUP_def] >| [
        (* TODO: Factor this *)
        Induct_on `t` >| [
          REWRITE_TAC[IUPDATE_def, ILOOKUP_def, IGUPDATE_def],
          Cases_on `h` >> ASM_REWRITE_TAC[IUPDATE_def, IGUPDATE_def, ILOOKUP_def]
        ],
        Induct_on `t` >| [
          REWRITE_TAC[IUPDATE_def, ILOOKUP_def, IGUPDATE_def],
          Cases_on `h` >> ASM_REWRITE_TAC[IUPDATE_def, IGUPDATE_def, ILOOKUP_def]
        ]
      ]
    ],
    (* ∀ $o v idx. LOOKUP (UPDATE v (Node a $o a') idx) idx = SOME v
       ------------------------------------
       0.  ∀v idx. LOOKUP (UPDATE v a idx) idx = SOME v
       1.  ∀v idx. LOOKUP (UPDATE v a' idx) idx = SOME v *)
    Cases_on `idx` >| [
      ASSUME_TAC (EVAL ``SUC 0``) >> ASM_REWRITE_TAC[] >>
      REWRITE_TAC[num2boolList_def] >>
      REWRITE_TAC[IGUPDATE_def, LOOKUP_def, ILOOKUP_def],
      
      ONCE_REWRITE_TAC[num2boolList_def] >>
      SIMP_TAC arith_ss [] >>
      SPEC_TAC (``n: num``, ``n: num``) >>
      Cases_on `EVEN (SUC (SUC n))` >| [
        (* idx is (T::) -> right node *)
        REWRITE_TAC[IGUPDATE_def, ILOOKUP_def] >>
        (* TODO: Factor this *)
        Cases_on `SUC (SUC n) DIV 2` >| [
          REWRITE_TAC[num2boolList_def] >>
          Cases_on `a'` >> REWRITE_TAC[IUPDATE_def, IGUPDATE_def, ILOOKUP_def],
          SPEC_TAC (``n': num``, ``idx: num``) >>
          ASM_REWRITE_TAC[]
        ],
        (* idx is (F::) -> left node *)
        REWRITE_TAC[IGUPDATE_def, ILOOKUP_def] >>
        Cases_on `SUC (SUC n) DIV 2` >| [
          REWRITE_TAC[num2boolList_def] >>
          Cases_on `a` >> REWRITE_TAC[IUPDATE_def, IGUPDATE_def, ILOOKUP_def],
          SPEC_TAC (``n': num``, ``idx: num``) >>
          ASM_REWRITE_TAC[]
        ]
      ]
    ]
  ]
  );

(* STRIP_ASSUME_TAC (SPEC_ALL num2arrayIndex_INJ_CONTR) >> RES_TAC >> *)
val num2arrayIndex_INJ_CONTR = store_thm ("num2arrayIndex_INJ_CONTR",
  ``!n m. (n ≠ m) ⇔ (num2arrayIndex n ≠ num2arrayIndex m)``,
  REPEAT GEN_TAC >>
  EQ_TAC >| [
    REWRITE_TAC[CONTRAPOS (fst (EQ_IMP_RULE (SPEC_ALL num2arrayIndex_INJ)))],
    REWRITE_TAC[CONTRAPOS (snd (EQ_IMP_RULE (SPEC_ALL num2arrayIndex_INJ)))]
  ]);

val LOOKUP_UPDATE_DIFF_N = store_thm ("LOOKUP_UPDATE_DIFF_N",
  ``n ≠ m ⇒ !v a. LOOKUP (UPDATE v a n) m = LOOKUP a m``,
  DISCH_TAC >>
  Induct_on `a` >| [
    (* Base case *)
    REWRITE_TAC[LOOKUP_def, UPDATE_def] >>
    UNDISCH_TAC ``n ≠ m: num`` >>
    SPEC_TAC (``n: num``, ``n: num``) >> SPEC_TAC (``m: num``, ``m: num``) >>
    Induct_on `(num2arrayIndex n)` >| [
      REPEAT STRIP_TAC >>
      SUBGOAL_THEN ``num2arrayIndex n = []`` (fn th => ONCE_ASM_REWRITE_TAC[th]) >> METIS_TAC[] >>
      Cases_on `(num2arrayIndex m)` >| [
        METIS_TAC[num2arrayIndex_INJ],
        REWRITE_TAC[IUPDATE_def, IGUPDATE_def, ILOOKUP_def] >>
        Cases_on `h` >> REWRITE_TAC[ILOOKUP_def]
      ]
    ],
    (* Induction step *)
    Cases_on `h` >| [
      REPEAT STRIP_TAC >>
      `num2arrayIndex n = T::v` by ASM_REWRITE_TAC[],
      PAT_X_ASSUM ``_ = _::_`` (fn th => ONCE_ASM_REWRITE_TAC[th]) >>
      REWRITE_TAC[IUPDATE_def, IGUPDATE_def] >>
      Cases_on `num2arrayIndex m` >| [
        REWRITE_TAC[ILOOKUP_def],
        Cases_on `h` >| [
          REWRITE_TAC[Once ILOOKUP_def] >>
          SUBGOAL_THEN ``ILOOKUP Leaf (T::t) = ILOOKUP Leaf t`` (fn th => REWRITE_TAC[th]) >>
          REWRITE_TAC[ILOOKUP_def] >>
          SUBGOAL_THEN ``IGUPDATE (SOME v') Leaf v = IUPDATE v' Leaf v`` (fn th => REWRITE_TAC[th]) >>
          REWRITE_TAC[IUPDATE_def] >>
          (* Useless, but I'm so happy to have found this function :D *)
          Q.MATCH_RENAME_TAC `ILOOKUP (IUPDATE tmp Leaf s) t = _` >>
          Q.MATCH_RENAME_TAC `ILOOKUP (IUPDATE v Leaf s) t = _` >>
          SPEC_TAC (``v: 'a``, ``v: 'a``) >>
          (**)
          `s ≠ t` by METIS_TAC[num2arrayIndex_INJ] >>






        , REWRITE_TAC[ILOOKUP_def]
      ]
    ]
  ]
  );
(*
  DISCH_TAC >>
  Cases_on `a` >| [
    REWRITE_TAC[UPDATE_def, LOOKUP_def, ILOOKUP_def, IUPDATE_def] >>
    STRIP_ASSUME_TAC (SPEC_ALL num2arrayIndex_INJ_CONTR) >> RES_TAC >>
    Cases_on `(num2arrayIndex n)` >| [
      Cases_on `(num2arrayIndex m)` >| [
        METIS_TAC[],
        REWRITE_TAC[IGUPDATE_def, ILOOKUP_ONLY_LEAF_IS_NONE]
      ],
      Cases_on `(num2arrayIndex m)` >| [
        Cases_on `h` >> REWRITE_TAC[IGUPDATE_def, ILOOKUP_def],
        Cases_on `h` >> REWRITE_TAC[IGUPDATE_def] >| [
          Cases_on `h'` >> REWRITE_TAC[ILOOKUP_def]
        ]
      ]
    ]
  ]
  ); *)

val LOOKUP_UPDATE = store_thm ("LOOKUP_UPDATE",
  ``!n n' v a. LOOKUP (UPDATE v a n) n' =
       (if (n = n') then SOME v else LOOKUP a n')``,
  NTAC 2 GEN_TAC >>
  Cases_on `n = n'` >| [
    ASM_REWRITE_TAC[LOOKUP_UPDATE_SIMPLE],
    ASM_REWRITE_TAC[] >>
    UNDISCH_TAC ``n: num ≠ n'`` >>
    ASM_REWRITE_TAC[LOOKUP_UPDATE_DIFF_N]
  ]
  );

val LOOKUP_REMOVE = store_thm ("LOOKUP_REMOVE",
  ``!n n' a. LOOKUP (REMOVE a n) n' =
       (if (n = n') then NONE else LOOKUP a n')``,
cheat);


val UPDATE_REMOVE_EQ = store_thm ("UPDATE_REMOVE_EQ", ``
  (!v1 v2 n a. UPDATE v1 (UPDATE v2 a n) n = UPDATE v1 a n) /\
  (!v n a. UPDATE v (REMOVE a n) n = UPDATE v a n) /\
  (!v n a. REMOVE (UPDATE v a n) n = REMOVE a n)
``,
cheat);


val UPDATE_REMOVE_NEQ = store_thm ("UPDATE_REMOVE_NEQ", ``
  (!v1 v2 a n1 n2. n1 <> n2 ==>
     ((UPDATE v1 (UPDATE v2 a n2) n1) = (UPDATE v2 (UPDATE v1 a n1) n2))) /\
  (!v a n1 n2. n1 <> n2 ==>
     ((UPDATE v (REMOVE a n2) n1) = (REMOVE (UPDATE v a n1) n2))) /\
  (!a n1 n2. n1 <> n2 ==>
     ((REMOVE (REMOVE a n2) n1) = (REMOVE (REMOVE a n1) n2)))``,
cheat);


val _ = export_theory();

