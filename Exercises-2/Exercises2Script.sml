(* 1.2 HOL Documentation

See: https://hol-theorem-prover.org/guidebook/#finding-theorems

DB.find "skolem";
DB.apropos ``A ∧ A = A``;

2. Terms

2.1 Free and Bound Vars

List the free variables of the following terms:
• (\x. 2 + (7 * x) + y) z
x is the only bound variable, so y and z are free.

• x + y + 2
x and y are free.

• !x. x + 1 > x
x is bound.

• ?x. x = y + 2
x is bound, y is free.


2.2 Alpha Equivalence
Are the following pairs of terms alpha-equivalent?  A simple mark on the sheet is a sufficient
answer.  Also take two colors and mark all occurences of free vars in one color and all occourences
of bound vars in the other.  Assume that x, y, z, a and b are variables.

Instead of colors, upper-case variable are free.

• \x. x               \y. y
Alpha-equivalent.

• (\x. x) A           (\y. y) A
Alpha-equivalent.

• (\x. x) A           (\y. y) B
Not alpha-equivalent.

• (\x. x)             (\x. Y)
Not alpha-equivalent.

• (\x y. x ∧ y)      (\y x. x ∧ y)
Logically the equivalent but not alpha-equivalent.

• (\x y. x ∧ y) A A  (\y x. x ∧ y) A A
Logically the equivalent but not alpha-equivalent.

• A ∧ B              A ∧ B
Not alpha-equivalent.

• !x. x + 1 > x       !y. y + 1 > y
Alpha-equivalent.

• ?x. x = Y + 2       ?x. x = z + 2
Not alpha-equivalent.

• !y. ?x. x = y + 2   !z. ?x. x = z + 2
Alpha-equivalent.


2.3 Constructing Terms
Write a SML function mk_imp_conj_term : int -> term that constructs for inputs
n greater than 1 the term !A1 ... An. A1 ⇒ ... ⇒ An ⇒ (A1 ∧ ... ∧ An).  If n is
not greater than one, a HOL_ERR exception (use failwith).  You might want to read
up on boolSyntax for this exercise. You can use list-make-functions like
mk_list_conj, but also use non-list ones.

help "boolSyntax";

*)

fun mk_an_var n = mk_var("A" ^ Int.toString n, bool);

fun mk_list_an_vars 0 = []
  | mk_list_an_vars n = (mk_an_var n) :: (mk_list_an_vars (n - 1))

fun mk_imp_conj_term n =
  if n < 1 then failwith ("Invalid n: " ^ Int.toString n) else
  let val list_vars = rev (mk_list_an_vars n)
  in list_mk_exists(list_vars, list_mk_imp(list_vars, list_mk_conj(list_vars)))
  end

(*

mk_imp_conj_term 5

3. Basic Forward Proofs

3.1. Commutativity of Conjunction
Prove the lemma !A B. (A ∧ B) <=> (B ∧ A) using only inferences presented in the lecture.

help "FinalThm";
help "FinalTerm";
help "FinalType";
help "Drule";
help "Psyntax";
help "boolSyntax";
help "Lib";

set_trace "assumptions" 1;

*)

val COMM_CONJ_THM = let
  (* Show ⊢ A ∧ B ⇒ B ∧ A *)
  val thm1_conj_ab = ASSUME ``A ∧ B``;
  val thm1_conj_ba = CONJ (CONJUNCT2 thm1_conj_ab) (CONJUNCT1 thm1_conj_ab);
  val thm1 = DISCH ``A ∧ B`` thm1_conj_ba;

  (* Show ⊢ B ∧ A ⇒ A ∧ B *)
  val thm2_conj_ba = ASSUME ``B ∧ A``;
  val thm2_conj_ab = CONJ (CONJUNCT2 thm2_conj_ba) (CONJUNCT1 thm2_conj_ba);
  val thm2 = DISCH ``B ∧ A`` thm2_conj_ab;

  (* Combine <= and => to <=> *)
  val thm3 = IMP_ANTISYM_RULE thm1 thm2;
in
  (* Add quantifiers *)
  GENL [``A: bool``, ``B: bool``] thm3
end

(*

3.2 Simplifying Conjunction
Prove the lemmas !A. (A ∧ ~A) <=> F and !A B. (A ∧ ~A) ∧ B <=> F.

*)

(* ∀A. A ∧ ¬A ⇔ F *)
val SIMPL1_CONJ_THM = let
  (* Show ⊢ A ∧ ¬A ⇒ F *)
  val thm1_ana = ASSUME ``A ∧ ¬A``;
  val thm1_a = CONJUNCT1 thm1_ana;
  val thm1_na = CONJUNCT2 thm1_ana;
  val thm1_F = MP thm1_na thm1_a;
  val thm1 = DISCH ``A ∧ ¬A`` thm1_F;

  (* Show ⊢ F ⇒ A ∧ ¬A *)
  val thm2 = SPEC ``A ∧ ¬A`` FALSITY;

  (* Combine <= and => to <=> *)
  val thm3 = IMP_ANTISYM_RULE thm1 thm2;
in
  (* Add quantifier *)
  GEN_ALL thm3
end

(*
DB.match [] ``!A. A ∧ F ⇒ F``;
DB.match [] ``!A B. A ∧ B ⇒ B ∧ A``;
DB.match [] ``!A B C. (A ⇔ B) ∧ (B ⇔ C) ⇒ (A ⇔ C)``;
*)

(* ∀A. A ∧ F ⇔ F *)
val CONJ1_F_THM = let
  val thm1_af = ASSUME ``A ∧ F``;
  val thm1_f = CONJUNCT2 thm1_af;
  val thm1 = DISCH ``A ∧ F`` thm1_f;
  val thm2 = SPEC ``A ∧ F`` FALSITY;
  val thm3 = IMP_ANTISYM_RULE thm1 thm2;
in
  GEN_ALL thm3
end

(* ∀A. F ∧ A ⇔ F *)
val CONJ2_F_THM = let
  (* Proved using CONJ1_F_THM instead of using
   * the same method as CONJ1_F_THM. *)

  (* A ∧ B ⇒ B ∧ A *)
  val comm_conj_thm = SPECL [F, ``A: bool``] COMM_CONJ_THM;
  val thm11 = fst (EQ_IMP_RULE comm_conj_thm);

  (* A ∧ F ⇒ F *)
  val conj1_thm = SPEC_ALL CONJ1_F_THM;
  val thm12 = fst (EQ_IMP_RULE conj1_thm);

  (* F ∧ A ⇒ F *)
  val thm1 = IMP_TRANS thm11 thm12;

  (* F ⇒ F ∧ A *)
  val thm2 = SPEC ``F ∧ A`` FALSITY;
in
  GEN_ALL (IMP_ANTISYM_RULE thm1 thm2)
end

(*
DB.match [] ``!A B C. (A ⇔ B) ∧ (A ∧ C) ⇒ (B ∧ C)``;
DB.match [] ``!A B C. (A = B) ∧ (A ∧ C) ⇒ (B ∧ C)``;
DB.match [] ``!A B C. (A ⇒ B) ⇒ ((A ∧ C) ⇒ (B ∧ C))``;
DB.match [] ``!A B C. (A ∧ B ⇔ C) ⇒ (B ∧ A ⇔ C)``;
DB.find "conj";
*)

(* (A ∧ ¬A) ∧ B ⇔ F *)
val SIMPL2_CONJ2_THM = let
  (* (A ∧ ¬A) ∧ B ⇒ F ∧ B *)
  val thm1_eq = CONJ_DISCH ``B: bool`` (SPEC_ALL SIMPL1_CONJ_THM);
  val thm1 = fst (EQ_IMP_RULE thm1_eq);

  (* B ∧ F ⇒ F *)
  val thm2_eq = SPEC ``B: bool`` CONJ1_F_THM;
  val thm2 = fst (EQ_IMP_RULE thm2_eq);

  (* B ∧ (A ∧ ¬A) ⇒ F *)
  val thm3 = IMP_TRANS thm1 thm2;

  (* F ⇒ ... *)
  val thm4 = SPEC ``B ∧ (A ∧ ¬A)`` FALSITY;
in
  GEN_ALL (IMP_ANTISYM_RULE thm3 thm4)
end

val SIMPL2_CONJ1_THM = let
  val thm1_eq = SPECL [``A ∧ ¬A``, ``B: bool``] COMM_CONJ_THM;
  val thm1 = fst (EQ_IMP_RULE thm1_eq);

  val thm2_eq = SPEC_ALL SIMPL2_CONJ2_THM;
  val thm2 = fst (EQ_IMP_RULE thm2_eq);

  val thm3 = IMP_TRANS thm1 thm2;

  val thm4 = SPEC ``(A ∧ ¬A) ∧ B`` FALSITY;
in
  GEN_ALL (IMP_ANTISYM_RULE thm3 thm4)
end

(*

4 Writing Own Automation
4.1 Implications between Conjunctions

help "RedBlackSet";
help "RedBlackMap";

*)

fun path_to_prove_conj_entails_term conj_tm tm =
  if (conj_tm = F) then [] else
  if (conj_tm = tm) then [] else
  let val (lhs, rhs) = dest_conj conj_tm
  in
    if (lhs = tm) then [1] else
    if (rhs = tm) then [2] else
    1::(path_to_prove_conj_entails_term lhs tm)
    handle HOL_ERR _ =>
    2::(path_to_prove_conj_entails_term rhs tm)
  end handle HOL_ERR _ =>
    raise mk_HOL_ERR "Exercise2" "path_to_prove_conj_entails_term" "no path"

(*
Tests:
path_to_prove_conj_entails_term ``A /\ B`` ``A: bool``; (* [1] *)
path_to_prove_conj_entails_term ``A /\ B`` ``B: bool``; (* [2] *)
path_to_prove_conj_entails_term ``(A /\ B) /\ C`` ``A: bool``; (* [1,1] *)
path_to_prove_conj_entails_term ``(A /\ B) /\ C`` ``B: bool``; (* [1,2] *)
path_to_prove_conj_entails_term ``(A /\ B) /\ C`` ``C: bool``; (* [2] *)
path_to_prove_conj_entails_term ``A /\ (B /\ C)`` ``A: bool``; (* [1] *)
path_to_prove_conj_entails_term ``A /\ (B /\ C)`` ``B: bool``; (* [2,1] *)
path_to_prove_conj_entails_term ``A /\ (B /\ C)`` ``C: bool``; (* [2,2] *)
path_to_prove_conj_entails_term ``F`` ``A: bool``; (* [] *)
path_to_prove_conj_entails_term ``F /\ (B /\ C)`` ``Z: bool``; (* [1] *)
path_to_prove_conj_entails_term ``A /\ (F /\ C)`` ``Z: bool``; (* [2,1] *)
path_to_prove_conj_entails_term ``A /\ (B /\ F)`` ``Z: bool``; (* [2,2] *)
*)

fun prove_conj_entails_term conj_thm [] = conj_thm
  | prove_conj_entails_term conj_thm (1::path)
      = prove_conj_entails_term (CONJUNCT1 conj_thm) path
  | prove_conj_entails_term conj_thm (2::path)
      = prove_conj_entails_term (CONJUNCT2 conj_thm) path
  | prove_conj_entails_term _ _ = fail()

(*
Tests:
prove_conj_entails_term (ASSUME ``A /\ B``) [1]; (* [A /\ B] |- A *)
prove_conj_entails_term (ASSUME ``A /\ B``) [2]; (* [A /\ B] |- B *)
prove_conj_entails_term (ASSUME ``(A /\ B) /\ C``) [1,1]; (* [(A /\ B) /\ C] |- A *)
prove_conj_entails_term (ASSUME ``(A /\ B) /\ C``) [1,2]; (* [(A /\ B) /\ C] |- B *)
prove_conj_entails_term (ASSUME ``(A /\ B) /\ C``) [2]; (* [(A /\ B) /\ C] |- C *)
prove_conj_entails_term (ASSUME ``A /\ (B /\ C)``) [1]; (* [(A /\ (B /\ C)] |- A *)
prove_conj_entails_term (ASSUME ``A /\ (B /\ C)``) [2,1]; (* [A /\ (B /\ C)] |- B *)
prove_conj_entails_term (ASSUME ``A /\ (B /\ C)``) [2,2]; (* [A /\ (B /\ C)] |- C *)
*)

fun show_conj_imp_single tm1 tm2 =
  if (tm2 = T) then DISCH tm1 TRUTH else
  let
    val path = (path_to_prove_conj_entails_term tm1 tm2);
    val thm = DISCH tm1 (prove_conj_entails_term (ASSUME tm1) path);
    val is_F = (concl(UNDISCH thm) = F);
  in
    if not(is_F) then thm else
    IMP_TRANS thm (SPEC tm2 FALSITY)
  end

(*
Tests:
show_conj_imp_single ``A: bool`` ``A: bool``;
show_conj_imp_single ``A /\ B`` ``A: bool``;
show_conj_imp_single ``A /\ B`` ``B: bool``;
show_conj_imp_single ``(A /\ B) /\ C`` ``A: bool``;
show_conj_imp_single ``(A /\ B) /\ C`` ``B: bool``;
show_conj_imp_single ``(A /\ B) /\ C`` ``C: bool``;
show_conj_imp_single ``A /\ (B /\ C)`` ``A: bool``;
show_conj_imp_single ``A /\ (B /\ C)`` ``B: bool``;
show_conj_imp_single ``A /\ (B /\ C)`` ``C: bool``;
show_conj_imp_single ``A /\ (B /\ C)`` ``Z: bool``; (* Fails *)
show_conj_imp_single ``F`` ``A: bool``;
show_conj_imp_single ``F /\ (B /\ C)`` ``Z: bool``;
show_conj_imp_single ``A /\ (F /\ C)`` ``Z: bool``;
show_conj_imp_single ``A /\ (B /\ F)`` ``Z: bool``;
show_conj_imp_single ``A: bool`` ``T``;
*)

fun show_big_conj_imp tm1 tm2 =
  if not(is_conj(tm2)) then (show_conj_imp_single tm1 tm2) else
  let
    val (lhs, rhs) = dest_conj tm2;
    val lthm = UNDISCH (show_big_conj_imp tm1 lhs);
    val rthm = UNDISCH (show_big_conj_imp tm1 rhs);
  in
    DISCH tm1 (CONJ lthm rthm)
  end

(*
Tests:
show_big_conj_imp ``A: bool`` ``A: bool``;
show_big_conj_imp ``(A /\ B) /\ C`` ``A: bool``;
show_big_conj_imp ``(A /\ B) /\ C`` ``A /\ B``;
show_big_conj_imp ``(A /\ B) /\ C`` ``A /\ C``;
show_big_conj_imp ``(A /\ B) /\ C`` ``B /\ C``;
show_big_conj_imp ``(A /\ B) /\ C`` ``A /\ B /\ C``;
show_big_conj_imp ``(A /\ B) /\ C`` ``B /\ C /\ A``;
show_big_conj_imp ``(A /\ B) /\ C`` ``B /\ C /\ T``;
show_big_conj_imp ``(A /\ B) /\ C`` ``Z /\ T``; (* Fails *)

Examples in exercise:
show_big_conj_imp ``a /\ (b /\ a) /\ c`` ``c /\ T /\ a``;
show_big_conj_imp ``(a /\ F) /\ c`` ``d: bool``;

4.2 Equivalences between Conjunctions

*)

fun show_big_conj_eq tm1 tm2 =
  if (aconv tm1 tm2) then (raise UNCHANGED) else
  let
    val thm1 = show_big_conj_imp tm1 tm2;
    val thm2 = show_big_conj_imp tm2 tm1;
  in
    IMP_ANTISYM_RULE thm1 thm2
  end

(*
Tests:
show_big_conj_eq ``A: bool`` ``A: bool``;
show_big_conj_eq ``(T /\ B) /\ A`` ``(A /\ T) /\ B``;

4.3 Duplicates in Conjunctions

*)

fun remove_dups_in_conj_CONV tm = let
  fun inner tm set =
    if not(is_conj tm) then
      if Redblackset.member(set, tm) then (set, T)
      else (Redblackset.add(set, tm), tm)
    else let (* is_conj *)
      val (lhs, rhs) = dest_conj tm;
      val (set, lhs) = inner lhs set;
      val (set, rhs) = inner rhs set;
    in (set, mk_conj (lhs, rhs)) end
    val (_, deduped) = (inner tm (Redblackset.empty Term.compare));
in
  show_big_conj_eq tm deduped
end

(*
Tests:
remove_dups_in_conj_CONV ``a /\ b /\ c``; (* Fails with UNCHANGED *)
remove_dups_in_conj_CONV ``a /\ (b /\ a) /\ c /\ b /\ a``;

4.4 Contradictions in Conjunctions

*)

fun keep_only_term_in_conj conj_thm term =
  if (concl(conj_thm) = term) then conj_thm else
  if not(is_conj (concl conj_thm)) then
    raise mk_HOL_ERR "Exercise2" "keep_only_term_in_conj" "not a conj"
  else keep_only_term_in_conj (CONJUNCT1 conj_thm) term
    handle HOL_ERR _ => keep_only_term_in_conj (CONJUNCT2 conj_thm) term

(*
Tests:
keep_only_term_in_conj (ASSUME ``A /\ B``) ``A: bool``; (* A *)
keep_only_term_in_conj (ASSUME ``A /\ B``) ``B: bool``; (* B *)
keep_only_term_in_conj (ASSUME ``A /\ (B /\ C)``) ``A: bool``; (* A *)
keep_only_term_in_conj (ASSUME ``A /\ (B /\ C)``) ``B: bool``; (* B *)
keep_only_term_in_conj (ASSUME ``A /\ (B /\ C)``) ``C: bool``; (* C *)
keep_only_term_in_conj (ASSUME ``(A /\ B) /\ C``) ``A: bool``; (* A *)
keep_only_term_in_conj (ASSUME ``(A /\ B) /\ C``) ``B: bool``; (* B *)
keep_only_term_in_conj (ASSUME ``(A /\ B) /\ C``) ``C: bool``; (* C *)
*)

fun find_contr_in_conj_CONV conj_tm = let
  val term_set = Redblackset.fromList Term.compare (strip_conj conj_tm);
  val has_neg = valOf(Redblackset.find
        (fn tm => Redblackset.member(term_set, mk_neg tm)) term_set)
    handle Option => raise UNCHANGED

  val conj_thm = ASSUME conj_tm;
  val thm1 = keep_only_term_in_conj conj_thm has_neg;
  val thm2 = keep_only_term_in_conj conj_thm (mk_neg has_neg);
  val conj_imp_neg_thm = DISCH conj_tm (CONJ thm1 thm2);

  val neg_imp_F_thm = SPEC has_neg (GEN_ALL (NOT_ELIM NOT_AND));
in
  IMP_TRANS conj_imp_neg_thm neg_imp_F_thm
end

(*
Tests:
find_contr_in_conj_CONV ``a /\ (b /\ ~a) /\ c``;
find_contr_in_conj_CONV ``a /\ (b /\ a) /\ c``; (* Fails *)
*)

