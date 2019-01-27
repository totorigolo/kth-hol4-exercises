(* vim: ts=2:sw=2:textwidth=100
 * 
 * Exercise 5.2
 *
 *)

open boolLib listTheory rich_listTheory numTheory;

val IGNORE_ME = "vim's syntax highlighter is buggy";

(* Define some test tools *)

fun test_eq (lhs, rhs, description) = let
  val _ = assert_exn (fn (lhs, rhs) => lhs = rhs) (lhs, rhs)
          (Fail ("test failed: " ^ description));
in ("test passed: " ^ description) end;

fun test_rhs_is (thm, r, description) = let
  val _ = assert_exn (fn th => (rhs (concl th)) = r) thm
          (Fail ("test failed: " ^ description));
in ("test passed: " ^ description) end;

(* 2. Deep and Shallow Embeddings *)

(* Shallow embedding *)
val sh_true_def    = Define `sh_true = T`;
val sh_var_def     = Define `sh_var (v: bool) = v`;
val sh_not_def     = Define `sh_not b = ~b`;
val sh_and_def     = Define `sh_and b1 b2 = (b1 /\ b2)`;
val sh_or_def      = Define `sh_or b1 b2 = (b1 ∨ b2)`;
val sh_implies_def = Define `sh_implies b1 b2 = (b1 ==> b2)`;

(** 2.1. Syntax for propositional formulas **)
fun list_to_pair (x::y::[]) = (x, y)
  | list_to_pair _ = raise Fail "not a list with 2 elements";

fun pair_to_list (x, y) = x::y::[];

(* sh_true *)
fun mk_sh_true () = list_mk_comb (``sh_true``, []);
fun dest_sh_true tm = (); (* TODO: Is that ok? *)
fun is_sh_true tm = ((fst (strip_comb tm)) = ``sh_true``);
local
  val sh_true = mk_sh_true ()
in
  val _ = test_eq (sh_true, ``sh_true``, "mk_sh_true")
  val _ = test_eq (dest_sh_true sh_true, (), "dest_sh_true")
  val _ = test_eq (is_sh_true sh_true, true, "is_sh_true T")
  val _ = test_eq (is_sh_true ``sh_not T``, false, "is_sh_true F")
end;

(* sh_var *)
fun mk_sh_var tm = list_mk_comb (``sh_var``, [tm]);
fun dest_sh_var tm = hd (snd (strip_comb tm));
fun is_sh_var tm = ((fst (strip_comb tm)) = ``sh_var``);
local
  val sh_var = mk_sh_var ``a: bool``
in
  val _ = test_eq (sh_var, ``sh_var a``, "mk_sh_var")
  val _ = test_eq (dest_sh_var sh_var, (“a: bool”), "dest_sh_var")
  val _ = test_eq (is_sh_var sh_var, true, "is_sh_var T")
  val _ = test_eq (is_sh_var ``sh_not T``, false, "is_sh_var F")
end;

(* sh_not *)
fun mk_sh_not tm = list_mk_comb (``sh_not``, [tm]);
fun dest_sh_not tm = hd (snd (strip_comb tm));
fun is_sh_not tm = ((fst (strip_comb tm)) = ``sh_not``);
local
  val sh_not = mk_sh_not ``a: bool``
in
  val _ = test_eq (sh_not, ``sh_not a``, "mk_sh_not")
  val _ = test_eq (dest_sh_not sh_not, (“a: bool”), "dest_sh_not")
  val _ = test_eq (is_sh_not sh_not, true, "is_sh_not T")
  val _ = test_eq (is_sh_not ``sh_or T T``, false, "is_sh_not F")
end;

(* sh_and *)
fun mk_sh_and tm1 tm2 = list_mk_comb (``sh_and``, [tm1, tm2]);
fun dest_sh_and tm = list_to_pair (snd (strip_comb tm));
fun is_sh_and tm = ((fst (strip_comb tm)) = ``sh_and``);
local
  val sh_and = mk_sh_and ``a: bool`` ``b: bool``
in
  val _ = test_eq (sh_and, ``sh_and a b``, "mk_sh_and")
  val _ = test_eq (dest_sh_and sh_and, (“a: bool”, “b: bool”), "dest_sh_and")
  val _ = test_eq (is_sh_and sh_and, true, "is_sh_and T")
  val _ = test_eq (is_sh_and ``sh_not T``, false, "is_sh_and F")
end;

(* sh_or *)
fun mk_sh_or tm1 tm2 = list_mk_comb (``sh_or``, [tm1, tm2]);
fun dest_sh_or tm = list_to_pair (snd (strip_comb tm));
fun is_sh_or tm = ((fst (strip_comb tm)) = ``sh_or``);
local
  val sh_or = mk_sh_or ``a: bool`` ``b: bool``
in
  val _ = test_eq (sh_or, ``sh_or a b``, "mk_sh_or")
  val _ = test_eq (dest_sh_or sh_or, (“a: bool”, “b: bool”), "dest_sh_or")
  val _ = test_eq (is_sh_or sh_or, true, "is_sh_or T")
  val _ = test_eq (is_sh_or ``sh_not T``, false, "is_sh_or F")
end;

(* sh_implies *)
fun mk_sh_implies tm1 tm2 = list_mk_comb (``sh_implies``, [tm1, tm2]);
fun dest_sh_implies tm = list_to_pair (snd (strip_comb tm));
fun is_sh_implies tm = ((fst (strip_comb tm)) = ``sh_implies``);
local
  val sh_implies = mk_sh_implies ``a: bool`` ``b: bool``
in
  val _ = test_eq (sh_implies, ``sh_implies a b``, "mk_sh_implies")
  val _ = test_eq (dest_sh_implies sh_implies, (“a: bool”, “b: bool”), "dest_sh_implies")
  val _ = test_eq (is_sh_implies sh_implies, true, "is_sh_implies T")
  val _ = test_eq (is_sh_implies ``sh_not T``, false, "is_sh_implies F")
end;

(* is_sh_prop *)
fun is_sh_prop tm =
         is_sh_true    tm
  orelse is_sh_var     tm
  orelse is_sh_not     tm
  orelse is_sh_and     tm
  orelse is_sh_or      tm
  orelse is_sh_implies tm
local in
  val _ = test_eq (is_sh_prop (mk_sh_true ()), true, "sh_true")
  val _ = test_eq (is_sh_prop (mk_sh_var ``a: bool``), true, "sh_var")
  val _ = test_eq (is_sh_prop (mk_sh_not ``a: bool``), true, "sh_not")
  val _ = test_eq (is_sh_prop (mk_sh_and ``a: bool`` ``b: bool``), true, "sh_and")
  val _ = test_eq (is_sh_prop (mk_sh_or ``a: bool`` ``b: bool``), true, "sh_or")
  val _ = test_eq (is_sh_prop (mk_sh_implies ``a: bool`` ``b: bool``), true, "sh_implies")
  val _ = test_eq (is_sh_prop ``T ∧ F``, false, "not a prop")
end;

(* Deep embedding *)
val _ = Datatype `bvar = BVar num`
val _ = Datatype `prop = d_true
                       | d_var bvar
                       | d_not prop
                       | d_and prop prop
                       | d_or prop prop
                       | d_implies prop prop`;

val _ = Datatype `var_assignment = BAssign (bvar -> bool)`
val VAR_VALUE_def = Define `VAR_VALUE (BAssign a) v = (a v)`;

val PROP_SEM_def = Define `
    (PROP_SEM a d_true = T)
  ∧ (PROP_SEM a (d_var v) = VAR_VALUE a v)
  ∧ (PROP_SEM a (d_not p) = ¬(PROP_SEM a p))
  ∧ (PROP_SEM a (d_and p1 p2) = (PROP_SEM a p1 ∧ PROP_SEM a p2))
  ∧ (PROP_SEM a (d_or p1 p2) = (PROP_SEM a p1 ∨ PROP_SEM a p2))
  ∧ (PROP_SEM a (d_implies p1 p2) = (PROP_SEM a p1 ==> PROP_SEM a p2))
`;

val IS_NNF_def = Define `
    (IS_NNF (d_not d_true) = T)
  ∧ (IS_NNF (d_not (d_var _)) = T)
  ∧ (IS_NNF (d_not _) = F)
  ∧ (IS_NNF d_true = T)
  ∧ (IS_NNF (d_var _) = T)
  ∧ (IS_NNF (d_and p1 p2) = (IS_NNF p1 ∧ IS_NNF p2))
  ∧ (IS_NNF (d_or p1 p2) = (IS_NNF p1 ∧ IS_NNF p2))
  ∧ (IS_NNF (d_implies p1 p2) = (IS_NNF p1 ∧ IS_NNF p2))
`;

val PROP_IS_EQUIV_def = Define `PROP_IS_EQUIV p1 p2 <=> (!a. PROP_SEM a p1 = PROP_SEM a p2)`;

(* 2.2. Getting Rid of Conjunction and Implication *)

val PROP_CONTAINS_NO_AND_IMPL_def = Define `
    (PROP_CONTAINS_NO_AND_IMPL (d_and _ _) = F)
  ∧ (PROP_CONTAINS_NO_AND_IMPL (d_implies _ _) = F)
  ∧ (PROP_CONTAINS_NO_AND_IMPL d_true = T)
  ∧ (PROP_CONTAINS_NO_AND_IMPL (d_var _) = T)
  ∧ (PROP_CONTAINS_NO_AND_IMPL (d_not p) = PROP_CONTAINS_NO_AND_IMPL p)
  ∧ (PROP_CONTAINS_NO_AND_IMPL (d_or p1 p2)
      = PROP_CONTAINS_NO_AND_IMPL p1 ∧ PROP_CONTAINS_NO_AND_IMPL p2)
`;

test_rhs_is (EVAL ``PROP_CONTAINS_NO_AND_IMPL (d_true)``, T, "d_true");
test_rhs_is (EVAL ``PROP_CONTAINS_NO_AND_IMPL (d_var a)``, T, "d_var");
test_rhs_is (EVAL ``PROP_CONTAINS_NO_AND_IMPL (d_and a b)``, F, "d_and");
test_rhs_is (EVAL ``PROP_CONTAINS_NO_AND_IMPL (d_implies a b)``, F, "d_implies");
test_rhs_is (EVAL ``PROP_CONTAINS_NO_AND_IMPL (d_and (d_or a b) d_true)``, F, "F nested 1");
test_rhs_is (EVAL ``PROP_CONTAINS_NO_AND_IMPL (d_or (d_and a b) (d_or a c))``, F, "F nested 2");
test_rhs_is (EVAL ``PROP_CONTAINS_NO_AND_IMPL (d_or (d_var v) (d_or d_true d_true))``, T, "T nested 2");

fun sh_prop_contains_no_and_impl prop =
  if ((is_sh_and prop) orelse (is_sh_implies prop)) then false else
  if (is_sh_true prop) then true else
  if (is_sh_var prop) then true else 
  if (is_sh_not prop) then sh_prop_contains_no_and_impl (dest_sh_not prop) else
  if (is_sh_or prop) then all sh_prop_contains_no_and_impl (pair_to_list (dest_sh_or prop)) else
  raise Fail "not a prop";

test_eq (sh_prop_contains_no_and_impl ``sh_true``, true, "sh_true");
test_eq (sh_prop_contains_no_and_impl ``sh_and sh_true sh_true``, false, "sh_false");
test_eq (sh_prop_contains_no_and_impl ``sh_or (sh_var v) sh_true``, true, "sh_or simple");
test_eq (sh_prop_contains_no_and_impl ``sh_or sh_true (sh_and sh_true sh_true)``, false, "sh_or simple");

val PROP_REMOVE_AND_IMPL_def = Define `
    (PROP_REMOVE_AND_IMPL (d_and l r) = d_not (d_or (d_not (PROP_REMOVE_AND_IMPL l))
                                                    (d_not (PROP_REMOVE_AND_IMPL r))))
  ∧ (PROP_REMOVE_AND_IMPL (d_implies l r) = d_or (d_not (PROP_REMOVE_AND_IMPL l))
                                                        (PROP_REMOVE_AND_IMPL r))
  ∧ (PROP_REMOVE_AND_IMPL d_true = d_true)
  ∧ (PROP_REMOVE_AND_IMPL (d_var v) = d_var v)
  ∧ (PROP_REMOVE_AND_IMPL (d_not p) = d_not (PROP_REMOVE_AND_IMPL p))
  ∧ (PROP_REMOVE_AND_IMPL (d_or p1 p2)
      = d_or (PROP_REMOVE_AND_IMPL p1) (PROP_REMOVE_AND_IMPL p2))
`;

val PROP_REMOVE_AND_IMPL_EQUIV = prove (
  ``!p. PROP_IS_EQUIV (PROP_REMOVE_AND_IMPL p) p``,
  REWRITE_TAC[PROP_IS_EQUIV_def] >>
  Induct_on `p` >>
  FULL_SIMP_TAC bool_ss [PROP_REMOVE_AND_IMPL_def, PROP_SEM_def] >>
  DECIDE_TAC
);

val PROP_REMOVE_AND_IMPL_NONE_LEFT = prove (
  ``!p. PROP_CONTAINS_NO_AND_IMPL (PROP_REMOVE_AND_IMPL p)``,
  Induct >>
  FULL_SIMP_TAC bool_ss [PROP_REMOVE_AND_IMPL_def, PROP_CONTAINS_NO_AND_IMPL_def] >>
  DECIDE_TAC
);

fun sh_prop_remove_and_impl tm =
let
  fun assert_prop tm = assert_exn is_sh_prop tm (Fail "not a prop");
  fun remove_and_impl tm =
    if (is_sh_and tm) then
      (let val (lhs, rhs) = (dest_sh_and tm);
      in (mk_sh_not (mk_sh_or (mk_sh_not lhs) (mk_sh_not rhs))) end)
    else if (is_sh_implies tm) then
      (let val (lhs, rhs) = (dest_sh_implies tm);
      in (mk_sh_or (mk_sh_not lhs) rhs) end)
    else tm;
  fun prove_eqiv (tm1, tm2) = prove (
    mk_eq (tm1, tm2),
    REWRITE_TAC[sh_true_def, sh_var_def, sh_not_def, sh_and_def, sh_or_def, sh_implies_def]);
  val prop_tm = assert_prop tm;
in prove_eqiv (prop_tm, remove_and_impl prop_tm) end;

(*
sh_prop_remove_and_impl ``sh_and sh_true (sh_or sh_true (sh_var b))``;
sh_prop_remove_and_impl ``5``;
*)

(* 3. Fancy Function Definitions *)

val expunge_def = Define `
    (expunge x []     = [])
  ∧ (expunge x (h::t) = if x = h then expunge x t else h::expunge x t)
`;

val min_def = Define `
    (min [] m = m)
  ∧ (min (h::t) m = if m ≤ h then min t m else min t h)
`;

val minsort_defn = Hol_defn "minsort" `
    (minsort [] = [])
  ∧ (minsort (h::t) = let m = min t h
                      in m::minsort (expunge m (h::t)))
`;

val LENGTH_expunge = prove (
  ``!x xs. LENGTH (expunge x xs) ≤ LENGTH xs``,
  Induct_on `xs` >>
  SIMP_TAC list_ss [expunge_def] >>
  Cases_on `x = h` >>
  REWRITE_TAC[] >>
  `LENGTH (expunge h xs) ≤ LENGTH xs` by ASM_REWRITE_TAC[] >| [
    DECIDE_TAC,
    ASM_SIMP_TAC arith_ss [LENGTH]
  ]
);

val SHORTER_LENGTH_WHEN_expunge_MEM = prove (
  ``!x xs. MEM x xs ==> LENGTH (expunge x xs) < LENGTH xs``,
  Induct_on `xs` >>
  REWRITE_TAC[MEM, LENGTH, expunge_def] >>
  Cases_on `x = h` >>
  SIMP_TAC list_ss [] >| [
    `LENGTH xs < SUC (LENGTH xs)` by SIMP_TAC list_ss [] >>
    `LENGTH (expunge x xs) ≤ LENGTH xs` suffices_by ASM_SIMP_TAC list_ss [] >>
    REWRITE_TAC[LENGTH_expunge],
    PROVE_TAC[]
  ]
);

val min_MEM_of_list = prove (
  ``!x xs. MEM (min xs x) (x::xs)``,
  Induct_on `xs` >>
  REWRITE_TAC[MEM, min_def] >>
  Cases_on `x ≤ h` >>
  SIMP_TAC list_ss [] >>
  `MEM (min xs x) (x::xs)` by ASM_REWRITE_TAC[] >>
  FULL_SIMP_TAC list_ss []
);

Defn.tprove (minsort_defn,
  WF_REL_TAC `measure LENGTH` >>
  PROVE_TAC[LENGTH_expunge, SHORTER_LENGTH_WHEN_expunge_MEM, min_MEM_of_list]
);















