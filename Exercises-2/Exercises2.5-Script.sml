(*

5.2 Proof

Prove: Sp platon

set_trace "assumptions" 1;

*)

open philTheory;

(*
Using the lemma MONO_NOT and the inference rules MATCH_MP, SPEC and IMP_TRANS
show the lemma |- ~(W p) ==> Sp p.
*)

val not_wise_imp_not_at = MATCH_MP MONO_NOT (SPEC_ALL PHIL_KNOWLEDGE_b);
val not_wise_imp_sp = IMP_TRANS not_wise_imp_not_at (SPEC_ALL PHIL_KNOWLEDGE_d2);

(*
Similarly show |- ~(B p) ==> At p.
*)

val not_brave_imp_not_sp = MATCH_MP MONO_NOT (SPEC_ALL PHIL_KNOWLEDGE_a);
val not_brave_imp_at = IMP_TRANS not_brave_imp_not_sp (SPEC_ALL PHIL_KNOWLEDGE_d1);

(*
Assume At platon and using this show the lemma [At platon] |- F with MP and
MATCH_MP. You will need many steps and many different lemmata.

⊢ At platon ⇒ ¬W euklid ==> Sp euklid
⊢ Sp euklid ⇒ ¬B diogenes ==> At diogenes
⊢ At diogenes ⇒ ¬B euklid ==> At euklid
⊢ At euklid ==> ¬Sp euklid (* CONTRADICTION *)
*)

val atp = ASSUME ``At platon``;

val atp_then_not_wise_euklid = MATCH_MP PHIL_KNOWLEDGE_h atp;
val atp_then_spe = MATCH_MP not_wise_imp_sp atp_then_not_wise_euklid;

val atp_then_not_brave_diogenes = MATCH_MP PHIL_KNOWLEDGE_f atp_then_spe;
val atp_then_atd = MATCH_MP not_brave_imp_at atp_then_not_brave_diogenes;

val atp_then_not_brave_euklid = MATCH_MP PHIL_KNOWLEDGE_g atp_then_atd;
val atp_then_ate = MATCH_MP not_brave_imp_at atp_then_not_brave_euklid;
val atp_then_not_spe = MATCH_MP (SPEC_ALL PHIL_KNOWLEDGE_c2) atp_then_ate;

val atp_then_contr = CONJ atp_then_spe atp_then_not_spe;
val atp_then_F = MATCH_MP (NOT_ELIM NOT_AND) atp_then_contr;

(*
Using DISCH, NOT_INTRO and MATCH_MP show: Sp platon.
*)

val not_atp = NOT_INTRO (DISCH_ALL atp_then_F);
val sp_platon = MATCH_MP PHIL_KNOWLEDGE_d2 not_atp;

