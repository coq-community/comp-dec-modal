(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs
 Require Import edone bcase fset base modular_hilbert sltype.

From CompDecModal.CTL
 Require Import CTL_def dags demo agreement hilbert hilbert_ref hilbert_LS hilbert_Eme90.
From CompDecModal.CTL
 Require Import gen_def gen_dec gen_hsound gen_ref.

(** * Main Results *)

(** Equivalence of Hilbert Systems *)

Theorem IC_soundness s : IC.prv s -> forall (M:cmodel) (w:M), eval s w.
Proof. exact: IC.soundness. Qed.

Theorem IC_LS_equivalence s : IC.prv s <-> LS.prv s.
Proof. split. exact: LS_translation. exact: LS_sound. Qed.

Theorem IC_Eme90_equivalence s : IC.prv s <-> Eme90.prv s.
Proof. split. exact: Eme90_translation. exact: Eme90_sound. Qed.

(** Soundness and Completeness for IC *)
Import IC.

Theorem soundness s : prv s -> forall (M:cmodel) (w:M), eval s w.
Proof. exact: soundness. Qed.

Theorem informative_completeness s :
     ( prv (~~: s) )
  +  (exists2 M : fmodel, #|M| <= f_size s * 2^(4 * f_size s + 2) & exists (w:M), eval s w).
Proof. exact: informative_completeness. Qed.

Corollary fin_completeness s : (forall (M:fmodel) (w:M), eval s w) -> prv s.
Proof. exact: fin_completeness. Qed.


(** Decidability and Small-Model-Property *)

Corollary prv_dec s : decidable (prv s).
Proof. exact: prv_dec. Qed.

Corollary sat_dec s : decidable (exists (M:cmodel) (w:M), eval s w).
Proof. exact: sat_dec. Qed.

Corollary valid_dec s : decidable (forall (M:cmodel) (w:M), eval s w).
Proof. exact: valid_dec. Qed.

Corollary small_models s :
  (exists (M:cmodel) (w:M), eval s w) -> 
  (exists2 M : fmodel, #|M| <= f_size s * 2^(4 * f_size s + 2) & exists (w:M), eval s w).
Proof. exact: small_models. Qed.


(** Gentzen System *)

Theorem plain_soundness C : gen (C,aVoid) -> prv (~~: [af C]).
Proof. exact: plain_soundness. Qed.

Theorem gen_complete C :
  gen (C,aVoid) + (exists (M:fmodel) (w:M), forall s, s \in C -> eval (interp s) w).
Proof. exact: gen_complete. Qed.

Theorem gen_dec (A : clause * annot) : decidable (gen A).
Proof. exact: gen_dec. Qed.


(** Agreement of Path semantics with Inductive Semantics *)

Lemma evalP2 (M:fmodel) s (w : M) : (@satisfies M s w) <-> (@eval M s w).
Proof. exact: evalP2. Qed.

Lemma fin_path_soundness s : prv s -> forall (M : fmodel) (w:M), @satisfies M s w.
Proof. move => H M w. apply/evalP2. exact: soundness M w. Qed.

Lemma sts_agreement : XM -> DC -> forall (M:sts) (w :M) s, eval s w <-> satisfies s w.
Proof. exact: sts_agreement. Qed.


(** Soundness wrt. to Path semantics implies XM and DX *)

Lemma XM_required : 
  (forall s, prv s -> forall (M : sts) (w : M), satisfies s w) -> XM.
Proof. exact: XM_required. Qed.

Lemma DC_required : 
  (forall s, prv s -> forall (M : sts) (w : M), satisfies s w) -> DC.
Proof. exact: DC_required. Qed.

(** Agreement of coinductive AR and disjunctive AR implies LPO *)

Section LPO.
  Hypothesis hyp_AR : forall (M : fmodel) (w : M) (s t : form), 
    cAR (@trans M) (eval s) (eval t) w -> pAR' (@trans M) (satisfies s) (satisfies t) w.

  Lemma LPO_of_disjunctive_AR (f : nat -> bool) :
    (forall n, f n = false) \/ exists n, f n = true.
  Proof. exact: LPO_of_disjunctive_AR. Qed.
End LPO.
