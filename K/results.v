(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset modular_hilbert base sltype.
Require Import K_def demo hilbert_ref gentzen universal_model.

(** * Main Results *)

Theorem soundness s : prv s -> forall (M:cmodel) (w:M), eval s w.
Proof. exact: soundness. Qed.

Theorem informative_completeness s : 
    prv (fImp s fF)  
  + (exists2 M:fmodel, #|M| <= 2^(f_size s) & exists w:M, eval s w).
Proof. exact: informative_completeness. Qed.

Corollary prv_dec s : decidable (prv s).
Proof. exact: prv_dec. Qed.

Corollary sat_dec s : decidable (exists (M:cmodel) (w:M), eval s w).
Proof. exact: sat_dec. Qed.

Corollary valid_dec s : decidable (forall (M:cmodel) (w:M), eval s w).
Proof. exact: valid_dec. Qed.

Corollary small_models s:
  (exists (M:cmodel) (w:M), eval s w) ->
  (exists2 M:fmodel, #|M| <= 2^(f_size s) & exists w:M, eval s w).
Proof. exact: small_models. Qed.

(** Canonicity of the pruning demo *)

Fact DD_canonical F (sfc_F : sf_closed F) (C : clause) : 
  reflect (C \in S0 F  /\ exists M : cmodel, sat M C) (C \in DD F).
Proof. exact: DD_canonical. Qed.

Proposition support_sat C :
  (exists M, sat M C) <->
  (exists D, [/\ D \in S0 (sfc C), (exists M, sat M D) & suppC D C]).
Proof. exact: support_sat. Qed.


(** Gentzen System *)
    
Theorem gen_completeness C : gen C + (exists M : fmodel, sat M C).
Proof. exact: gen_completeness. Qed.

Corollary gen_correctness C : gen C <-> ~ (exists M : cmodel, sat M C).
Proof. exact: gen_correctness. Qed.

Corollary gen_dec C : decidable (gen C).
Proof. exact: gen_dec. Qed.

(** Universal Model *)

Theorem UM_universal s :
  (exists (M:cmodel) (w:M), eval s w) -> (exists (w:UM), eval s w).
Proof. exact: UM_universal. Qed.


(** Soundness for all Kripke Models equivalent to XM *)

Theorem xm_soundness (xm : XM) s : prv s -> forall (M : ts) (w : M), eval s w.
Proof. exact: xm_soundness. Qed.

Lemma XM_required : (forall s, prv s -> forall (M : ts) (w : M), eval s w) -> XM.
Proof. exact: XM_required. Qed.
