(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.

Require Import Kstar_def demo hilbert_ref gen_def gen_ref. 

(** * Main Results *)

(** Soundness and Completeness of the Hilbert System *)

Lemma soundness s : prv s -> forall (M:cmodel) (w:M), eval s w.
Proof. exact: Kstar_def.soundness. Qed.

Theorem informative_completeness s : 
    prv (fImp s fF)
  + (exists2 M:fmodel, #|M| <= 2^(2 * f_size s) & exists w:M, eval s w).
Proof. exact: informative_completeness s. Qed.

Corollary prv_dec s : decidable (prv s).
Proof. exact: prv_dec. Qed.

Corollary sat_dec s : decidable (exists (M:cmodel) (w:M), eval s w).
Proof. exact: sat_dec. Qed.

Corollary valid_dec s : decidable (forall (M:cmodel) (w:M), eval s w).
Proof. exact: valid_dec. Qed.

Corollary small_models s:
  (exists (M:cmodel) (w:M), eval s w) ->
  (exists2 M:fmodel, #|M| <= 2^(2 * f_size s) & exists w:M, eval s w).
Proof. exact: small_models. Qed.


(** Correctness of the Gentzen System *)

Lemma gen_completeness C : gen (C,aVoid) + (exists M : fmodel, sat M C).
Proof. exact: gen_completeness. Qed.

Theorem gen_correctness C : gen (C,aVoid) <-> ~ (exists M : cmodel, sat M C).
Proof. exact: gen_correctness. Qed.

(** Equivalence to Segerberg Style Hilbert System *)

Theorem prv_Sprv s : prv s <-> S.prv s.
Proof. exact: prv_Sprv. Qed.
