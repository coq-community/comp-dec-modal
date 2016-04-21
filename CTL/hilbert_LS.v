(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert.
Require Import CTL_def hilbert hilbert_hist.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Axiomatization of Lange and Stirling 

Lange and Stirling give an axiomatization of CTL based on a game semantics. We
show that this axiomatization is equivalent to the Hilbert system employed in
our completeness proof. 

Note: The Infrastructure for Hilbert proofs only works for the "Canonical"
Hilbert system for a given type of formulas. We use modules to ensure that the
right system is considered canonical at the right time. *)

Module LS.
Section Hilbert.

(** The defined logical operations are only available once the respective
records ([pSystem] etc.) have been declared. Hence we introduce local notations
and later restate some of the axioms and rules using the defined notations from
[modular_hilbert.v] *)
  
  Local Notation "s ---> t" := (fImp s t).
  Local Notation "~~: s" := (s ---> fF).
  Local Notation "s :\/: t" := (~~: s ---> t).
  Local Notation "s :/\: t" := (~~: (s ---> ~~: t)).
  Local Notation "s <--> t" := ((s ---> t) :/\: (t ---> s)).
  Definition fEX s := (~~: fAX (~~: s)).
  Definition fER s t := (~~: fAU (~~: s) (~~: t)).

  Inductive prv : form -> Prop :=
  | rMP s t : prv (s ---> t) -> prv s -> prv t
  | axK s t : prv (s ---> t ---> s)
  | axS s t u : prv ((u ---> s ---> t) ---> (u ---> s) ---> u ---> t)
  | axDN s : prv (((s ---> fF) ---> fF)  ---> s)
  | rNec s : prv s -> prv (fAX s)
  | axN s t : prv (fAX (s ---> t) ---> fAX s ---> fAX t)

  | axSer s : prv (fAX (~~: s) ---> ~~: fAX s)

  | axARf' s t : prv (fAR s t ---> t :/\: (s :\/: fAX (fAR s t)))
  | ARel' s t u :
      prv (u ---> t :/\: (s :\/: fAX (fAR (s :\/: u) (t :\/: u)))) ->
      prv (u ---> fAR s t)

  | axERf' s t : prv (fER s t ---> t :/\: (s :\/: fEX (fER s t)))
  | ERel' s t u :
      prv (u ---> t :/\: (s :\/: fEX (fER (s :\/: u) (t :\/: u)))) ->
      prv (u ---> fER s t)

  | axAUcmp' s t : prv (fAU s t <--> ~~: fER (~~: s) (~~: t)). 
End Hilbert.

Canonical Structure prv_mSystem := MSystem rMP axK axS.
Canonical Structure prv_pSystem := PSystem axDN.
Canonical Structure prv_kSystem := KSystem rNec axN.

(** restate axioms/rule using notations from modular_hilbert.v *)

Lemma ARel s t u :
  prv (u ---> t :/\: (s :\/: fAX (fAR (s :\/: u) (t :\/: u)))) ->
  prv (u ---> fAR s t).
Proof. exact: ARel'. Qed.

Lemma axARf s t : prv (fAR s t ---> t :/\: (s :\/: fAX (fAR s t))).
Proof. exact: axARf'. Qed.

Lemma ERel s t u :
      prv (u ---> t :/\: (s :\/: fEX (fER (s :\/: u) (t :\/: u)))) ->
      prv (u ---> fER s t).
Proof. exact: ERel'. Qed.

Lemma axERf s t : prv (fER s t ---> t :/\: (s :\/: fEX (fER s t))).
Proof. exact: axERf'. Qed.

Lemma axAUcmp s t : prv (fAU s t <--> ~~: fER (~~: s) (~~: t)). 
Proof. exact: axAUcmp'. Qed.


(** ** Completeness 

We show completenes of the Hilbert system LS by showing admissibility of the
rules and axoms of the Hilbert system IC. *)

(** Helper Lemmas *)

Lemma ARI s t : prv (s ---> t ---> fAR s t).
Proof. apply: rAIL. apply ARel. rule axAcase; do 2 Intro. ApplyH axAI. ApplyH axOIl. Qed.

Lemma ERI s t : prv (s ---> t ---> fER s t).
Proof. apply: rAIL. apply ERel. rule axAcase; do 2 Intro. ApplyH axAI. ApplyH axOIl. Qed.

(** Rules/Axioms of inductive Hilbert system *)

Lemma AR_ind s t u : prv (u ---> t) -> prv (u ---> (s ---> fF) ---> fAX u) -> prv (u ---> fAR s t).
Proof.
  move => H1 H2. apply: ARel.
  Intro. ApplyH axAI; [ApplyH H1|]. Intro.
  Have (fAX u); [by ApplyH H2|drop]. apply: rNorm.
  Intro. ApplyH ARI. ApplyH axOIr. ApplyH axOIl. ApplyH H1.
Qed.

Lemma axARE s t  : prv (fAR s t ---> t).
Proof. rewrite -> axARf. exact: axAEl. Qed.

Lemma axARu s t  : prv (fAR s t ---> ~~: s ---> fAX (fAR s t)).
Proof. rewrite -> axARf at 1. rule axAcase. by drop. Qed.

Lemma AU_ind s t u : prv (t ---> u) -> prv (s ---> fAX u ---> u) -> prv ((fAU s t) ---> u).
Proof.
  move => H1 H2. rewrite -> axAUcmp, <- (axDN u). rule ax_contraNN. apply: ERel.
  Intro; ApplyH axAI; first by Rev; rule ax_contraNN.
  rewrite {1}/Or. rewrite -> modular_hilbert.axDN. Intro.
  Have (fEX (~~: u)). Intro. Apply* 2. ApplyH H2. Rev. drop. apply: rNorm. exact: axDN.
  drop. apply: rEXn. 
  Intro. ApplyH ERI. ApplyH axOIr. ApplyH axOIl. rewrite -> H1. Rev. exact: axI.
Qed.

Lemma axAUI s t : prv (t ---> fAU s t).
Proof. 
  rewrite -> axAUcmp. rewrite -> (axDNI t) at 1. rule ax_contraNN.
  rewrite -> axERf. exact: axAEl.
Qed.

Lemma axAUf s t : prv (s ---> fAX (fAU s t) ---> fAU s t).
Proof.
  apply: rAIL. rule ax_contra. rewrite -> axAUcmp, modular_hilbert.axDN.
  rewrite -> axERf at 1. rule axAcase. Intro. 
  (* need to help unification*)
  set u := ~~: (s :/\: _). ApplyH (axOE (~~: s) (fEX (fER (~~: s) (~~: t))) u); rewrite /u.
  - Intro. ApplyH axAcase. do 2 Intro. Apply* 2.
  - Intro. ApplyH axAcase. do 2 Intro. Apply* 2.
Qed.

Lemma ax_serial : prv (~~: (fAX fF)).
Proof. Intro. ApplyH (axSer fF). drop. apply: rNec. exact: axI. Qed.

End LS.


Theorem LS_translation s : IC.prv s -> LS.prv s.
Proof.
  elim => {s}; eauto using LS.prv,LS.axARE,LS.axARu,LS.AR_ind,LS.AU_ind,LS.axAUI, LS.axAUf.
Qed.

(** ** Soundness 

We show soundness by proving all rules admissible in IC *)

(** Set up the Infrastructure for Hilbert proofs for the system IC *)
Import IC.

(** The lemmas below correspond, up to propositional reasoning, to the hilbert
lemmas for the soundness proof of the Gentzen system (file hilbert_hist.v) *)

Lemma ERel (s t u : form) :
      prv (u ---> t :/\: (s :\/: EX (ER (s :\/: u) (t :\/: u)))) ->
      prv (u ---> ER s t).
Proof.
  move => H. 
  rewrite /ER. rewrite -> (axAsT (~~: s)), (axAsT (~~: t)). apply: AUH_hil.
  - rule axAcase. rewrite -[~~: t ---> _]/(~~: (~~: t)). rewrite -> axDNE.
    rule axB; last apply H. exact: axAEl.
  - rewrite /AU_. rewrite <- axAsT. do ! rewrite <- dmO. rewrite <- dmER.
    rewrite -> H at 1. exact: axAEr.
Qed.

Lemma ARel s t u :
  prv (u ---> t :/\: (s :\/: AX (AR (s :\/: u) (t :\/: u)))) ->
  prv (u ---> AR s t).
Proof.
  move => H. rewrite <- (axDNE (AR s t)), dmAR.
  rewrite -> (axAsT (~~: s)), (axAsT (~~: t)). apply: ARH_hil.
  - rule ax_contraNN. rule axB; last apply H. exact: axAEl.
  - rewrite /EU_. rewrite <- axAsT. do ! rewrite <- dmO. rewrite <- dmAR.
    rewrite /EX. rewrite -> axDNE.
    do 2 Intro. rewrite -> H at 3. ApplyH axAcase. Intro. by ApplyH axOE.
Qed.

Lemma axARf s t : prv (fAR s t ---> t :/\: (s :\/: fAX (fAR s t))).
Proof. rewrite -> axAReq at 1. exact: axI. Qed.

Lemma axERf s t : prv (ER s t ---> t :/\: (s :\/: EX (ER s t))).
Proof. exact: axERu. Qed.

Lemma axAUcmp s t : prv (fAU s t <--> ~~: ER (~~: s) (~~: t)). 
Proof. rule axAI; rewrite -> dmER, axDNE, axDNE; exact: axI. Qed.

Lemma axSer s : prv (fAX (~~: s) ---> ~~: fAX s).
Proof.
  rewrite {2}/Neg. rewrite <- ax_serial. apply rAIL. rewrite -> axABBA.
  apply: rNorm. rule axAcase. exact: axI.
Qed.       

Lemma LS_sound s : LS.prv s -> prv s.
Proof. elim => {s} *; eauto using prv,ERel,ARel,axARf,axERf,axAUcmp,axSer. Qed.