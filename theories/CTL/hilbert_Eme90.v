(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs
 Require Import edone bcase fset base induced_sym modular_hilbert.
From CompDecModal.CTL
 Require Import CTL_def hilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Emerson's Axiomatization

In the Handbook of Theoretical Computer Science Emerson gives an axiomatization
of CTL. We show that this axiomatization is equivalent to the Hilbert system
employed in our completeness proof.

Note: The Infrastructure for Hilbert proofs only works for the "Canonical"
Hilbert system for a given type of formulas. We use modules to ensure that the
right system is considered canonical at the right time. *)

Module Eme90.
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
  Definition fEU s t := (~~: fAR (~~: s) (~~: t)).
  Definition fAG s := fAR fF s.

  Inductive prv : form -> Prop :=
  | rMP s t : prv (s ---> t) -> prv s -> prv t
  | axK s t : prv (s ---> t ---> s)
  | axS s t u : prv ((u ---> s ---> t) ---> (u ---> s) ---> u ---> t)
  | axDN s : prv (((s ---> fF) ---> fF)  ---> s)

  | rGen s : prv s -> prv (fAG s)

  | axEXD' s t : prv (fEX (s :\/: t) <--> fEX s :\/: fEX t)
  | axReg' s t : prv (fAG (s ---> t) ---> fEX s ---> fEX t)

  | axSer' : prv (fEX (fF ---> fF))
  | axAXT  : prv (fAX (fF ---> fF))
  | axEUeq' s t : prv (fEU s t <--> t :\/: (s :/\: fEX (fEU s t)))
  | axAUeq' s t : prv (fAU s t <--> t :\/: (s :/\: fAX (fAU s t)))

  | axAUr' s t u : prv (fAG (u ---> ~~:t :/\: fEX u) ---> u ---> ~~: fAU s t)
  | axEUr' s t u : prv (fAG (u ---> ~~:t :/\: (s ---> fAX u)) ---> u ---> ~~: fEU s t)

  | axAXdef' s : prv (fAX s <--> ~~: fEX (~~: s))
  | axARdef' s t : prv (fAR s t <--> ~~: fEU (~~: s) (~~: t))
  .
End Hilbert.

(** ** Completeness 

We show completeness by showing admissibility of the rules and axoms of the
Hilbert system IC.

The [pSystem] instance is immedate. For the [kSystem] instance we
need to show the necessitation rule and the and normality scheme *)

Canonical Structure prv_mSystem := MSystem rMP axK axS.
Canonical Structure prv_pSystem := PSystem axDN.

Lemma axAXdef s : prv (fAX s <--> ~~: fEX (~~: s)). exact: axAXdef'. Qed.
Lemma axEXD s t : prv (fEX (s :\/: t) <--> fEX s :\/: fEX t). exact: axEXD'. Qed.
Lemma axReg s t : prv (fAG (s ---> t) ---> fEX s ---> fEX t). exact: axReg'. Qed.

Lemma rRegEX s t : prv (s ---> t) -> prv (fEX s ---> fEX t).
Proof. move => H. rule axReg. exact: rGen. Qed.

Lemma rRegAX s t : prv (s ---> t) -> prv (fAX s ---> fAX t).
Proof.
  move => H. rewrite -> (axAXdef s), -> (axAXdef t). rule ax_contraNN.
  apply: rRegEX. by rule ax_contraNN.
Qed.

Lemma rNec s : prv s -> prv (fAX s).
Proof. move => H. apply: rMP axAXT. apply: rRegAX. ApplyH H. Qed.

Lemma axABBA s t : prv (fAX s :/\: fAX t ---> fAX (s :/\: t)).
Proof.
  rewrite -> (axAXdef s),(axAXdef t),(axAXdef (s :/\: t)). rewrite <- dmO.
  rule ax_contraNN. rewrite <- axEXD. apply: rRegEX. rewrite -> dmA. exact: axI.
Qed.

Lemma axN s t : prv (fAX (s ---> t) ---> fAX s ---> fAX t).
Proof. apply: rAIL. rewrite -> axABBA. apply: rRegAX. by rule axAcase. Qed.

Canonical Structure prv_kSystem := KSystem rNec axN.

Lemma axSer : prv (fEX Top). exact: axSer'. Qed.
Lemma axEUeq s t : prv (fEU s t <--> t :\/: (s :/\: fEX (fEU s t))). exact: axEUeq'. Qed.
Lemma axAUeq s t : prv (fAU s t <--> t :\/: (s :/\: fAX (fAU s t))). exact: axAUeq'. Qed.
Lemma axAUr s t u : prv (fAG (u ---> ~~:t :/\: fEX u) ---> u ---> ~~: fAU s t). exact: axAUr'. Qed.
Lemma axEUr s t u : prv (fAG (u ---> ~~:t :/\: (s ---> fAX u)) ---> u ---> ~~: fEU s t). exact: axEUr'. Qed.
Lemma axARdef s t : prv (fAR s t <--> ~~: fEU (~~: s) (~~: t)). exact: axARdef'. Qed.


(** Admissibility of the induction rules *)

Lemma AR_ind s t u : prv (u ---> t) -> prv (u ---> (s ---> fF) ---> fAX u) -> prv (u ---> fAR s t).
Proof.
  move => H1 H2. rewrite -> axARdef. rule axEUr. apply: rGen.
  ApplyH axAI => //. by rewrite -> axDNE.
Qed.

Lemma AU_ind_aux s t u : prv (t ---> u) -> prv (fAX u ---> u) -> prv ((fAU s t) ---> u).
Proof.
  move => H1 H2. rule ax_contra. rule axAUr. apply: rGen. rewrite -> H1.
  Intro. ApplyH axAI. Rev. rule ax_contraNN. rewrite -[fAX _]/(AX (~~: (~~: u))).
  by rewrite -> axDNE.
Qed.

Lemma AU_ind s t u : prv (t ---> u) -> prv (s ---> fAX u ---> u) -> prv ((fAU s t) ---> u).
Proof.
  move => H1 H2. rewrite -> (axA2 (fAU s t)). rule axAcase. apply: AU_ind_aux.
  - rewrite <- H1. exact: axK.
  - rewrite -> axAUeq at 2. Intro. ApplyH axOE; first by ApplyH H1.
    ApplyH axAcase. do 2 Intro. ApplyH H2. ApplyH (axN (fAU s t)).
Qed.

(** Introducion/Inversion Rules *)

Lemma ax_serial : prv (fAX fF ---> fF).
Proof. rewrite -> axAXdef. Intro. Apply. drop. exact: axSer. Qed.

Lemma axAUI s t : prv (t ---> fAU s t).
Proof. rewrite -> axAUeq. exact: axContra. Qed.

Lemma axAUf s t : prv (s ---> fAX (fAU s t) ---> fAU s t).
Proof. rewrite -> axAUeq at 2. do 2 Intro. ApplyH axOIr. ApplyH axAI. Qed.

Lemma axARE s t : prv (fAR s t ---> t).
Proof. rule ax_contra. rewrite -> axARdef, axDNE,axEUeq. exact: axOIl. Qed.

Lemma axARu s t : prv (fAR s t ---> (s ---> fF) ---> fAX (fAR s t)).
Proof.
  rewrite -> axARdef at 1. rewrite -> axEUeq,dmO,dmA.
  set u := fEU _ _. rewrite -[~~: fEX u]/(~~: (~~: (fAX (~~: u)))).
  do ! rewrite -> axDNE. rewrite /u. rewrite <- axARdef. rule axAcase. Intro.
  ApplyH axOE. ApplyH axContra. do 2 Intro. by Asm.
Qed.

End Eme90.

Theorem Eme90_translation s : IC.prv s -> Eme90.prv s.
Proof.
  elim => {s}; eauto using Eme90.prv,Eme90.axARE,Eme90.axARu,Eme90.AR_ind,
               Eme90.AU_ind,Eme90.axAUI, Eme90.axAUf, Eme90.axN, Eme90.rNec,Eme90.ax_serial.
Qed.


(** ** Soundness

We show soundness by proving all rules admissible in IC. Importing IC enables
using the infrastructure for Hilbert proofs for the system IC. *)
Import IC.

Lemma rGen s : prv s -> prv (AR Bot s).
Proof.
  move => H. apply: (@modular_hilbert.rMP _ s) => //.
  apply: modular_hilbert.rAR_ind => //. do 2 drop. exact: rNec.
Qed.

Lemma axEXAXI s t : prv  (EX s ---> AX (s ---> t) ---> EX t).
Proof.
  do 2 Intro. Have (EX (s :/\: (s ---> t))). by ApplyH axDBD.
  drop. rewrite -> axAC. apply: rEXn. by rule axAcase.
Qed.


Lemma axAUr (s t u : form) : prv (AR Bot (u ---> ~~:t :/\: EX u) ---> u ---> ~~: AU s t).
Proof.
  apply: rAIL. rule ax_contra. rewrite -> axDNE. rewrite -> dmA. rewrite <- axOC.
  rewrite /Or. rewrite -> axDNE. set X := ~~: AR _ _. apply: rAU_ind.
  - rewrite /X. rewrite -> axARE. do 3 Intro. Suff (~~: t). Intro; Apply. ApplyH axAEl. by Apply.
  - drop. rewrite {2}/X. rewrite -> axAReq. rewrite -> dmA. rewrite -> axOF.
    rewrite /Or. rewrite -> axDNE. rewrite -> dmAX. rewrite -/X.
    do 3 Intro. ApplyH (axEXAXI u). ApplyH axAEr. by Apply.
Qed.

Lemma axEUr s t u : prv (AR Bot (u ---> ~~:t :/\: (s ---> fAX u)) ---> u ---> ~~: EU s t).
Proof.
  rewrite /EU. rewrite -> axDNE. apply rAIL. apply: modular_hilbert.rAR_ind.
  - rewrite -> axARE. rule axAcase. do 2 Intro. ApplyH axAEl. by Apply* 1.
  - rewrite -> axAReq at 1. rewrite -> axOF. do 2 rule axAcase. do 4 Intro. 
    rewrite <- axABBA. ApplyH axAI. Rev. rewrite -[~~: s ---> Bot]/(~~: (~~: s)).
    rewrite -> axDNE. ApplyH axAEr. Apply* 2.
Qed.

Lemma axEUeq (s t : form) : prv (EU s t <--> t :\/: s :/\: EX (EU s t)). exact: axEUeq. Qed.
Lemma axAUeq (s t : form) : prv (AU s t <--> t :\/: s :/\: AX (AU s t)). exact: axAUeq. Qed.

Lemma axEXD s t : prv (EX (s :\/: t) <--> EX s :\/: EX t).
Proof. rewrite /EX. rewrite -> dmO, <- axABBA, dmA. reflexivity. Qed.

Lemma axReg s t : prv (AR Bot (s ---> t) ---> EX s ---> EX t).
Proof.
  do 2 rewrite -> axAReq. do 2 rewrite -> axOF. rule axAcase; drop.
  rewrite -> axAC,<- axABBA. rule axAcase; drop. rule axC. exact: axEXAXI.
Qed.

Lemma axAXdef s : prv (AX s <--> ~~: EX (~~: s)).
Proof. rewrite /EX. do ! rewrite -> axDNE. reflexivity. Qed.

Lemma axARdef s t : prv (fAR s t <--> ~~: EU (~~: s) (~~: t)).
Proof. rewrite /EU. do ! rewrite -> axDNE. reflexivity. Qed.

Lemma axSer : prv (EX (fF ---> fF)).
Proof. change (prv (~~: AX (~~: (~~: fF)))). rewrite -> axDNE. exact: ax_serial. Qed.

Lemma axAXT : prv (AX (fF ---> fF)).
Proof. apply: rNec. exact: axI. Qed.


Theorem Eme90_sound s : Eme90.prv s -> prv s.
Proof.
  elim => {s}; eauto using prv,rGen,axEXD,axReg,axSer,axAXT,axEUeq,axAUeq,axAUr,axEUr,axAXdef,axARdef.
Qed.
