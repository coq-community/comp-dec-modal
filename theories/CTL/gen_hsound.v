(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs
 Require Import edone bcase fset base induced_sym modular_hilbert sltype.
From CompDecModal.CTL
 Require Import CTL_def gen_def hilbert hilbert_hist.
Import IC.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** * Translation from Gentzen derivations to Hilbert Refutations *)

Definition hist (H : {fset clause}) := \and_(C <- H) ~~: [af C].

Lemma histU C (H : {fset clause}) :
  prv (hist (C |` H) <--> ~~: [af C] :/\: hist H).
Proof. rule axAI.
  - rewrite {1}/hist. by rewrite -> andU, bigA1.
  - rewrite {2}/hist. by rewrite -> andU, bigA1.
Qed.

Definition interp_a A :=
  match A with
    | aVoid => Top
    | aAU (s, t, H) => AU (s :/\: hist H) (t :/\: hist H)
    | aAXU (s, t, H) => AX (AU (s :/\: hist H) (t :/\: hist H))
    | aAR (s, t, H) => EU (~~:s :/\: hist H) (~~: t :/\: hist H)
    | aAXR (s, t, H) => EX (EU (~~:s :/\: hist H) (~~: t :/\: hist H))
  end.

Lemma annot_request E : prv (interp_a E ---> AX (interp_a (aR E))).
Proof.
  case: E => [[[s t] H]|[[s t] H]|[[s t] H]|[[s t] H]|]; try (Intro; ApplyH axBT).
  exact: axI.
Qed.

Lemma hist0 s : prv (s ---> s :/\: hist fset0).
Proof. Intro. ApplyH axAI. drop. rewrite /hist fset0Es big_nil. exact: axI. Qed.

Lemma hilbert_soundness A : gen A -> prv ([af A.1] ---> interp_a A.2 ---> Bot).
Proof.
  elim => {A} /=.
  - move => C E. rewrite -> andU, afp1. rule axAcase. exact: axBE.
  - move => p C E. rewrite -> andU,andU,afp1,afn1.
    rule axAcase. Intro. ApplyH axAcase; do 3 Intro. Apply* 2.
  - move => s t C E _ IHs _ IHt. rewrite -> andU, afp1. rule axAcase.
    Intro. Have (~~: s :\/: t). ApplyH axIO. drop. rule axOE.
    + rewrite <- IHs. rewrite -> andU,af1n. exact: axAI.
    + rewrite <- IHt. rewrite -> andU. rewrite -> (af1p t) at 1. exact: axAI.
  - move => s t C R _ IH. rewrite <- IH. do ! rewrite -> andU. rewrite -> afn1, <- af1p, <- af1n.
    rewrite -> dmI, axAA. exact: axI.
  - (* gen_AXn *) move => s C E _ IH.
    rewrite -> andU,afn1. rewrite -> box_request, annot_request.
    rewrite <- (axDN s); rewrite -/(EX (~~: s)). rule axAcase. do 3 Intro.
    Have (EX ( ~~: s :/\: (interp_a (aR E) :/\: [af R C]))). ApplyH axDBD. rewrite <- axABBA. by ApplyH axAI.
    drop. rewrite <- axDF. apply: rEXn. rule axAcase. Intro. ApplyH axAcase; do 2 Intro.
    ApplyH IH. rewrite -> andU, <- af1n. ApplyH axAI.
  - (* gen_AUp *) move => s t C E _ IH1 _ IH2.
    rewrite -> andU, afp1, axAUeq. rewrite -> axADr. rule axOE.
    + by rewrite -> (af1p t), <- andU.
    + rewrite -> (af1p s) at 1. rewrite -> (af1p (AX (AU s t))). do 2 rewrite <- andU.
      by rewrite -fsetUA.
  - (* gen_AUn *) move => s t C R _ IH1 _ IH2.
    rewrite -> andU,afn1. rewrite -> axAC. rule axAcase. Intro.
    rewrite -> (dmAU s t), axERu. ApplyH axAcase; Intro. ApplyH axOE; Intro.
    - ApplyH IH1. do ! rewrite -> andU. do ! rewrite <- af1n. do ! ApplyH axAI.
    - ApplyH IH2. do ! rewrite -> andU. do ! rewrite <- af1n. ApplyH axAI. ApplyH axAI.
      Rev. drop. do 2 Intro.
      Have (EX (ER (~~: s) (~~: t) :/\: fAU s t)). by ApplyH axDBD.
      drop. rewrite -> axAC, axAUERF. exact: axDF.
  - (* gen_AUfoc *) move => s t C _ IH. rewrite -> andU, afp1.
    do ! rewrite <- hist0 in IH. rule axAcase. do 3 Intro. by ApplyH IH.
  - (* gen_AUh *) move => s t H C _ IH1 _ IH2.
    apply: AUH_hil. 
    + rule axAcase. do 2 Intro. ApplyH IH1. rewrite -> andU, <- af1p. ApplyH axAI. exact: axsT.
    + rewrite /AU_. rewrite <- histU. do 3 Intro. ApplyH IH2. rewrite -> andU, <- af1p. by ApplyH axAI.
  - (* gen_AUrep *) move => s t H C.
    rewrite -> axAUAEr, histU. rewrite -> axAEl. do 2 Intro. Apply.
  - (* gen_ARp *) move => s t C E _ IH1 _ IH2.
    rewrite -> andU,afp1. rewrite -> axAReq. do 2 rule axAcase. rule axC. rule axOE.
    + do 3 Intro. ApplyH IH1. do 2 rewrite -> andU. do 2 rewrite <- af1p. by do 2 ApplyH axAI.
    + do 3 Intro. ApplyH IH2. do 2 rewrite -> andU. do 2 rewrite <- af1p. by do 2 ApplyH axAI.
  - (* gen_ARn *) move => s t C E _ IH1 _ IH2.
    rewrite -> andU,afn1. rewrite -> (dmAR s t). rewrite -> axEUeq. rule axAcase. rule axOE.
    + do 3 Intro. ApplyH IH1. rewrite -> andU. rewrite <- af1n. by ApplyH axAI.
    + rule axAcase. do 3 Intro. ApplyH IH2. do 2 rewrite -> andU. do 2 rewrite <- af1n.
      rewrite /=. rewrite -> dmAX. rewrite -> dmAR. by do 2 ApplyH axAI.
  - (* gen_ARfoc *) move => s t C _ IH. rewrite -> andU,afn1 => /=. rewrite -> dmAR. rule axAcase. do 3 Intro.
    do 2 rewrite <- hist0 in IH. by ApplyH IH.
  - (* gen_ARh *) move => s t H C _ IH1 _ IH2. apply: ARH_hil.
    - rewrite -> andU in IH1. do 2 Intro. ApplyH IH1; last by drop; exact: axI.
      rewrite <- af1n. by ApplyH axAI.
    - rewrite /EU_. rewrite <- histU. do 3 Intro. ApplyH IH2. rewrite -> andU. rewrite <- af1n. by ApplyH axAI.
  - (* gen_ARrep *) move => s t H C.
    rewrite -> axEUEr. rewrite -> histU,axAEl. exact: axContra.
  - (* gen_aAXR *) move => s t H C _ IH. rewrite -> box_request. do 2 Intro.
    Suff (EX fF). drop. Intro. Apply. drop. exact: axBT.
    Suff (EX ([af R C] :/\: EU (~~: s :/\: hist H) (~~: t :/\: hist H))).
    drop. apply: rEXn. by rule axAcase.
    rewrite <- (axAC _ [af R C]). ApplyH axDBD.
  - (* gen_jmp *) move => C E _ IH.
    rewrite -> box_request, annot_request. do 2 Intro.
    Have (~~: fAX fF). ApplyH ax_serial. rewrite <- (axDN fF) at 1; rewrite -/(EX Top). Intro.
    Have (EX ( Top :/\: (interp_a (aR E) :/\: [af R C]))). ApplyH axDBD. rewrite <- axABBA. by ApplyH axAI.
    drop. rewrite <- axDF. apply: rEXn. rule axAcase. drop. rule axAcase; do 2 Intro.
    Rev* 1. Rev. done.
Qed.

Lemma plain_soundness C : gen (C,aVoid) -> prv (~~: [af C]).
Proof. move/hilbert_soundness => /= H. Intro. ApplyH H. by drop. Qed.
