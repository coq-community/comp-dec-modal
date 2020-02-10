(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.
Require Import CTL_def.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Hilbert System for CTL *)

Module IC.
Section Hilbert.
  Local Notation "s ---> t" := (fImp s t).

  Inductive prv : form -> Prop :=
  | rMP s t : prv (s ---> t) -> prv s -> prv t
  | axK s t : prv (s ---> t ---> s)
  | axS s t u : prv ((u ---> s ---> t) ---> (u ---> s) ---> u ---> t)
  | axDN s : prv (((s ---> fF) ---> fF)  ---> s)
  | rNec s : prv s -> prv (fAX s)
  | axN s t : prv (fAX (s ---> t) ---> fAX s ---> fAX t)

  | AU_ind s t u : prv (t ---> u) -> prv (s ---> fAX u ---> u) -> prv ((fAU s t) ---> u)
  | axAUI s t     : prv (t ---> fAU s t)
  | axAUf s t     : prv (s ---> fAX (fAU s t) ---> fAU s t)

  | rAR_ind s t u :
      prv (u ---> t) -> prv (u ---> (s ---> fF) ---> fAX u) -> prv (u ---> fAR s t)
  | axARE s t    : prv (fAR s t ---> t)
  | axARu s t    : prv (fAR s t ---> (s ---> fF) ---> fAX (fAR s t))

  | ax_serial : prv (fAX fF ---> fF).

  (** The hilbert system for CTL can be seen as the composition of
  Hilbert systems for minimal logic (M), classical propositional logic
  (P), basic modal logic (K) and the rules and axioms specific to CTL *)

  Canonical Structure prv_mSystem := MSystem rMP axK axS.
  Canonical Structure prv_pSystem := PSystem axDN.
  Canonical Structure prv_kSystem := KSystem rNec axN.
  Canonical Structure prv_ctlSystem := CTLSystem AU_ind axAUI axAUf rAR_ind axARE axARu.

  Canonical Structure form_slpType := @SLPType prv_pSystem form_slClass.

  (** ** Soundness *)

  Lemma soundness s : prv s -> forall (M:cmodel) (w:M), eval s w.
  Proof.
    elim => {s}; try by [move => /= *; firstorder].
    - move => /= s M w H. by case: (modelP s w); firstorder.
    - move => s t u _ /= IH1 _ IH2 M w. elim => {w} - w; first exact: IH1.
      move => ws H1 H2. exact: IH2.
    - move => s t M w /=. exact: AU0.
    - move => s t M w /=. exact: AUs.
    - move => s t u _ IH1 _ IH2.
      cofix soundness => /= M w H. case (modelP s w) => Hs.
      - apply: AR0 Hs _. exact: IH1 H.
      - apply: ARs. exact: IH1 H. move => v wv. apply: soundness.
        exact: IH2 wv.
    - move => s t M w /=. by case.
    - move => s t M w /=. by case.
    - move => M w /=. case: (serial w) => v wv. by move/(_ _ wv).
  Qed.

  Lemma box_request (C : clause) : prv ([af C] ---> AX [af R C]).
  Proof.
    rewrite <- bigABBA. apply: bigAI. case => [s [|]]; last by rewrite (negbTE (Rpos _ _)).
    rewrite RE. exact: bigAE.
  Qed.

End Hilbert.
End IC.

