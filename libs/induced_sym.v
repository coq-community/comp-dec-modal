(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Setoid Morphisms Basics.

(** * Induced Symmetric Subrelations *)

(** Every relation P induces a symmetyic subrelation.  For a
   [PreOrder] P, this is an Equivalence. Defining [InducedSym] as a
   class, allows for non-convertible but extensionally equal
   definitions of the induced subrelation. *)

Class InducedSym {T : Type} (P R : relation T) :=
  induced_iff : forall x y, R x y <-> P x y /\ P y x.

Instance induced_sub {T : Type} (P R : relation T) :
  InducedSym P R -> subrelation R P.
Proof. firstorder. Qed.

Ltac induced_tac R :=
  (repeat match goal with
            | [ H : R ?x ?y |- _] => apply induced_iff in H
            | [ |- R ?x ?y ] => apply induced_iff
          end); firstorder.

Lemma induced_eqi {T : Type} (P R : relation T) :
  PreOrder P -> InducedSym P R -> Equivalence R.
Proof.
  intros pre ind. split. firstorder.
  - intros x y Rxy; induced_tac R.
  - intros x y z Rxy Ryz. destruct pre; induced_tac R.
Qed.

Lemma induced_mor_iff {T : Type} (P R : relation T) m :
  InducedSym P R -> Proper (P ==> impl) m -> Proper (R ==> iff) m.
Proof. intros ind prop x y Rxy; induced_tac R. Qed.

Lemma induced_mor_iff2 {T : Type} (P R : relation T) m :
  PreOrder P -> InducedSym P R -> Proper (P ==> P --> impl) m -> Proper (R ==> R ==> iff) m.
Proof.
  intros pre ind prop x y Rxy x' y' Rxy'.
  apply induced_iff in Rxy. apply induced_iff in Rxy'.
  destruct Rxy as [Pxy Pyx]. destruct Rxy' as [Pxy' Pyx'].
  generalize (prop _ _ Pxy  _ _ Pyx').
  generalize (prop _ _ Pyx _ _ Pxy').
  firstorder.
Qed.

Instance induced_mor_p {T : Type} (P R : relation T) m :
  InducedSym P R -> Proper (P ==> P) m -> Proper (R ==> R) m.
Proof. intros ind prop x y Rxy; induced_tac R. Qed.

Instance induced_mor_n {T : Type} (P R : relation T) m :
  InducedSym P R -> Proper (P --> P) m -> Proper (R ==> R) m.
Proof. intros ind prop x y Rxy; induced_tac R. Qed.

Instance induced_mor_pp {T : Type} (P R : relation T) m :
  InducedSym P R -> Proper (P ==> P ==> P) m -> Proper (R ==> R ==> R) m.
Proof. intros ind prop x y Rxy x' y' Rxy'; induced_tac R. Qed.

Instance induced_mor_pn {T : Type} (P R : relation T) m :
  InducedSym P R -> Proper (P ==> P --> P) m -> Proper (R ==> R ==> R) m.
Proof. intros ind prop x y Rxy x' y' Rxy'; induced_tac R. Qed.

Instance induced_mor_np {T : Type} (P R : relation T) m :
  InducedSym P R -> Proper (P --> P ==> P) m -> Proper (R ==> R ==> R) m.
Proof. intros ind prop x y Rxy x' y' Rxy'; induced_tac R. Qed.
