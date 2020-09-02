(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)

(** * A simple checker for boolean tautologies *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.

Ltac bcase_atom b :=
  match b with
    | _ || _ => fail 1
    | _ && _ => fail 1
    | _ ==> _ => fail 1
    | _ => idtac
  end.

Ltac bcase_rec :=
  try reflexivity;
  match goal with
    | [ |- context[ ?b || _ ] ] => bcase_atom b; case: b
    | [ |- context[ ?b && _ ] ] => bcase_atom b; case: b
    | [ |- context[ ?b ==> _ ] ] => bcase_atom b; case: b
  end; rewrite /= ?andbT ?andbF ?orbT ?orbF; [bcase_rec..].

Ltac bcaseHyps :=
  (repeat match goal with
            | [ H : is_true ?b |- _ ] => move : H ; apply/implyP
          end).

Ltac bcase := move => * ; bcaseHyps ; bcase_rec.
