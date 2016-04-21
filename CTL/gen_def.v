(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base.
Require Import CTL_def.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * History-Based Gentzen System for CTL *)

(** As for formulas, we need to show that the type of annotations is a
countable type. *)

Inductive annot :=
| aAU of form * form * {fset clause}
| aAXU of form * form * {fset clause}
| aAR of form * form * {fset clause}
| aAXR of form * form * {fset clause}
| aVoid.

Lemma eq_annot_dec (E1 E2 : annot) : {E1 = E2} + {E1 <> E2}.
Proof. decide equality; apply: eq_comparable. Qed.

Definition annot_eqMixin := EqMixin (compareP eq_annot_dec).
Canonical Structure annot_eqType := Eval hnf in @EqType annot annot_eqMixin.

Definition aR (E : annot) := if E is aAXU (p, H) then aAU (p,H) else aVoid.

Module Annot.
  Definition pickle A :=
    match A with
      | aAU s => (1,pickle s)
      | aAXU s => (2,pickle s)
      | aVoid => (3,0)
      | aAR s => (4,pickle s)
      | aAXR s => (5,pickle s)
    end.

  Prenex Implicits Some.

  Definition unpickle p :=
    match p with
      | (1,n) => obind (Some \o aAU) (unpickle n)
      | (2,n) => obind (Some \o aAXU) (unpickle n)
      | (3,_) => Some aVoid
      | (4,n) => obind (Some \o aAR) (unpickle n)
      | (5,n) => obind (Some \o aAXR) (unpickle n)
      | _ => None
    end.

  Lemma pickleP : pcancel pickle unpickle.
  Proof. move => s. case: s => //= p; by rewrite pickleK. Qed.
End Annot.


Definition annot_countMixin := PcanCountMixin (Annot.pickleP).
Definition annot_choiceMixin := CountChoiceMixin annot_countMixin.
Canonical Structure annot_choiceType := Eval hnf in ChoiceType annot annot_choiceMixin.
Canonical Structure annot_CountType := Eval hnf in CountType annot annot_countMixin.

Implicit Types (C : clause) (E : annot).

(** [gen_jmp] placed last, so that the constructor tactic tries more specific rules first *)

Inductive gen : clause * annot -> Prop :=
| gen_F C E :
    gen (fF^+ |` C, E)
| gen_p p C E :
    gen ([fset fV p^+ , fV p^-  & C], E)
| gen_Ip s t C E :
    gen (s^- |` C, E) -> gen (t^+ |` C, E) -> gen (fImp s t^+ |` C, E)
| gen_In s t C E :
    gen ([fset s^+ , t^- & C], E) -> gen (fImp s t^- |` C, E)
| gen_AXn s C E :
    gen (s^- |` R C, aR E) -> gen (fAX s^- |` C , E)
| gen_AUp s t C E :
    gen (t^+ |` C,E) -> gen ([fset s^+, fAX (fAU s t)^+ & C],E) -> gen (fAU s t^+ |` C,E)
| gen_AUn s t C E :
    gen ([fset s^-, t^- & C], E) -> gen ([fset t^-, fAX (fAU s t)^- & C],E) -> gen (fAU s t^- |` C, E)
| gen_AUfoc s t C :
    gen (C,aAU (s, t, fset0)) -> gen (fAU s t^+ |` C , aVoid)
| gen_AUh s t H C :
    gen (t^+ |` C, aVoid) -> gen (s^+ |` C, aAXU (s, t, C |` H)) -> gen (C, aAU (s, t, H))
| gen_AUrep s t H C :
    gen (C, aAU (s, t, C |` H))
| gen_ARp s t C E :
    gen ([fset s^+, t^+ & C],E) -> gen ([fset t^+, fAX (fAR s t)^+ & C],E) -> gen (fAR s t^+ |` C,E)
| gen_ARn s t C E :
    gen (t^- |` C,E) -> gen ([fset s^-, fAX (fAR s t)^- & C],E) -> gen (fAR s t^- |` C,E)
| gen_ARfoc s t C :
    gen (C, aAR (s,t,fset0)) -> gen (fAR s t^- |` C, aVoid)
| gen_ARh s t H C :
    gen (t^- |` C, aVoid) -> gen (s^- |` C, aAXR (s,t,C |` H)) -> gen (C, aAR (s,t,H))
| gen_ARrep s t H C :
    gen (C,aAR(s,t,C |` H))
| gen_aAXR s t H C :
    gen (R C, aAR (s,t,H)) -> gen (C, aAXR (s,t,H))
| gen_jmp C E : 
    gen (R C, aR E) -> gen (C,E)
.

