(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs
 Require Import edone bcase fset base modular_hilbert sltype.

From CompDecModal.Kstar
 Require Import Kstar_def.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * History-based Gentzen system for K* *)

(** As for formulas, we need to show that the type of annotations is a
countable type. *)

Inductive annot :=
| aAG of form * {fset clause}
| aAXG of form * {fset clause}
| aVoid.

Lemma eq_annot_dec (E1 E2 : annot) : {E1 = E2} + {E1 <> E2}.
Proof. decide equality; apply: eq_comparable. Qed.

Definition annot_eqMixin := EqMixin (compareP eq_annot_dec).
Canonical Structure annot_eqType := Eval hnf in @EqType annot annot_eqMixin.

Module Annot.
  Definition pickle A :=
    match A with
      | aAG s => (1,pickle s)
      | aAXG s => (2,pickle s)
      | aVoid => (3,0)
    end.

  Prenex Implicits Some.

  Definition unpickle p :=
    match p with
      | (1,n) => obind (Some \o aAG) (unpickle n)
      | (2,n) => obind (Some \o aAXG) (unpickle n)
      | (3,_) => Some aVoid
      | _ => None
    end.

  Lemma pickleP : pcancel pickle unpickle.
  Proof. move => s. case: s => //= p; by rewrite pickleK. Qed.
End Annot.


Definition annot_countMixin := PcanCountMixin (Annot.pickleP).
Definition annot_choiceMixin := CountChoiceMixin annot_countMixin.
Canonical Structure annot_choiceType := Eval hnf in ChoiceType annot annot_choiceMixin.
Canonical Structure annot_CountType := Eval hnf in CountType annot annot_countMixin.

Implicit Types (S H : {fset clause}) (C D E : clause) (a : annot) (Ca : clause * annot).

(** Definition of the Rules *)

Inductive gen : clause * annot -> Prop :=
| gen_F C a :
    gen (fF^+ |` C, a)
| gen_p p C a :
    gen ([fset fV p^+ , fV p^-  & C], a)
| gen_Ip s t C a :
    gen (s^- |` C, a) -> gen (t^+ |` C, a) -> gen (fImp s t^+ |` C, a)
| gen_In s t C a :
    gen ([fset s^+ , t^- & C], a) -> gen (fImp s t^- |` C, a)
| gen_AXn s C a :
    gen (s^- |` R C, aVoid) -> gen (fAX s^- |` C , a)
| gen_AXH s C H :
    gen (R C,aAG (s,H)) -> gen (C,aAXG (s,H))
| gen_AGp s C a :
    gen ([fset s^+ , fAX (fAG s)^+ & C],a ) -> gen (fAG s^+ |` C,a)
| gen_AGn s C a :
    gen (s^- |` C, a) -> gen (fAX (fAG s)^- |` C,a) -> gen (fAG s^- |` C, a)
| gen_foc s C :
    gen (C,aAXG (s,fset0)) -> gen (fAX (fAG s)^- |` C,aVoid)
| gen_AGh s C H :
    gen (s^- |` C, aVoid) -> gen (C, aAXG (s,C |` H))-> gen (C,aAG (s,H))
| gen_rep s C H :
    gen (C, aAG(s,C |` H))
.

(** ** Soundness for Finite Models *)

Definition satC (M : fmodel) (w:M) C := [all s in C, evalb (interp s) w].

Lemma satCU (M : fmodel) (w:M) C D : satC w (C `|` D) = satC w C && satC w D.
Proof. exact: allU. Qed.

Lemma satC1 (M : fmodel) (w:M) s D : satC w (s |` D) = evalb (interp s) w && satC w D.
Proof. by rewrite satCU /satC {1}fset1Es /= andbT. Qed.

Definition dsatH (M : fmodel) (w:M) H := [all C in H, ~~ satC w C].

Lemma dsat0 (M : fmodel) (w:M) : dsatH w fset0. 
Proof. by rewrite /dsatH fset0Es. Qed.

Lemma dsatU1 (M : fmodel) (w:M) H C : dsatH w (C |` H) = ~~ satC w C && dsatH w H.
Proof. by rewrite /dsatH allU fset1Es /=. Qed.


Inductive hist (M: fmodel) H s (w:M) : Prop :=
| hist0   : dsatH w H -> ~~ evalb s w -> hist H s w
| histS v : dsatH w H -> ftrans w v -> hist H s v -> hist H s w.

Lemma hist_dsatH (M: fmodel) H s (w:M) : hist H s w -> dsatH w H.
Proof. by case. Qed.

Definition satA (M: fmodel) (w:M) a :=
  match a with
  | aAG (s,H) => hist H s w
  | aAXG (s,H) => exists2 v, ftrans w v & hist H s v
  | aVoid => True
  end.

Lemma sat_hist0 (M : fmodel) (w : M) s : ~~ evalb (fAG s) w -> hist fset0 s w.
Proof. 
  rewrite /= /AGb inE negbK.
  move: w. apply lfp_ind; first by move => ?;rewrite inE.
  move => A IH w. rewrite !inE negb_and.
  case/orP; first (apply: hist0; exact: dsat0).
  case/forall_inPn => v wv. rewrite inE negbK => inA.
  apply: histS wv _. apply dsat0. exact: IH.
Qed.

Definition satCA (M : fmodel) (w : M) Ca := satC w Ca.1 /\ satA w Ca.2.

Definition funsat (M : fmodel) Ca := ~ exists w:M, satCA w Ca.

Lemma funsat2 (M : fmodel) C C1 C2 a : (forall w:M, satC w C -> satC w C1 || satC w C2) ->
  funsat M (C1,a) -> funsat M (C2,a) -> funsat M (C,a).
Proof.
  move => H U1 U2 [w] [/= w1 w2]. 
  case/orP: (H _ w1) => Hw; [apply U1|apply U2]; by exists w.
Qed.

Lemma funsat1 (M : fmodel) C C1 a : (forall w:M, satC w C -> satC w C1) ->
  funsat M (C1,a) -> funsat M (C,a).
Proof. move => H U [w] [/= /H w1 w2]. apply U. by exists w. Qed.

Lemma satU1P (M : fmodel) (w : M) s C : reflect (evalb (interp s) w /\ satC w C) (satC w (s |` C)).
Proof. rewrite satC1. exact: andP. Qed.

Lemma satCR (M : fmodel) (w v : M) C : satC w C -> ftrans w v -> satC v (R C).  
Proof. 
  move => /allP H1 H2. apply/allP => [[s [|]]]; rewrite ?(negbTE (Rpos _ _)) // RE.
  move/H1 => /forall_inP /(_ _ H2). done.
Qed.

Lemma evalbAG (M : fmodel) (w : M) s : evalb (fAG s) w = (evalb s w && evalb (fAX (fAG s)) w).
Proof. by rewrite [fAX _]lock /= /AGb (gfpE (AR_mono _ _)) inE -lock. Qed.

Lemma soundness (M : fmodel) Ca : gen Ca -> funsat M Ca.
Proof.
  elim => {Ca}.
  - move => C E [w] [/=]. by rewrite satC1 /=.
  - move => p C E [w] [/=]. rewrite !satC1 /=. by case: (flabel _).
  - move => s t C a _ U1 _ U2. 
    apply: funsat2 U1 U2; by (move => w; rewrite ?satC1 /=; bcase).
  - move => s t C a _ U1. 
    apply: funsat1 U1; by (move => w; rewrite ?satC1 /=; bcase).
  - move => s C a _ U1 [w] [/=]. case/satU1P. 
    rewrite /= implybF negb_forall => /existsP [v]. 
    rewrite negb_imply => /andP [A B] H _. apply U1. exists v.
    split => //=. rewrite satC1 /= implybF B /=. exact: satCR A.
  - move => s C H _ U1 [w] [/= wC] [v wv hst]. apply: U1.
    exists v => //. split => //=. exact: satCR wv.
  - move => s C a _ U1. apply: funsat1 U1.
    move => w. rewrite !satC1 [interp _]/= evalbAG. bcase.
  - move => s C a _ U1 _ U2. apply: funsat2 U1 U2 => w.
    rewrite !satC1 [interp _]/= [fAG _]lock [fAX _]lock /= -!lock evalbAG. bcase.
  - (* gen_foc *)
    move => s C _ IH [w] [/= /satU1P [w1 w2] _]. apply IH; exists w. 
    split => //=. case/forall_inPn : w1 => v wv H. exists v => //. exact: sat_hist0.
  - (* gen_AGh *)
    move => s C H _ IH1 _ IH2 [w [/= w1 w2]].
    case: w2 => [_ ws|v wH wv Hv].
    apply: (IH1). exists w. split => //=. by rewrite satC1 w1.
    apply: (IH2). exists w. split => //=. exists v => //. 
    elim: {w w1 wH wv} Hv => {v} - v.
      * move => v1 v2. apply: hist0 (v2). rewrite dsatU1 v1 andbT.
        apply/negP => HC. apply IH1. exists v. split => //=. by rewrite satC1 HC.
      * move => u vH vu _ H2. apply: histS (vu) (H2). rewrite dsatU1 vH andbT.
        apply/negP => HC. apply IH2. exists v. split => //=. by exists u.
  - (* gen_rep *)
    move => s C H [w] [/= D1 /hist_dsatH D2]. by rewrite dsatU1 D1 in D2.
Qed.
