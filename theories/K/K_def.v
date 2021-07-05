(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs
 Require Import edone bcase fset base modular_hilbert sltype.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * K in Coq  *)

(** ** Formulas *)

Definition var := nat.

Inductive form :=
| fF
| fV   of var
| fImp of form & form
| fAX  of form.

Lemma eq_form_dec (s t : form) : { s = t} + { s <> t}.
Proof. decide equality; apply eq_comparable. Qed.

Definition form_eqMixin := EqMixin (compareP eq_form_dec).
Canonical Structure form_eqType := Eval hnf in @EqType form form_eqMixin.

(** To use formulas and other types built around formulas as base type
for the finite set libaray, we need to show that formulas are
countable. We do this by embedding formulas into the Ssreflect's
generic trees *)

Module formChoice.
  Import GenTree.

  Fixpoint pickle (s : form) :=
    match s with
      | fV v => Leaf v
      | fF => Node 0 [::]
      | fImp s t => Node 1 [:: pickle s ; pickle t]
      | fAX s => Node 2 [:: pickle s]
    end.

  Fixpoint unpickle t :=
    match t with
      | Leaf v  => Some (fV v)
      | Node 0 [::]  => Some (fF)
      | Node 1 [:: t ; t' ] =>
          obind (fun s => obind (fun s' => Some (fImp s s')) (unpickle t')) (unpickle t)
      | Node 2 [:: t ] => obind (fun s => Some (fAX s)) (unpickle t)
      | _ => None
    end.

  Lemma pickleP : pcancel pickle unpickle.
  Proof. move => s. by elim: s => //= [s -> t ->| s -> ]. Qed.
End formChoice.

Definition form_countMixin := PcanCountMixin formChoice.pickleP.
Definition form_choiceMixin := CountChoiceMixin form_countMixin.
Canonical Structure form_ChoiceType := Eval hnf in ChoiceType form form_choiceMixin.
Canonical Structure form_CountType := Eval hnf in CountType form form_countMixin.

(** ** Models

We distinguish thee classes of models

- raw models or transition systems ([ts]): The satisfaction relation [eval] is
  defined on this class

- finite models ([fmodel]): models where the type of states is finite and
  everything else is decidable

- classical models, i.e., models where [eval] is logically decidable ([cmodel]):
  This is the largest class of models for which we can show soundness of the
  hilbert system. *)

Definition stable X Y (R : X -> Y -> Prop) := forall x y, ~ ~ R x y -> R x y.
Definition ldec X Y (R : X -> Y -> Prop) := forall x y, R x y \/ ~ R x y.

Record ts := TS {
  state  :> Type;
  trans  : state -> state -> Prop;
  label  : var -> state -> Prop
}.
Prenex Implicits trans.

Record fmodel := FModel {
  fstate :> finType;
  ftrans : rel fstate;
  flabel : var -> pred fstate
}.
Prenex Implicits ftrans.

(** Make ts inferable for states of fmodels *)
Canonical ts_of_fmodel (M : fmodel) : ts := TS (@ftrans M) (@flabel M).
Coercion ts_of_fmodel : fmodel >-> ts.

Section Characterizations.
  Variables (X : Type) (e : X -> X -> Prop).
  Definition cEX (p : X -> Prop) (w : X) : Prop := exists2 v, e w v & p v.
  Definition cAX (p : X -> Prop) (w : X) : Prop := forall v, e w v -> p v.  
End Characterizations.

Fixpoint eval (M:ts) (s : form) :=
  match s with
    | fF       => (fun _ => False)
    | fV v     => label v
    | fImp s t => (fun w => eval M s w -> eval M t w)
    | fAX s    => cAX (@trans M) (eval M s)
  end.

Record cmodel := CModel { sts_of :> ts; modelP : ldec (@eval sts_of) }.

(** * Hilbert System *)

Section Hilbert.
  Local Notation "s ---> t" := (fImp s t).

  Inductive prv : form -> Prop := 
  | rMP s t : prv (s ---> t) -> prv s -> prv t
  | axK s t : prv (s ---> t ---> s)
  | axS s t u : prv ((u ---> s ---> t) ---> (u ---> s) ---> u ---> t)
  | axDN s : prv (((s ---> fF) ---> fF)  ---> s)
  | rNec s : prv s -> prv (fAX s) 
  | axN s t : prv (fAX (s ---> t) ---> fAX s ---> fAX t)
  .

  (** The hilbert system for K can be seen as a combination of a Hilbert system
  for minimal logic (M) with classical reasoning (P), and the rules/axioms for
  normal modal logics (K). *)

  Canonical Structure prv_mSystem := MSystem rMP axK axS.
  Canonical Structure prv_pSystem := PSystem axDN.
  Canonical Structure prv_kSystem := KSystem rNec axN.

  Definition valid s := forall (M:cmodel) (w:M), eval s w.

  (** ** Soundness 

   The Hilbert System is sound for classical models. *)
  
  Lemma soundness s : prv s -> forall (M:cmodel) (w:M), eval s w.
  Proof.
    elim => {s} ; try by [move => /= *; firstorder].
    move => /= s M w H. by case: (modelP s w); firstorder.  
  Qed.
  
  (** With excluded middle, every model is a classical model, and the
  Hilbert system is sound for all models *)

  Lemma xm_soundness (xm : XM) s :
    prv s -> forall (M : ts) (w : M), eval s w.
  Proof.
    move => H M w. 
    have ldec_ts : ldec (@eval M) by move => ? ?; exact: xm.
    exact: (@soundness _ H (CModel ldec_ts)).
  Qed.

  Lemma XM_required : 
    (forall s, prv s -> forall (M : ts) (w : M), eval s w) -> XM.
  Proof.
    move => snd.
    suff S : (forall P, ~ ~ P -> P). 
    { move => P. apply: S => C. apply: (C). right => p. apply C. by left. }
    move => P.
    pose L (p : var) (w :unit) := P.
    pose R (w v : unit) := True.
    pose M := TS R L.
    exact: (@snd _ (axDN (fV 0)) M tt).
Qed.

End Hilbert.

(** ** Finite Models

A model is finite, if the underlying type of states is a finite type and the
transition relation and the labeling are decidable. We show that the Hilbert
system is sound for finite models. For this we show that [eval] is decidable on
finite models. *)

Section FiniteModels.
  Variables (M : fmodel).

  Fixpoint evalb s : pred M :=
    match s with
    | fV p => flabel p
    | fF => xpred0
    | fImp s t => fun w => evalb s w ==> evalb t w
    | fAX s => fun w => [forall (v | ftrans w v) , evalb s v]
  end.

  Lemma evalP (w:M) s : reflect (@eval M s w) (evalb s w).
  Proof.
    elim: s w => //=.
    - by constructor.
    - move => * ; exact: idP.
    - move => s IHs t IHt w.
      apply: iffP (@implyP _ _) _ _ => ? /IHs ?; apply/IHt; firstorder.
    - move => s IHs w.
      apply: iffP (@forall_inP _ _ _) _ _ => H v /H /IHs; done.
  Qed.

  Lemma fin_modelP : ldec (@eval M).
  Proof. move => s w. case : (decP (evalP w s)); tauto. Qed.

End FiniteModels.

Canonical cmodel_of_fmodel (M : fmodel) := CModel (@fin_modelP M).
Coercion cmodel_of_fmodel : fmodel >-> cmodel.

(** * Signed Formulas, Clauses, and Support *)

(** ** Signed Formulas

Our decision methods employ signed formulas. we also define a number of
inversion lemmas and other useful constructiuons *)

Definition sform  := (form * bool) %type.
Notation "s ^-" := (s,false) (at level 20, format "s ^-").
Notation "s ^+" := (s,true) (at level 20, format "s ^+").

Definition interp s := match s with (t,true) => t | (t,false) => fImp t fF end.

Definition body s := match s with fAX t^+ => t^+ | fAX t^- => t^- | _ => s end.

Definition isBox s := if s is fAX s^+ then true else false.

Inductive isBox_spec s : bool -> Type :=
| isBox_true t : s = fAX t^+ -> isBox_spec s true
| isBox_false  : isBox_spec s false.

Lemma isBoxP s : isBox_spec s (isBox s).
Proof. move: s => [ [|?|? ?|?] [|]] /=; try constructor. exact: isBox_true. Qed.

Definition isDia s := if s is fAX s^- then true else false.

Inductive isDia_spec s : bool -> Type :=
| isDia_true t : s = fAX t^- -> isDia_spec s true
| isDia_false  : isDia_spec s false.

Lemma isDiaP s : isDia_spec s (isDia s).
Proof. move: s => [ [|?|? ?|?] [|]] /=; try constructor. exact: isDia_true. Qed.

(** ** Clauses and Support *)

Definition clause := {fset sform}.
Implicit Types C D : clause.

Definition sat (M:cmodel) C := exists (w:M), forall s, s \in C -> eval (interp s) w.

(** Local Consistency *)

Definition lcons (L : clause) :=
  (fF^+ \notin L) && [all s in L, if s is fV p^+ then fV p^- \notin L else true].

(** Literals and Support *)

Definition literal (s : sform) :=
  let: (t,_) := s in
  match t with
    | fV _ => true
    | fAX _ => true
    | fF    => true
    | _ => false
  end.

Fixpoint supp (L : clause) u b :=
    match u,b with
      | fImp s t,true  => supp L s false || supp L t true
      | fImp s t,false => supp L s true && supp L t false
      | _,_ => (u,b) \in L
    end.

(** For a locally consistent clause [L], the collection of formulas
supported by [L] corresponds to an (infinite) Hintikka set. *)

Notation "C |> s ^ b" := (supp C s b) (at level 30, format "C  |>  s ^ b").
Notation "C |> s ^+"  := (supp C s true) (at level 30, format "C  |>  s ^+").
Notation "C |> s ^-"  := (supp C s false) (at level 30, format "C  |>  s ^-").
Notation "C |> s"     := (supp C s.1 s.2) (at level 30).

(** Would like to use 
[Definition supp' L (s : sform) := let: (t,b) := s in supp L t b.]
[Notation "L |> t" := (supp' L t) (at level 30)]
However, simplification then breaks the notation *)

Lemma supp_mon L1 L2 s : L1 `<=` L2 -> L1 |> s -> L2 |> s.
Proof.
  move/subP => sub. case: s.
  elim => //= [|p|s IHs t IHt|s IHs] [|];
    solve [exact: sub| rewrite -?(rwP orP,rwP andP); intuition].
Qed.

Fixpoint f_weight (s : form) :=
  match s with
    | fImp s t => (f_weight s + f_weight t).+1
    | _        => 0
  end.

Lemma sweight_lit s : f_weight s.1 = 0 <-> literal s.
Proof. case: s => [[|p|s t|s] [|]] //. Qed.

Lemma supp_lit C s b : literal (s,b) -> supp C s b = ((s,b) \in C).
Proof. by case: s. Qed.

Definition form_slClass := SLClass supp_mon supp_lit sweight_lit.
Canonical Structure form_slType := SLType form_slClass.
Canonical Structure form_slpType := @SLPType prv_pSystem form_slClass.


(** Want suppC on singletons to expose the concrete support operation, not the
abstract one *)
Lemma suppC1 L s : suppC L [fset s] = L |> s.
Proof. exact: all_fset1. Qed.

Lemma satA (M:cmodel) (w:M) C :
  (forall s, s \in C -> eval (interp s) w) <-> eval [af C] w.
Proof.
  case: C => xs i /=.
  change ((forall s, s \in xs -> eval (interp s) w) <-> eval [af xs] w). 
  elim: xs {i} => [|/= s xs IH]. rewrite big_nil forall_nil /=. tauto.
  rewrite big_cons forall_cons IH {2}/And /=.
  move: (modelP (interp s) w) (modelP [af xs] w); tauto.
Qed.

Lemma href_sound C : prv ([af C] ---> Bot) -> ~ (exists M : cmodel, sat M C).
Proof. move => H [M] [w] /satA X. exact: soundness H M w X. Qed.

(** ** Request *)

Definition R C := [fset body s | s <- [fset t in C | isBox t]].

Lemma RE C s : (s^+ \in R C) = (fAX s^+ \in C).
Proof.
  apply/fimsetP/idP => [ [t] | H].
  - rewrite inE andbC. by case: (isBoxP t) => //= t' -> /= ? [->].
  - exists (fAX s^+) => //. by rewrite inE H.
Qed.

Lemma Rpos s C : s^- \notin R C.
Proof.
  apply/negP. case/fimsetP => t. rewrite inE andbC.
    by case (isBoxP t) => // t' ->.
Qed.

Lemma RU (C C' : clause) : R (C `|` C') = (R C `|` R C').
Proof. by rewrite /R sepU fimsetU. Qed.

Lemma R1 (s : sform) : R [fset s] = if s is fAX u^+ then [fset u^+] else fset0.
Proof. case: s => [[|p|s t|s] [|]]; by rewrite /R sep1 /= ?fimset1 ?fimset0. Qed.

Lemma R0 : R fset0 = fset0.
Proof. by rewrite /R sep0 fimset0. Qed.

Lemma box_request (C : clause) : prv ([af C] ---> AX [af R C]).
Proof.
  rewrite <- bigABBA. apply: bigAI. case => [s [|]]; last by rewrite (negbTE (Rpos _ _)).
  rewrite RE. exact: bigAE.
Qed.

(** ** Subformula Closure *)

Fixpoint ssub' b s :=
  (s,b) |` match s with
             | fImp s t => ssub' (negb b) s `|` ssub' b t
             | fAX t => ssub' b t
             | _ => fset0
           end.

Lemma ssub'_refl s b : (s,b) \in ssub' b s.
Proof. case: s => [|x|s t|s] /=; by rewrite !inE. Qed.

Definition ssub (s : sform) := let (t,b) := s in (ssub' b t).

Lemma ssub_refl s : s \in ssub s.
Proof. case: s. exact: ssub'_refl. Qed.

Definition sf_closed' (F : {fset sform}) (s:sform) :=
  match s with
    | (fImp s t,b) => ((s,negb b) \in F) && ((t,b) \in F)
    | (fAX s, b) => (s,b) \in F
    | _ => true
  end.
Arguments sf_closed' F !s.

Definition sf_closed (F :{fset sform}) := forall s, s \in F -> sf_closed' F s.

Lemma sf_closed'_mon (X Y : clause) s : sf_closed' X s -> X `<=` Y -> sf_closed' Y s.
Proof.
  case: s. elim => [|x|s IHs t IHt|s IHs] b H /subP sub //=;
    rewrite ?sub //=; by [case/andP: H | case/and3P: H].
Qed.

Lemma sf_ssub F s : sf_closed F -> s \in F -> ssub s `<=` F. 
Proof.
  case: s. elim => [|p|s IHs t IHt|s IHs] [|] sfc_F inF //=; 
   rewrite ?fsetU0 ?fsubUset ?fsub1 ?inF ?IHs ?IHt ?andbT //=;
   move: (sfc_F _ inF) => /=; try bcase.
Qed.

Lemma sfc_ssub s : sf_closed (ssub s).
Proof.
  case: s.
  elim => [|x|s IHs t IHt|s IHs] b //= u; rewrite !inE ?orbF.
  - by move/eqP => -> /=.
  - by move/eqP => -> /=.
  - case/orP => [/eqP ->|H] /=. by rewrite !inE !ssub'_refl.
    apply: sf_closed'_mon (fsubUr _ _).
    case/orP: H => H. apply: sf_closed'_mon (fsubUl _ _). exact: IHs.
    apply: sf_closed'_mon (fsubUr _ _). exact: IHt.
  - case/orP => [/eqP ->|H] /=. by rewrite !inE !ssub'_refl.
    apply: sf_closed'_mon (fsubUr _ _). exact: IHs.
Qed.

Lemma sfcU (X Y : {fset sform}) : sf_closed X -> sf_closed Y -> sf_closed (X `|` Y).
Proof.
  rewrite /sf_closed => /= H1 H2 s.
  case/fsetUP => [/H1 | /H2] H; apply: sf_closed'_mon H _; auto with fset.
Qed.

Definition sfc C : clause := \bigcup_(s in C) ssub s.

Lemma sfc_bigcup (T : choiceType) (C : {fset T}) F :
  (forall s, sf_closed (F s)) -> sf_closed (\bigcup_(s in C) F s).
Proof.
  move => H. apply: big_rec => [s|i D _]; by [rewrite inE|exact: sfcU].
Qed.

Lemma closed_sfc C : sf_closed (sfc C).
Proof. exact: sfc_bigcup sfc_ssub. Qed.

Lemma sub_sfc C : C `<=` (sfc C).
Proof.
  rewrite /sfc. apply/subP => s inC. apply/cupP.
  exists s => //. by rewrite inC ssub_refl.
Qed.

Lemma inU_sfc C : C \in powerset (sfc C).
Proof. by rewrite powersetE sub_sfc. Qed.

#[export] Hint Resolve closed_sfc inU_sfc : core.

Lemma RinU (F : clause) : sf_closed F -> 
  forall C, C \in powerset F -> R C \in powerset F.
Proof.
  move => sfc_F C. rewrite !powersetE => /subP H. apply/subP => s.
  case: s => s [|]; last by rewrite (negbTE (Rpos _ _)).
  by rewrite RE => /H /sfc_F.
Qed.

(** ** Size of Subformula Universes *)

Fixpoint f_size (s : form) := 
  match s with
    | fF => 1
    | fV p => 1
    | fImp s t => (f_size s + f_size t).+1
    | fAX s => (f_size s).+1
  end.

Lemma size_ssub (s : form) (b : bool) : size (ssub (s,b)) <= f_size s.
Proof.
  elim: s b => //= [|p|s IHs t IHt|s IHs] b; 
    try by rewrite fsetU0 fset1Es.
  - apply: leq_trans (fsizeU1 _ _) _. apply: leq_ltn_trans (fsizeU _ _) _.
    rewrite ltnS. exact: leq_add. 
  - apply: leq_trans (fsizeU1 _ _) _. by rewrite ltnS. 
Qed.
