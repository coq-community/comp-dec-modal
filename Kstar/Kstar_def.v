(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * K* in Coq  *)

Notation "P =p Q" := (forall x, P x <-> Q x) (at level 40).
Definition PredC X (p : X -> Prop) x := ~ p x.

Arguments clos_refl_trans [A] R x _.

Section Characterizations.
  (** ** Inductive Characterizations *)

  Variables (X : Type) (e : X -> X -> Prop).

  Definition cEX (p : X -> Prop) (w : X) : Prop := exists2 v, e w v & p v.
  Definition cAX (p : X -> Prop) (w : X) : Prop := forall v, e w v -> p v.

  CoInductive cAG (p : X -> Prop) (w : X) : Prop :=
  | AGs : p w -> (forall v, e w v -> cAG p v) -> cAG p w.

  (** The coinductive definiton of AG is equivalent to the standard
  defintion using reflexive transitive closure. *)

  Fact cAG_crt p w :
    cAG p w <-> forall v, clos_refl_trans e w v -> p v.
  Proof.
    split.
    - move => C v H. apply clos_rt_rt1n in H.
      by elim: H C => [x|x y z xy _ IH]; case => // _ /(_ _ xy).
    - move: w. cofix cAG_crt => w H. apply: AGs; first by apply H,rt_refl.
      move => v wv. apply: cAG_crt => v' vv'. apply: H.
      eauto using rt_step, rt_trans.
  Qed.  

  Inductive cEF (p : X -> Prop) (w : X) : Prop :=
  | EF0 : p w -> cEF p w
  | EFs v : e w v -> cEF p v -> cEF p w.

  Lemma cAG_cEF (p : X -> Prop) (w : X) :
    cEF (PredC p) w -> ~ cAG p w.
  Proof.
    move => E A. elim: E A => {w}[w qw|w v wv]; first by case.
    move => _ IH. case => //. by firstorder.
  Qed.

  (** Strengthening Lemmas *)

  Lemma AG_strengthen (p1 p2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> cAG p1 w -> cAG p2 w.
  Proof.
    move => H1. move: w. cofix AG_strengthen => w. case => [/H1 p2w IH].
    by apply: AGs p2w _ => v /IH /AG_strengthen. 
  Qed.

  Lemma EF_strengthen (p1 p2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> cEF p1 w -> cEF p2 w.
  Proof.
    move => H1. elim => {w} - w; first by move => ?; apply EF0; auto.
    move => v wv ? IH. by apply: EFs ; auto.
  Qed.
  
End Characterizations.

(** ** Formulas *)

Definition var := nat.

Inductive form :=
| fF
| fV   of var
| fImp of form & form
| fAX  of form
| fAG  of form.

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
      | fAG s => Node 3 [:: pickle s]
    end.

  Fixpoint unpickle t :=
    match t with
      | Leaf v  => Some (fV v)
      | Node 0 [::]  => Some (fF)
      | Node 1 [:: t ; t' ] =>
          obind (fun s => obind (fun s' => Some (fImp s s')) (unpickle t')) (unpickle t)
      | Node 2 [:: t ] => obind (fun s => Some (fAX s)) (unpickle t)
      | Node 3 [:: t ] => obind (fun s => Some (fAG s)) (unpickle t)
      | _ => None
    end.

  Lemma pickleP : pcancel pickle unpickle.
  Proof. move => s. by elim: s => //= [s -> t ->| s -> | s -> ]. Qed.
End formChoice.

Definition form_countMixin := PcanCountMixin formChoice.pickleP.
Definition form_choiceMixin := CountChoiceMixin form_countMixin.
Canonical Structure form_ChoiceType := Eval hnf in ChoiceType form form_choiceMixin.
Canonical Structure form_CountType := Eval hnf in CountType form form_countMixin.

(** ** Models 

We distinguish thee classes of models

- raw models or transition systems ([ts]): The inductive
  satisfaction relation [eval] is defined on this class

- finite models ([fmodel]): models where the type of states is finite and
  everything else is decidable 

- classical models, i.e., models where [eval] is logically decidable
  ([cmodel]): This is the largest class of models for which we can show
  soundness of the hilbert system. *)

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

Fixpoint eval (M:ts) (s : form) :=
  match s with
    | fF       => (fun _ => False)
    | fV v     => label v
    | fImp s t => (fun w => eval M s w -> eval M t w)
    | fAX s    => cAX (@trans M) (eval M s)
    | fAG s    => cAG trans (eval M s) 
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

  | axAGEl s    : prv (fAG s ---> s)
  | axAGEr s    : prv (fAG s ---> fAX (fAG s))
  | rAG_ind u s : prv (u ---> fAX u) -> prv (u ---> s) -> prv (u --->fAG s)
  .

  (** The hilbert system for K* can be seen as the composition of
  Hilbert systems for minimal logic (M), classical propositional logic
  (P), basic modal logic (K) and the rules and axioms specific to K* *)  

  Canonical Structure prv_mSystem := MSystem rMP axK axS.
  Canonical Structure prv_pSystem := PSystem axDN.
  Canonical Structure prv_kSystem := KSystem rNec axN.
  Canonical Structure prv_ksSystem := KSSystem axAGEl axAGEr rAG_ind.
    

  Definition valid s := forall (M:cmodel) (w:M), eval s w.

  (** ** Soundness 

   The Hilbert System is sound for classical models. *)
  
  Lemma soundness s : prv s -> forall (M:cmodel) (w:M), eval s w.
  Proof.
    elim => {s}. (* try by [move => /= *; firstorder]. -- unfortunately diverges *)
    - by [move => /= *; firstorder].
    - by [move => /= *; firstorder].
    - by [move => /= *; firstorder].
    - move => /= s M w H. by case: (modelP s w); firstorder.  
    - by [move => /= *; firstorder].
    - by [move => /= *; firstorder].
    - by move => s M w [H ?].
    - by move => s M w [? H].
    - move => u s _ Hstep _ Hs M. cofix soundness => w /= Hw.
      apply: AGs => [|v wv]; first exact: Hs.
      apply: soundness. exact: Hstep wv.
  Qed.

  (** With excluded middle, every model is a classical model, and the
  Hilbert system is sound for all models *)

  Lemma xm_soundness (xm : forall P, P \/ ~ P) s :
    prv s -> forall (M : ts) (w : M), eval s w.
  Proof.
    move => H M w. 
    have ldec_ts : ldec (@eval M) by move => ? ?; exact: xm.
    exact: (@soundness _ H (CModel ldec_ts)).
  Qed.

End Hilbert.

(** ** Equivalence to Segerberg style Hilbert system *)

Module S.
Section Seg.
  Local Notation "s ---> t" := (fImp s t).

  Inductive prv : form -> Prop := 
  | rMP s t : prv (s ---> t) -> prv s -> prv t
  | axK s t : prv (s ---> t ---> s)
  | axS s t u : prv ((u ---> s ---> t) ---> (u ---> s) ---> u ---> t)
  | axDN s : prv (((s ---> fF) ---> fF)  ---> s)
  | rNec s : prv s -> prv (fAX s) 
  | axN s t : prv (fAX (s ---> t) ---> fAX s ---> fAX t)

  | axAGEl s    : prv (fAG s ---> s)
  | axAGEr s    : prv (fAG s ---> fAX (fAG s))

  | axSeg s     : prv (fAG (s ---> fAX s) ---> s --->  fAG s)
  | axNS  s t   : prv (fAG (s ---> t) ---> fAG s ---> fAG t)
  | rNecS s     : prv s -> prv (fAG s)
  .

End Seg.
End S.

Ltac S_rule H :=
  first [ eapply S.rMP; first eapply H | eapply S.rMP; first eapply S.rMP; first eapply H ].

Fact prv_Sprv s : prv s <-> S.prv s.
Proof.
  split.
  - elim => {s}; try by constructor.
    + move => ? ? ? ? ?. exact: S.rMP.
    + move => u s _ IH1 _ IH2.
      have H1 : S.prv (AG (u ---> AX u)). exact: S.rNecS.
      have H2 : S.prv (AG (u ---> s)). exact: S.rNecS.
      S_rule S.axS. S_rule S.axK. S_rule S.axNS. apply H2.
      by S_rule S.axSeg.
  - elim => {s}; try by constructor.
    + move => ? ? ? ? ?. exact: rMP.
    + move => t. exact: segerberg.
    + move => s t. exact: axAGN.
    + move => s _ . exact: rNecS.
Qed.


(** ** Soundness for Finite Models 

A model is finite, if the underlying type of states is a finite type.
We show that the Hilbert system is sound for finite models. For this
we show that [eval] is decidable on finite models. For this we need to evaluate the
evanutalities. This requires a boolean reflection of AG which we
obtain using a fixpoint computation *)

Section DecidabilityAndAgreement.
  Variables (T: finType) (e : rel T) (p : pred T).

  Definition AG_fun (X : {set T}) := [set x | p x && [forall (y | e x y), y \in X]].

  Lemma AR_mono : mono AG_fun.
  Proof.
    move => X Y S. apply/subsetP => x; rewrite !inE.
    case (p x) => //= ?. apply/forall_inP => y xy. apply: (subsetP S). by apply/forall_inP : y xy.
  Qed.

  Definition AGb w := w \in gfp AG_fun.

  Lemma agP w : reflect (cAG e p w) (AGb w).
  Proof.
    rewrite /AGb; apply (iffP idP).
    - move: w. cofix agP => w. rewrite (gfpE AR_mono) !inE. 
      case/andP => [x1 x2].
      apply: AGs _ => [//|v wv]. apply: agP. exact: (forall_inP x2). 
    - apply: gfp_ind2 => {w} - w X CH. 
      case => pw H. rewrite inE pw /=. apply/forall_inP => v /H. exact: CH.
  Qed.
                                    
End DecidabilityAndAgreement.

Arguments agP {T e p w}.

(** Given decidability and correctness for AG, decidavility and
correctness of [evalb] follows using a simple induction on formulas *)

Section FiniteModels.
  Variables (M : fmodel).

  Fixpoint evalb s : pred M :=
    match s with
    | fV p => flabel p
    | fF => xpred0
    | fImp s t => fun w => evalb s w ==> evalb t w
    | fAX s => fun w => [forall (v | ftrans w v) , evalb s v]
    | fAG s => AGb ftrans (evalb s) 
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
    - move => s IHs w.
      apply: (iffP agP); apply: AG_strengthen; intuition; solve [exact/IHs|exact/IHt].
  Qed.

  Lemma fin_modelP : ldec (@eval M).
  Proof. move => s w. case : (decP (evalP w s)); tauto. Qed.

End FiniteModels.

(** Every finite decidable model is a clasical model. Therefore, the
Hilberst system is sound for finite decidable models. *)

Definition cmodel_of_fmodel (M : fmodel) := CModel (@fin_modelP M).
Coercion cmodel_of_fmodel : fmodel >-> cmodel.

Theorem  finite_soundness s : prv s -> forall (M:fmodel) (w : M), eval s w.
Proof. move => H M w. exact: (@soundness _ H (cmodel_of_fmodel M) w). Qed.


(** * Clauses and Support *)

(** ** Signed Formulas

Our decision methods for CTL employ signed formulas. we also define a
number of inversion lemmas and other useful constructiuons *)

Definition sform  := (form * bool) %type.
Notation "s ^-" := (s,false) (at level 20, format "s ^-").
Notation "s ^+" := (s,true) (at level 20, format "s ^+").

Definition body s := match s with fAX t^+ => t^+ | fAX t^- => t^- | _ => s end.

Definition positive (s:sform) := if s is t^+ then true else false.
Definition positives C := [fset s.1 | s <- [fset t in C | positive t]].

Lemma posE C s : (s \in positives C) = (s^+ \in C).
Proof.
  apply/fimsetP/idP => [ [[t [|]]] | H].
  - by rewrite inE /= andbT => ? ->.
  - by rewrite inE /= andbF.
  - exists (s^+) => //. by rewrite inE.
Qed.

Definition negative (s:sform) := ~~ positive s.
Definition negatives C := [fset s.1 | s <- [fset t in C | negative t]].

Lemma negE C s : (s \in negatives C) = (s^- \in C).
Proof.
  apply/fimsetP/idP => [ [[t [|]]] | H].
  - by rewrite inE /= andbC.
  - by rewrite inE /negative  andbT => ? ->.
  - exists (s^-) => //. by rewrite inE.
Qed.

Definition isBox s := if s is fAX s^+ then true else false.

Inductive isBox_spec s : bool -> Type :=
| isBox_true t : s = fAX t^+ -> isBox_spec s true
| isBox_false  : isBox_spec s false.

Lemma isBoxP s : isBox_spec s (isBox s).
Proof. move: s => [ [|?|? ?|?|?] [|]] /=; try constructor. exact: isBox_true. Qed.

Definition isDia s := if s is fAX s^- then true else false.

Inductive isDia_spec s : bool -> Type :=
| isDia_true t : s = fAX t^- -> isDia_spec s true
| isDia_false  : isDia_spec s false.

Lemma isDiaP s : isDia_spec s (isDia s).
Proof. move: s => [ [|?|? ?|?|?] [|]] /=; try constructor. exact: isDia_true. Qed.

(** ** Clauses and Support *)

Definition clause := {fset sform}.

Definition lcons (L : clause) :=
  (fF^+ \notin L) && [all s in L, if s is fV p^+ then fV p^- \notin L else true].

Fixpoint literal (s : sform) :=
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
      | fAG s,true     => supp L s true && ((fAX (fAG s),true) \in L)
      | fAG s,false    => supp L s false || ((fAX (fAG s),false) \in L)
      | _,_ => (u,b) \in L
    end.

Notation "C |> s ^ b" := (supp C s b) (at level 30, format "C  |>  s ^ b").
Notation "C |> s ^+"  := (supp C s true) (at level 30, format "C  |>  s ^+").
Notation "C |> s ^-"  := (supp C s false) (at level 30, format "C  |>  s ^-").
Notation "C |> s"     := (supp C s.1 s.2) (at level 30).

(** Would like to use 
[Definition supp' L (s : sform) := let: (t,b) := s in supp L t b.]
[Notation "L |> t" := (supp' L t) (at level 30)]
However, simplification then breaks the notation *)

(** For a locally consistent clause [L], the collection of formulas
supported by [L] corresponds to an (infinite) Hintikka set. *)

Lemma supp_mon L1 L2 s : L1 `<=` L2 -> L1 |> s -> L2 |> s.
Proof.
  move/subP => sub. case: s.
  elim => //= [|p|s IHs t IHt|s IHs|s IHs] [|];
    solve [exact: sub| rewrite -?(rwP orP,rwP andP); intuition].
Qed.

Fixpoint f_weight (s : form) :=
  match s with
    | fImp s t => (f_weight s + f_weight t).+1
    | fAG s    => (f_weight s).+1
    | _        => 0
  end.

Lemma sweight_lit s : f_weight s.1 = 0 <-> literal s.
Proof. case: s => [[|p|s t|s|s] [|]] //. Qed.

Lemma supp_lit C s b : literal (s,b) -> supp C s b = ((s,b) \in C).
Proof. by case: s. Qed.

Definition form_slClass := SLClass supp_mon supp_lit sweight_lit.
Canonical Structure form_slType := SLType form_slClass.
Canonical Structure form_slpType := @SLPType prv_pSystem form_slClass.

(** Want suppC on singletons to expose the concrete support operation, not the
abstract one *)
Lemma suppC1 L s : suppC L [fset s] = L |> s.
Proof. exact: all_fset1. Qed.

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
Proof. case: s => [[|p|s t|s|s] [|]]; by rewrite /R sep1 /= ?fimset1 ?fimset0. Qed.

Lemma R0 : R fset0 = fset0.
Proof. by rewrite /R sep0 fimset0. Qed.

(** ** Subformula Closure *)

Fixpoint ssub' b s :=
  (s,b) |` match s with
             | fImp s t => ssub' (negb b) s `|` ssub' b t
             | fAX t => ssub' b t
             | fAG s => (fAX (fAG s),b) |` ssub' b s
             | _ => fset0
           end.

Lemma ssub'_refl s b : (s,b) \in ssub' b s.
Proof. case: s => [|x|s t|s|s] /=; by rewrite !inE. Qed.

Definition ssub (s : sform) := let (t,b) := s in (ssub' b t).

Lemma ssub_refl s : s \in ssub s.
Proof. case: s. exact: ssub'_refl. Qed.

Definition sf_closed' (F : {fset sform}) (s:sform) :=
  match s with
    | (fImp s t,b) => ((s,negb b) \in F) && ((t,b) \in F)
    | (fAX s, b) => (s,b) \in F
    | (fAG s, b) => [&& (fAX (fAG s),b) \in F & (s,b) \in F]
    | _ => true
  end.
Arguments sf_closed' F !s.

Definition sf_closed (F :{fset sform}) := forall s, s \in F -> sf_closed' F s.

Lemma sf_closed'_mon (X Y : clause) s : sf_closed' X s -> X `<=` Y -> sf_closed' Y s.
Proof.
  case: s. elim => [|x|s IHs t IHt|s IHs|s IHs ] b H /subP sub //=;
    rewrite ?sub //=; by [case/andP: H | case/and3P: H].
Qed.

Lemma sf_ssub F s : sf_closed F -> s \in F -> ssub s `<=` F. 
Proof.
  case: s. elim => [|p|s IHs t IHt|s IHs |s IHs] [|] sfc_F inF //=; 
   rewrite ?fsetU0 ?fsubUset ?fsub1 ?inF ?IHs ?IHt ?andbT //=;
   move: (sfc_F _ inF) => /=; try bcase.
Qed.

Lemma sfc_ssub s : sf_closed (ssub s).
Proof.
  case: s.
  elim => [|x|s IHs t IHt|s IHs|s IHs] b //= u; rewrite !inE ?orbF.
  - by move/eqP => -> /=.
  - by move/eqP => -> /=.
  - case/orP => [/eqP ->|H] /=. by rewrite !inE !ssub'_refl.
    apply: sf_closed'_mon (fsubUr _ _).
    case/orP: H => H. apply: sf_closed'_mon (fsubUl _ _). exact: IHs.
    apply: sf_closed'_mon (fsubUr _ _). exact: IHt.
  - case/orP => [/eqP ->|H] /=. by rewrite !inE !ssub'_refl.
    apply: sf_closed'_mon (fsubUr _ _). exact: IHs.
  - case/or3P => [/eqP ->| /eqP -> | H] /=; try by rewrite !inE ?ssub'_refl.
    do 2 apply: sf_closed'_mon (fsubUr _ _). exact: IHs.
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

Lemma RinU (F : clause) : sf_closed F -> 
  forall C, C \in powerset F -> R C \in powerset F.
Proof.
  move => sfc_F C. rewrite !powersetE => /subP H. apply/subP => s.
  case: s => s [|]; last by rewrite (negbTE (Rpos _ _)).
  by rewrite RE => /H /sfc_F.
Qed.

(** ** Associtated Formuals *)

Lemma satA (M:cmodel) (w:M) (C:clause) : 
  (forall s, s \in C -> eval (interp s) w) <-> eval [af C] w.
Proof.
  case: C => xs i /=.
  change ((forall s, s \in xs -> eval (interp s) w) <-> eval [af xs] w). 
  elim: xs {i} => [|/= s xs IH]. rewrite big_nil forall_nil /=. tauto.
  rewrite big_cons forall_cons IH {2}/And /=.
  move: (modelP (interp s) w) (modelP [af xs] w); tauto.
Qed.

Lemma box_request (C : clause) : prv ([af C] ---> AX [af R C]).
Proof.
  rewrite <- bigABBA. apply: bigAI. case => [s [|]]; last by rewrite (negbTE (Rpos _ _)).
  rewrite RE. exact: bigAE.
Qed.

Fixpoint f_size (s : form) := 
  match s with
    | fF => 1
    | fV p => 1
    | fImp s t => (f_size s + f_size t).+1
    | fAX s => (f_size s).+1
    | fAG s => (f_size s).+1
  end.

Require Import Lia.

Lemma size_ssub (s : form) (b : bool) : size (ssub (s,b)) <= 2 * f_size s.
Proof. 
  elim: s b => //= [|p|s IHs t IHt|s IHs|s IHs ] b; 
    try by rewrite fsetU0 fset1Es.
  - apply: leq_trans (fsizeU1 _ _) _. apply: leq_ltn_trans (fsizeU _ _) _.
    apply: leq_ltn_trans (leq_add (IHs _) (IHt _)) _.
    apply/leP; rewrite -!(multE,plusE); lia.
  - apply: leq_trans (fsizeU1 _ _) _. apply: leq_ltn_trans (IHs _) _.
    apply/leP; rewrite -!(multE,plusE); lia.
  - apply: leq_trans (fsizeU1 _ _) _. apply: leq_ltn_trans (fsizeU1 _ _) _.
    by rewrite mulnS add2n !ltnS.
Qed.
