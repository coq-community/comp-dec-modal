(* (c) Copyright Christian Doczkal and Joachim Bard                       *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations Lia Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs 
 Require Import edone bcase fset base modular_hilbert sltype rewrite_inequality fset_tac.

Set Default Proof Using "Type".

(* add this globally in fset.v ? *)
#[export] Hint Resolve subxx : core.

Lemma sizes1 (T : choiceType) (x : T) : size [fset x] = 1.
Proof. by rewrite fset1Es. Qed.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * PDL in Coq  *)

(** ** Formulas *)

Definition var := nat.
Definition pvar := nat.

Inductive prog :=
  pV    of pvar
| pCh   of prog & prog
| pSeq  of prog & prog
| pStar of prog
| pTest of form

with form :=
| fF
| fV   of var
| fImp of form & form
| fAX  of prog & form.

Notation "[ p ] s" := (fAX p s) (right associativity, at level 0, format "[ p ] s").
Notation "p ^*" := (pStar p) (at level 30, format "p ^*").
Notation "p0 ;; p1" := (pSeq p0 p1) (at level 45, right associativity, format "p0  ;;  p1").
Notation "p0 + p1" := (pCh p0 p1) (at level 50, left associativity, format "p0  +  p1").
Notation "a ??" := (pTest a) (at level 1,format "a ??").

Scheme form_mind := Induction for form Sort Prop 
with prog_mind := Induction for prog Sort Prop.

Combined Scheme form_prog_ind from form_mind,prog_mind.

Scheme form_mrect := Induction for form Sort Type 
with prog_mrect := Induction for prog Sort Type.

Combined Scheme form_prog_rect from form_mrect,prog_mrect.

Module Eq.
Fixpoint eqf (s t : form) :=
  match s, t with
  | fV p,fV q => p == q
  | fF,fF => true
  | fImp s1 t1,fImp s2 t2 => eqf s1 s2 && eqf t1 t2
  | [a]s, [b]t => eqp a b && eqf s t
  | _,_ => false
  end
with eqp (p q : prog) :=
  match p,q with
  | pV a,pV b => a == b
  | a1 ;; b1, a2 ;; b2 => eqp a1 a2 && eqp b1 b2
  | a1 + b1, a2 + b2 => eqp a1 a2 && eqp b1 b2
  | a^*,b^* => eqp a b 
  | s??,t?? => eqf s t
  | _,_ => false
  end.

Lemma form_prog_dec : 
  (forall s t, reflect (s = t) (eqf s t)) *
  (forall a b, reflect (a = b) (eqp a b)).
Proof with case => /=; try (constructor; discriminate).
  apply:form_prog_rect.
  - move... by constructor.
  - move => p... move => q. apply: (iffP eqP); congruence.
  - move => s IHs t IHt... move => s' t'.
    by apply: (iffP andP) => [[/IHs -> /IHt ->]|[/IHs ? /IHt ?]].
  - move => s IHs t IHt... move => s' t'.
    by apply: (iffP andP) => [[/IHs -> /IHt ->]|[/IHs ? /IHt ?]].
  - move => p... move => q. apply: (iffP eqP); congruence.
  - move => a IHa b IHb... move => a' b'.
    by apply: (iffP andP) => [[/IHa -> /IHb ->]|[/IHa ? /IHb ?]].
  - move => a IHa s IHs... move => a' s'.
    by apply: (iffP andP) => [[/IHa -> /IHs ->]|[/IHa ? /IHs ?]].
  - move => p IHp... move => q. apply: (iffP (IHp _)); congruence.
  - move => s IHs... move => t. apply: (iffP (IHs _)); congruence.
Qed.
End Eq.
    
Definition form_eqMixin := EqMixin (fst Eq.form_prog_dec).
Canonical Structure form_eqType := Eval hnf in @EqType form form_eqMixin.

Definition prog_eqMixin := EqMixin (snd Eq.form_prog_dec).
Canonical Structure prog_eqType := Eval hnf in @EqType prog prog_eqMixin.


(** To use formulas and other types built around formulas as base type
for the finite set libaray, we need to show that formulas are
countable. We do this by embedding formulas into the Ssreflect's
generic trees *)


Module formChoice.
  Import GenTree.

  Fixpoint picklef (s : form) :=
    match s with
      | fV v => Leaf v
      | fF => Node 0 [::]
      | fImp s t => Node 1 [:: picklef s ; picklef t]
      | fAX p s => Node 2 [:: picklep p ; picklef s]
    end
  with picklep (p : prog) :=
    match p with
    | pV v => Leaf v
    | pSeq p1 p2 => Node 0 [:: picklep p1 ; picklep p2]
    | pCh p1 p2 => Node 1 [:: picklep p1 ; picklep p2]
    | pStar p => Node 2 [:: picklep p]
    | pTest s => Node 3 [:: picklef s]
    end.

  Fixpoint unpicklef t :=
    match t with
      | Leaf v  => Some (fV v)
      | Node 0 [::]  => Some (fF)
      | Node 1 [:: t ; t' ] =>
          obind (fun s => obind (fun s' => Some (fImp s s')) (unpicklef t')) (unpicklef t)
      | Node 2 [:: p ; t ] =>
          obind (fun q => obind (fun s => Some (fAX q s)) (unpicklef t)) (unpicklep p)
      | _ => None
    end
  with unpicklep t :=
    match t with
    | Leaf v => Some (pV v)
    | Node 0 [:: t ; t'] =>
      obind (fun p => obind (fun p' => Some (pSeq p p')) (unpicklep t')) (unpicklep t)
    | Node 1 [:: t ; t'] =>
      obind (fun p => obind (fun p' => Some (pCh p p')) (unpicklep t')) (unpicklep t)
    | Node 2 [:: t] => obind (fun p => Some (pStar p)) (unpicklep t)
    | Node 3 [:: s] => obind (fun s => Some (pTest s)) (unpicklef s)
    | _ => None
    end.

  Lemma pickleP : (pcancel picklef unpicklef) /\ (pcancel picklep unpicklep).
  Proof.
    apply: form_prog_ind => //= *;
    by repeat match goal with [ H : _ = Some _ |- _] => rewrite ?H /= => {H} end. 
  Qed.

  Lemma picklefP : pcancel picklef unpicklef. 
  Proof. by apply pickleP. Qed.

End formChoice.

(** Note that we only need the [choiceType] and [countType] instances for formulas *)

Definition form_countMixin := PcanCountMixin formChoice.picklefP.
Definition form_choiceMixin := CountChoiceMixin form_countMixin.
Canonical Structure form_ChoiceType := Eval hnf in ChoiceType form form_choiceMixin.
Canonical Structure form_CountType := Eval hnf in CountType form form_countMixin.



(** ** Models

We distinguish three classes of models

- raw models or transition systems ([ts]): The inductive satisfaction relation
  [eval] is defined on this class

- finite models ([fmodel]): models where the type of states is finite and
  everything else is decidable

- classical models, i.e., models where [eval] is stable under double negation
  ([cmodel]): This is the largest class of models for which we can show
  soundness of the hilbert system. *)

Definition stable X Y (R : X -> Y -> Prop) := forall x y, ~ ~ R x y -> R x y.
Definition ldec X Y (R : X -> Y -> Prop) := forall x y, R x y \/ ~ R x y.

Record ts := TS {
  state  :> Type;
  trans  : var -> state -> state -> Prop;
  label  : var -> state -> Prop
}.
Prenex Implicits trans.

Record fmodel := FModel {
  fstate :> finType;
  ftrans : var -> rel fstate;
  flabel : var -> pred fstate
}.
Prenex Implicits ftrans.

(** Make ts inferable for states of fmodels *)
Canonical ts_of_fmodel (M : fmodel) : ts := TS (@ftrans M) (@flabel M).
Coercion ts_of_fmodel : fmodel >-> ts.


(** ** Satisfaction relation *)

Inductive star X (R: X -> X -> Prop) (x : X) : X -> Prop :=
| Star0 : star R x x
| StarL y z : R x z -> star R z y -> star R x y.

Section Eval.
Variables (M : ts).

Fixpoint eval (s: form) :=
  match s with
    | fF       => (fun _ => False)
    | fV x     => label x
    | fImp s t => (fun v => eval s v -> eval t v)
    | fAX p s  => (fun v => forall w, reach p v w -> eval s w)
  end
with reach (p: prog) : M -> M -> Prop :=
  match p with
  | pV a => trans a
  | pSeq p0 p1 => (fun v w => exists2 u, reach p0 v u & reach p1 u w)
  | pCh p0 p1 => (fun v w => reach p0 v w \/ reach p1 v w)
  | pStar p => star (reach p)
  | pTest s => fun v w => w = v /\ eval s v
  end.
End Eval.

Record cmodel := CModel { ts_of :> ts; modelP : stable (@eval ts_of) }.

(** Decidability of the satisfaction relation on finite models *)

Section Evalb.
Variables (M : fmodel).

Fixpoint evalb (s: form) :=
  match s with
    | fF       => xpred0
    | fV x     => flabel x
    | fImp s t => (fun v => evalb s v ==> evalb t v)
    | fAX p s  => (fun v => [forall (w | reachb p v w), evalb s w])
  end
with reachb (p: prog) : M -> M -> bool :=
  match p with
  | pV a => ftrans a
  | pSeq p0 p1 => (fun v w => [exists u, reachb p0 v u && reachb p1 u w])
  | pCh p0 p1 => (fun v w => reachb p0 v w || reachb p1 v w)
  | pStar p => connect (reachb p)
  | pTest s => fun v w => (w == v) && evalb s v
  end.
End Evalb.

Lemma eval_reachP (M : fmodel) : 
  ((forall s (w:M), reflect (eval s w) (evalb s w))*
   (forall p (w v : M), reflect (reach p w v) (reachb p w v)%type)).
Proof.
  apply: form_prog_rect => 
  [?|? ?|s IHs t IHt w|p IHp s IHs w|? ? ?|p IHp q IHq w v|p IHp q IHq w v||] /=.
  - by constructor.
  - exact: idP.
  - apply: (iffP implyP); rewrite -(rwP (IHs _)) -(rwP (IHt _)); tauto.
  - apply: (iffP forall_inP); move => H v /IHp ?; apply/IHs; by auto.
  - exact: idP.
  - apply: (iffP orP); rewrite -(rwP (IHp _ _)) -(rwP (IHq _ _)); tauto.
  - apply: (iffP exists_inP); move => [u ? ?]; exists u; by [apply/IHp|apply/IHq].
  - move => p IHp w v. apply: (iffP connectP) => [[ps]|].
    + elim: ps w v => //= [? ? _ -> |u us IH w v]; first by constructor.
      case/andP => /IHp A B ->. apply: StarL A _. exact: IH.
    + elim => {w v} => [w|w v u A _ [ps B C]]; first by exists [::].
      exists (u::ps) => //=. rewrite B andbT. exact/IHp.
  - move => s IHs w v. apply: (iffP andP); rewrite (rwP eqP) (rwP (IHs _)); tauto.
Qed.

Lemma evalP (M:fmodel) (w : M) s : reflect (eval s w) (evalb s w).
Proof. by apply eval_reachP. Qed.

Lemma fin_modelP (M:fmodel) : stable (@eval M).
Proof. move => s v. case: (decP (evalP v s)); tauto. Qed.

Definition cmodel_of_fmodel (M : fmodel) := CModel (@fin_modelP M).
Coercion cmodel_of_fmodel : fmodel >-> cmodel.

(** ** Axiomatization *)

Section Hilbert.
  Local Notation "s ---> t" := (fImp s t).

  Inductive prv : form -> Prop := 
  | rMP s t : prv (s ---> t) -> prv s -> prv t
  | axK s t : prv (s ---> t ---> s)
  | axS s t u : prv ((u ---> s ---> t) ---> (u ---> s) ---> u ---> t)
  | axDN' s : prv (((s ---> fF) ---> fF)  ---> s)

  | rNec p s : prv s -> prv ([p]s) 
  | axN p s t : prv ([p](s ---> t) ---> [p]s ---> [p]t)

  | axConE p0 p1 s: prv ([p0;;p1]s ---> [p0][p1]s)
  | axCon p0 p1 s: prv ([p0][p1]s ---> [p0;;p1]s)
  | axChEl p0 p1 s: prv ([p0 + p1]s ---> [p0]s)
  | axChEr p0 p1 s: prv ([p0 + p1]s ---> [p1]s) 
  | axCh p0 p1 s: prv ([p0]s ---> [p1]s ---> [p0 + p1]s)
  | axStarEl p s    : prv ([p^*]s ---> s)
  | axStarEr p s    : prv ([p^*]s ---> [p][p^*]s)
  | rStar_ind' p u : prv (u ---> [p]u) -> prv (u ---> [p^*]u)

  | axTestE s t      : prv ([s??]t ---> s ---> t)
  | axTestI s t      : prv ((s ---> t) ---> [s??]t)
  .

  Canonical Structure prv_mSystem := MSystem rMP axK axS.
  Canonical Structure prv_pSystem := PSystem axDN'.
End Hilbert.

  Lemma rNorm p s t : prv (s ---> t) -> prv ([p]s ---> [p]t).
  Proof. move => H. rule axN. exact: rNec. Qed.

  Instance AX_mor (p : prog) : Proper (@mImpPrv prv_mSystem ==> @mImpPrv prv_mSystem) (fAX p).
  Proof. exact: rNorm. Qed.

  Lemma rStar_ind p u s : prv (u ---> [p]u) -> prv (u ---> s) -> prv (u ---> [p^*]s).
  Proof. move/rStar_ind' => A B. by rewrite <- B. Qed.

  Lemma axStar p s : prv (s ---> [p][p^*]s ---> [p^*]s).
  Proof.
    apply: rAIL. apply: rStar_ind; last exact: axAEl.
    rule axAcase. drop. apply: rNorm. 
    ApplyH axAI; [exact: axStarEl |exact: axStarEr].
  Qed.

  Definition EX p s := (~~: [p] ~~: s).

  Lemma axnEXF p : prv (~~: EX p Bot).
  Proof. rewrite /EX. rewrite -> axDNE. apply: rNec. exact: axI. Qed.

  Lemma rEXn p s t : prv (s ---> t) -> prv (EX p s ---> EX p t).
  Proof. move => H. rule ax_contraNN. apply: rNorm. by rule ax_contraNN. Qed.

  Lemma axDBD p s t : prv (EX p s ---> [p]t ---> EX p (s :/\: t)).
  Proof.
    do 3 Intro. Apply* 2. do 2 Rev. rewrite <- axN. apply: rNorm.
    do 3 Intro. Apply* 1. ApplyH axAI.
  Qed.
  
  Lemma dmAX p s : prv (~~:[p]s <--> EX p (~~:s)).
  Proof. rewrite /EX. rewrite -> axDNE. exact: ax_eq_refl. Qed.

  Lemma axABBA p s t : prv ([p]s :/\: [p]t ---> [p](s :/\: t)).
  Proof.
    rule axAcase. rewrite <- axN, <- axN. apply: rNec. exact: axAI.
  Qed.
  
  Lemma bigABBA (T: eqType) (xs: seq T) (F: T -> form) p :
    prv ((\and_(s <- xs) [p](F s)) ---> [p](\and_(s <- xs) F s)).
  Proof.
    elim: xs => [|t xs IH].
    - drop. rewrite big_nil. apply: rNec. exact: axI.
    - rewrite !big_cons. rewrite -> IH, axABBA. exact: axI.
  Qed.

  Lemma axEOOE p s t : prv (EX p (s :\/: t) ---> EX p s :\/: EX p t).
  Proof.
    rewrite /EX. rewrite <- dmA. rewrite <- (ax_contraNN _ ([p]~~: (s:\/:t))).
    rewrite -> axABBA. apply: rNorm. rewrite <- dmO. exact: axI.
  Qed.

  Lemma bigEOOE (T: eqType) (xs: seq T) (F: T -> form) p :
    prv (EX p (\or_(s <- xs) F s) ---> \or_(s <- xs) EX p (F s)).
  Proof.
    elim: xs => [|t xs IH].
    - rewrite !big_nil. exact: axnEXF.
    - rewrite !big_cons. rewrite -> axEOOE, IH. exact: axI.
  Qed.

  (** ** Soundness *)

  Definition valid s := forall (M: cmodel) (v: M), eval s v.


  (* Theorem 2.2 (Soundness) - both directions as individual lemmas *)
  Lemma soundness s: prv s -> valid s.
  Proof.
    elim  => {s}; try by move => *; firstorder.
    - move => s t _ A _ B M w. apply: A. exact: B.
    - move => s M v /=. exact: modelP. 
    - move => p s M v /=. apply. by constructor.
    - move => p s M v H u vRu w uRw /=. apply: H. exact: StarL.
    - move => p u _ IHu M v H w /= vRw.
      elim: vRw H => // {v w} - v w ? vRu _ IH H. apply: IH. exact: IHu.
    - by move => s t M v /= A w [->]. 
  Qed.

  Lemma soundness_classical (M:ts) :
    (forall s, prv s -> forall (w : M), eval s w) -> stable (@eval M).
  Proof. move => H s w. exact: (H _ (axDN s)). Qed.

  Corollary classical_soundness (dn: forall P , ~ ~ P -> P) s: 
    prv s -> forall (M: ts) (v: M), eval s v.
  Proof.
    move => H M v. 
    have stable_ts: stable (@eval M). move => t w. exact: dn.
    exact: (@soundness _ H (CModel stable_ts)).
  Qed.

  (** ** Segerberg formulation *)
  
  (** The essential difference between Segerberg's axiomatization and 
      ours is that the former uses an axiom rather than a rule for in induction. *)


  Module SEG.
  Section Hilbert.
  Local Notation "s ---> t" := (fImp s t).

  Inductive prv : form -> Prop := 
  | rMP s t : prv (s ---> t) -> prv s -> prv t
  | axK s t : prv (s ---> t ---> s)
  | axS s t u : prv ((u ---> s ---> t) ---> (u ---> s) ---> u ---> t)
  | axDN' s : prv (((s ---> fF) ---> fF)  ---> s)

  | rNec p s : prv s -> prv ([p]s) 
  | axN p s t : prv ([p](s ---> t) ---> [p]s ---> [p]t)

  | axConE p0 p1 s: prv ([p0;;p1]s ---> [p0][p1]s)
  | axCon p0 p1 s: prv ([p0][p1]s ---> [p0;;p1]s)
  | axChEl p0 p1 s: prv ([p0 + p1]s ---> [p0]s)
  | axChEr p0 p1 s: prv ([p0 + p1]s ---> [p1]s) 
  | axCh p0 p1 s: prv ([p0]s ---> [p1]s ---> [p0 + p1]s)
  | axStarEl p s    : prv ([p^*]s ---> s)
  | axStarEr p s    : prv ([p^*]s ---> [p][p^*]s)
  | axStarI p s    : prv (s ---> [p][p^*]s ---> [p^*]s)
  | axSeg p s : prv ([p^*](s ---> [p]s) ---> s ---> [p^*]s)

  | axTestE s t      : prv ([s??]t ---> s ---> t)
  | axTestI s t      : prv ((s ---> t) ---> [s??]t)
  .

  End Hilbert.
  End SEG.

  (** The only nontrivial part in showing the equivalence of the two
      axiom system is to show that the induction rule (which requires
      [s ---> [p]s to be a theorem,i.e., hold everywhere) implies the
      axiom (which only requires [s ---> [p]s] to hold at reachable states *)

  Lemma segerberg p s : prv ([p^*](s ---> [p]s) ---> s ---> [p^*]s).
  Proof.
    pose u := [p^*](s ---> [p]s) :/\: s.
    suff S : prv (u ---> [p]u). 
    { apply: rAIL. rewrite -/u. apply: rStar_ind S _. exact: axAEr. }
    rewrite /u. 
    rule axAcase. do 2 Intro. ApplyH axABBA. ApplyH axAI. 
    - Rev* 1. drop. by rewrite -> (axStarEr p (s ---> [p]s)) at 1.
    - Rev. Rev. by rewrite -> (axStarEl p (s ---> [p]s)) at 1.
  Qed.

  Fact segerberg_vs_inductive s : SEG.prv s <-> prv s.
  Proof. 
    split.
    - elim; solve [by constructor| eauto using rMP,segerberg,axStar]. 
    - elim; try solve [by constructor| eauto using SEG.rMP]. 
      move => p u _ /SEG.rNec IH. apply: SEG.rMP (IH (p^*)). by constructor.
  Qed.
    

(** * Subformula Universes *)

(** ** Fischer Ladner Closure *)

Fixpoint FL (s : form) {struct s} : {fset form} :=
  match s with
  | fV p => [fset fV p]
  | fF => [fset fF]
  | fImp s t => fImp s t |` FL s `|` FL t
  | [a]s => FL0 a s `|` FL s
  end
with FL0 (a : prog) (s : form) {struct a} : {fset form} :=
  match a with 
  | a + b => [a + b]s |` FL0 a s `|` FL0 b s
  | a ;; b => [a ;; b]s |` FL0 a [b]s `|` FL0 b s
  | t?? => [t??]s |` FL t
  | a^* =>[a^*]s |` FL0 a [a^*]s
  | pV a => [fset [pV a]s]
  end.

(* Lemma 3.3 *)
Lemma FL_refl s : s \in FL s.
Proof. case: s => [|||[]] /=; by fset_nocut. Qed.

Lemma FL0_refl p s : [p]s \in FL0 p s.
Proof. case: p => /= *; by fset_nocut. Qed.

Lemma FL_trans_mut : 
  (forall s t : form, t \in FL s -> FL t `<=` FL s) * 
  (forall a (s t : form), t \in FL0 a s -> FL t `<=` FL0 a s `|` FL s).
Proof.
  apply: form_prog_ind => /=.
  - fset_nocut.
  - fset_nocut.
  - move => s IHs t IHt u. rewrite !inE -orbA.
    case/or3P => [/eqP -> {t} //|/IHs|/IHt]; fset_nocut.
  - move => a IHa s IHs t /fsetUP [A|A].
    + exact: IHa.
    + exact: sub_trans (IHs t A) _. 
  - move => a s t. by rewrite inE => /eqP ->. 
  - move => a IHa b IHb s t. rewrite !inE -orbA.
    case/or3P => [/eqP -> {t} //|A|A].
    + move: (IHa _ _ A); fset_nocut.
    + move: (IHb _ _ A); fset_nocut.
  - move => a IHa b IHb s t. rewrite !inE -orbA.
    case/or3P => [/eqP -> {t} //|A|A].
    + move: (IHa _ _ A); fset_nocut.
    + move: (IHb _ _ A); fset_nocut.
  - move => p IHp s t. case/fsetU1P => [ -> // |A]. 
    move: (IHp _ _ A); fset_nocut.
  - move => u IHu s t /fsetU1P [-> // |A].
    move: (IHu _ A); fset_nocut.
Qed.

Lemma FL_trans s t u : t \in FL s -> s \in FL u -> t \in FL u.
Proof. move => A B. move: A. apply/subP. exact: FL_trans_mut.1. Qed.

Definition sf_closed' (F : {fset form}) s :=
  match s with
    | fImp s t => (s \in F) && (t \in F)
    | [pV _]s => s \in F
    | [p0;;p1]s => [&& [p0][p1]s \in F, [p1]s \in F & s \in F]
    | [p0 + p1]s => [&& [p0]s \in F, [p1]s \in F & s \in F]
    | [p^*]s => ([p][p^*]s \in F) && (s \in F)
    | [s??]t => (s \in F) && (t \in F)
    | _ => true
  end.

Arguments sf_closed' F !s.

Definition sf_closed (F :{fset form}) := forall s, s \in F -> sf_closed' F s.

(* Lemma 3.4 *)
Lemma FL_closed u : sf_closed (FL u).
Proof.
  case => //.
  - move => s t A /=. apply/andP;split; apply: FL_trans A; by rewrite !inE FL_refl.
  - case => //= [p s|p1 p2 s|p1 p2 s|p s|s t] A; repeat (apply/andP;split);
      by [apply: FL_trans A; rewrite !inE ?FL_refl ?FL0_refl ].
Qed.

Fixpoint sizef (s : form) :=
  match s with
  | fV p => 1
  | fF => 1
  | fImp s t => (1 + sizef s + sizef t)%N
  | [a]s => (1 + sizep a + sizef s)%N
  end
with sizep (a : prog) :=
  match a with 
  | pV a => 1
  | a + b => (1 + sizep a + sizep b)%N
  | a ;; b => (1 + sizep a + sizep b)%N
  | a^* => (sizep a + 1)%N
  | t?? => (1 + sizef t)%N
  end.

(** Wrapper for [lia] that uses ssreflects operators on [nat] *)

Ltac norm := rewrite ?sizes1;simpl in *.
Ltac normH := match goal with [ H : is_true (_ <= _) |- _] => move/leP : H end.
Ltac ssrlia := try
                 (try (apply/andP; split); (* handle a <= b <= c *)
                  apply/leP; (* convert claim *)
                  repeat normH; (* convert assuptions *)
                  norm ; (* simplify *)
                  rewrite ?addnE /addn_rec ; (* replace addn with plus *)
                  intros; (* revert converted assumptions *)
                  lia).

(** Make arguments implicit for easier passing to leqRW *)
Arguments fsizeU {T X Y}.

(* Lemma 3.5 *)
Lemma FL_size : 
  (forall s : form, size (FL s) <= sizef s) * 
  (forall a s, size (FL0 a s) <= sizep a).
Proof.
  apply: form_prog_ind => /=; try solve [move => *;ssrlia]. 
  - move => s IHs t IHt. rewrite !(leqRW fsizeU). by ssrlia.
  - move => p IHp s IHs. rewrite (leqRW fsizeU) (leqRW IHs) (leqRW (IHp _)). by ssrlia.
  - move => a IHa b IHb s. rewrite !(leqRW fsizeU) (leqRW (IHa _)) (leqRW (IHb _)). by ssrlia.
  - move => a IHa b IHb s. rewrite !(leqRW fsizeU) (leqRW (IHa _)) (leqRW (IHb _)). by ssrlia.
  - move => p IHp s. apply: leq_trans (fsizeU1 _ _) _. by rewrite !addn1 ltnS. 
  - move => s IHs t. rewrite !(leqRW fsizeU) (leqRW IHs). by ssrlia.
Qed.

(** ** Signed Formulas *)

Definition sform  := (form * bool) %type.
Notation "s ^-" := (s, false) (at level 20, format "s ^-").
Notation "s ^+" := (s, true) (at level 20, format "s ^+").

Definition body s :=
  match s with [_]t^+ => t^+ | [_]t^- => t^- | _ => s end.

Definition isBox (a: var) s :=
  match s with [pV b]t^+ => a == b | _ => false end.

Inductive isBox_spec a s : bool -> Type :=
| isBox_true t : s = [pV a]t^+ -> isBox_spec a s true
| isBox_false  : isBox_spec a s false.

Lemma isBoxP a s : isBox_spec a s (isBox a s).
Proof.
  move: s => [ [|?|? ?|[b|? ?|? ?|?|?] ?] [|]] /=; try constructor.
  case H: (a == b); try constructor.
  rewrite (eqP H). by exact: isBox_true.
Qed.

(** ** Subformula Universes *)

Definition clause := {fset sform}.

Definition flipcl F : clause := \bigcup_(s in F) [fset s^+; s^-].

Lemma flipcl_refl F s : s \in F -> forall b, (s, b) \in flipcl F.
Proof. move => inF [|]; apply/cupP; exists s; by rewrite inF /= !inE. Qed.

Definition drop_sign (s: sform) := match s with (t, _) => t end.

Lemma flip_drop_sign F s : s \in flipcl F -> drop_sign s \in F.
Proof. case/cupP => t. case/and3P => inF _. rewrite !inE. case/orP; by move/eqP => ->. Qed.

Definition flip (s : sform) := match s with t^+ => t^- | t^- => t^+ end.

Definition flip_closed (C: clause) := forall s, s \in C -> (flip s) \in C.

Lemma closed_flipcl F : flip_closed (flipcl F).
Proof.
  move => s /cupP [t] /and3P [inF _ H]. apply/cupP. exists t. move: H.
  rewrite inF /= !inE. case/orP => /eqP -> /=; by rewrite eqxx.
Qed.

(* simplify? *)
Lemma size_flipcl F : size (flipcl F) <= 2 * size F.
Proof.
  rewrite /flipcl. elim (elements F) => [|s xs IH] /=.
  - rewrite big_nil sizes0. done.
  - rewrite big_cons. apply: leq_trans; first exact: fsizeU.
    rewrite mulnS. apply: leq_add; last exact: IH.
    apply: leq_trans; first exact: fsizeU1.
    by rewrite fset1Es.
Qed.

(** ** Hintikka Sets *)

Definition lcons (L : clause) :=
  (fF^+ \notin L) && [all s in L, flip s \notin L].

Section Hintikka.
  Variable (F: {fset form}).
  Hypothesis (sfc_F: sf_closed F).

  Definition maximal (C: clause) := [all s in F, (s^+ \in C) || (s^- \in C)].

  Definition hintikka' s (L: clause) :=
  match s with
  | fImp s t^+ => (s^- \in L) || (t^+ \in L)
  | fImp s t^- => (s^+ \in L) && (t^- \in L)
  | ([p0;;p1]s, b) => ([p0][p1]s, b) \in L
  | [p0 + p1]s^+ => ([p0]s^+ \in L) && ([p1]s^+ \in L)
  | [p0 + p1]s^- => ([p0]s^- \in L) || ([p1]s^- \in L)
  | [p^*]s^+ => (s^+ \in L) && ([p][p^*]s^+ \in L)
  | [p^*]s^- => (s^- \in L) || ([p][p^*]s^- \in L)
  | [s??]t^+ => (s^- \in L) || (t^+ \in L)
  | [s??]t^- => (s^+ \in L) && (t^- \in L)
  | _ => true
  end.

  Definition hintikka L := lcons L && [all s in L, hintikka' s L].

  Variable (C: clause).
  Hypothesis (hint_C: hintikka C).
  Local Set Default Proof Using "hint_C".

  Lemma hint_imp_pos s t : fImp s t^+ \in C -> s^- \in C \/ t^+ \in C.
  Proof. case/andP: hint_C => _ /allP H inC. move: (H _ inC). case/orP; by auto. Qed.

  Lemma hint_imp_neg s t : fImp s t^- \in C -> s^+ \in C /\ t^- \in C.
  Proof. case/andP: hint_C => _ /allP H inC. move: (H _ inC). by case/andP. Qed.

  Lemma hint_box_con p0 p1 s b : ([p0;;p1]s, b) \in C -> ([p0][p1]s, b) \in C.
  Proof. case/andP: hint_C => _ /allP H inC. by move: (H _ inC). Qed.

  Lemma hint_box_ch p0 p1 s : [p0 + p1]s^+ \in C -> [p0]s^+ \in C /\ [p1]s^+ \in C.
  Proof. case/andP: hint_C => _ /allP H inC. move: (H _ inC). by case/andP. Qed.

  Lemma hint_dia_ch p0 p1 s : [p0 + p1]s^- \in C -> [p0]s^- \in C \/ [p1]s^- \in C.
  Proof. case/andP: hint_C => _ /allP H inC. move: (H _ inC). case/orP; by auto. Qed.

  Lemma hint_box_star p s : [p^*]s^+ \in C -> s^+ \in C /\ [p][p^*]s^+ \in C.
  Proof. case/andP: hint_C => _ /allP H inC. move: (H _ inC). by case/andP. Qed.

  Lemma hint_dia_star p s : [p^*]s^- \in C -> s^- \in C \/ [p][p^*]s^- \in C.
  Proof. case/andP: hint_C => _ /allP H inC. move: (H _ inC). case/orP; by auto. Qed.

End Hintikka.


(** ** Request *)

Definition R a C := [fset body s | s <- [fset t in C | isBox a t]].

Lemma RE C a s : (s^+ \in R a C) = ([pV a]s^+ \in C).
Proof.
  apply/fimsetP/idP => [ [t] | H].
  - rewrite inE andbC. by case: (isBoxP a t) => //= t' -> /= ? [->].
  - exists ([pV a]s^+) => //. by rewrite inE H /=.
Qed.

Lemma Rpos a s C : s^- \notin R a C.
Proof.
  apply/negP. case/fimsetP => t. rewrite inE andbC.
    by case (isBoxP a t) => // t' ->.
Qed.

Lemma RU a (C C' : clause) : R a (C `|` C') = (R a C `|` R a C').
Proof. by rewrite /R sepU fimsetU. Qed.

Lemma R1 a (s : sform) :
  R a [fset s] = if s is [pV b]u^+ then if (a == b) then [fset u^+] else fset0 else fset0.
Proof.
  case: s => [[|x|s t|[b|p0 p1|p0 p1|p|t] s] [|]]; rewrite /R sep1 /= ?fimset1 ?fimset0 //.
  case: (a == b); by rewrite ?fimset1 ?fimset0.
Qed.

Lemma R0 a : R a fset0 = fset0.
Proof. by rewrite /R sep0 fimset0. Qed.


Lemma RinU F a : sf_closed F -> 
  forall C, C \in powerset (flipcl F) -> R a C \in powerset (flipcl F).
Proof.
  move => sfc_F C. rewrite !powersetE => /subP H. apply/subP => s.
  case: s => s [|]; last by rewrite (negbTE (Rpos _ _ _)).
  rewrite RE /flipcl => /H /flip_drop_sign /= inF. apply/cupP. exists s. rewrite !inE /= andbT.
  exact: (sfc_F [pV a]s).
Qed.

(** ** Associated Formuals *)

Definition interp (s:sform) := match s with (s, true) => s | (s, false) => Neg s end.

Notation "[ 'af' C ]" := (\and_(s <- C) interp s) (at level 0, format "[ 'af'  C ]").

Lemma box_request (C: clause) a : prv ([af C] ---> [pV a][af R a C]).
Proof.
  rewrite <- bigABBA. apply: bigAI. case => [s [|]]; last by rewrite (negbTE (Rpos _ _ _)).
  rewrite RE. exact: bigAE.
Qed.
