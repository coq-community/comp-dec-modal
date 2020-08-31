(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * CTL in Coq

We define two semantics for CTL, the usual semantics in terms of infinite paths
and another semantics using induction and coinduction.  While we only need AX,
AU, and AR to define the evaluation function, we also define the duals. These
are used mainly when constructing models. *)

Notation "P =p Q" := (forall x, P x <-> Q x) (at level 40).
Definition PredC X (p : X -> Prop) x := ~ p x.

Section Characterizations.
  (** ** Inductive Characterizations *)

  Variables (X : Type) (e : X -> X -> Prop).

  Definition cEX (p : X -> Prop) (w : X) : Prop := exists2 v, e w v & p v.
  Definition cAX (p : X -> Prop) (w : X) : Prop := forall v, e w v -> p v.

  CoInductive cAR (p q : X -> Prop) (w : X) : Prop :=
  | AR0 : p w -> q w -> cAR p q w
  | ARs : q w -> (forall v, e w v -> cAR p q v) -> cAR p q w.

  Inductive cAU (p q : X -> Prop) (w : X) : Prop :=
  | AU0 : q w -> cAU p q w
  | AUs : p w -> (forall v, e w v -> cAU p q v) -> cAU p q w.

  CoInductive cER (p q : X -> Prop) (w : X) : Prop :=
  | ER0 : p w -> q w -> cER p q w
  | ERs v : q w -> e w v -> cER p q v -> cER p q w.

  Inductive cEU (p q : X -> Prop) (w : X) : Prop :=
  | EU0 : q w -> cEU p q w
  | EUs v : p w -> e w v -> cEU p q v -> cEU p q w.

  Lemma cAU_cER (p q : X -> Prop) (w : X) :
    cER (PredC p) (PredC q) w -> ~ cAU p q w.
  Proof.
    move => E A. elim: A E => {w}[w qw|w]; first by case.
    move => pw _ IH. case => // v _. exact: IH.
  Qed.

  Lemma cAR_cEU (p q : X -> Prop) (w : X) :
    cEU (PredC p) (PredC q) w -> ~ cAR p q w.
  Proof.
    move => E A. elim: E A => {w} [w ?|w v]; first by case.
    move => pw wv _ IH. case => // qw /(_ _ wv). exact: IH.
  Qed.

  Lemma AU_strengthen (p1 q1 p2 q2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
    cAU p1 q1 w -> cAU p2 q2 w.
  Proof.
    move => H1 H2. elim => {w} - w; first by move => ?; apply AU0; auto.
    move => /H1 ? _ IH. apply: AUs ; auto.
  Qed.

  Lemma AR_strengthen (p1 q1 p2 q2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
    cAR p1 q1 w -> cAR p2 q2 w.
  Proof.
    move => H1 H2. move: w. cofix AR_strengthen => w.
    case => [ /H1 ? /H2 ?|/H2 ? N]; first exact: AR0.
    apply: ARs => // v wv. apply: AR_strengthen. exact: N.
  Qed.

  Lemma ER_strengthen (p1 q1 p2 q2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
    cER p1 q1 w -> cER p2 q2 w.
  Proof.
    move => Hp Hq. move: w. cofix ER_strengthen => w. 
    case => [/Hp ? /Hq ?|v V1 V2 V3]; first exact: ER0.
    by apply: ERs _ V2 _ ; auto.
  Qed.

  Lemma EU_strengthen (p1 q1 p2 q2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
    cEU p1 q1 w -> cEU p2 q2 w.
  Proof.
    move => H1 H2. elim => {w} - w; first by move => ?; apply EU0; auto.
    move => v /H1 wv ? IH. apply: EUs ; auto.
  Qed.

  Lemma cAU_eq (x y : X) (p q : pred X) :
    p x = p y -> q x = q y -> e x =p e y -> cAU p q x -> cAU p q y.
  Proof.
    move => Hp Hq Ht. case => [?|px Hs]; first by apply: AU0; congruence.
    apply: AUs => //. congruence. move => v /Ht. exact: Hs.
  Qed.

  Lemma cEU_eq (x y : X) (p q : pred X) :
     p x = p y -> q x = q y -> e x =p e y -> cEU p q x -> cEU p q y.
  Proof.
    move => Hp Hq Ht. case => [?|z xz Hs]; first by apply: EU0; congruence.
    apply: EUs => //. congruence. exact/Ht.
  Qed.

  (** ** Path Characterizations *)

  Implicit Type (pi : nat -> X).
  Definition path pi := forall n, e (pi n) (pi n.+1).

  Definition pcons x pi k := if k is k.+1 then pi k else x.
  Definition ptail pi k := pi k.+1.
  
  Lemma path_pcons x pi : e x (pi 0) -> path pi -> path (pcons x pi). 
  Proof. move => H1 H2 [|k] //. exact: H2. Qed.

  Lemma path_ptail pi : path pi -> path (ptail pi).
  Proof. move => H n. exact: H. Qed.

  Definition p_until (p q : X -> Prop) pi := 
    exists2 n, forall m, m < n -> p (pi m) & q (pi n).

  Definition p_release (p q : X -> Prop) pi := 
    forall n, (exists2 m, m < n & p (pi m)) \/ q (pi n).

  Definition pAU (p q : X -> Prop) (w : X) : Prop := 
    forall pi, path pi -> pi 0 = w -> p_until p q pi.

  Definition pAR (p q : X -> Prop) (w : X) : Prop := 
    forall pi, path pi -> pi 0 = w -> p_release p q pi.

  Definition pEU (p q : X -> Prop) (w : X) : Prop := 
    exists pi, [/\ path pi, pi 0 = w & p_until p q pi].

  Definition pER (p q : X -> Prop) (w : X) : Prop := 
    exists pi, [/\ path pi, pi 0 = w & p_release p q pi].

  Lemma pAU_pER (p q : X -> Prop) (w : X) :
    pER (PredC p) (PredC q) w -> ~ pAU p q w.
  Proof. 
    case => pi [pi1 pi2 pi3]. move/(_ pi pi1 pi2).
    case => n n1 n2. case/(_ n): pi3; last by apply.
    case => m m1 m2. apply: m2. exact: n1.
  Qed.

  Lemma pAR_pEU (p q : X -> Prop) (w : X) :
    pEU (PredC p) (PredC q) w -> ~ pAR p q w.
  Proof.
    case => pi [pi1 pi2 pi3]. move/(_ pi pi1 pi2) => pi4.
    case: pi3 => n n1 n2. case: (pi4 n) => [[m m1 m2]|]. 
    - exact: n1 (m) _ _.
    - exact: n2.
  Qed.

  Lemma pAR_strengthen (p1 q1 p2 q2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
    pAR p1 q1 w -> pAR p2 q2 w.
  Proof. 
    move => Hp Hq H pi pi1 pi2 n. move: (H pi pi1 pi2 n).
    by case; [left|right]; firstorder.
  Qed.

  Lemma pAU_strengthen (p1 q1 p2 q2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
    pAU p1 q1 w -> pAU p2 q2 w.
  Proof. 
    move => Hp Hq H pi pi1 pi2. move: (H pi pi1 pi2).
    case => n n1 n2. by exists n; firstorder.
  Qed.

  Lemma pER_strengthen (p1 q1 p2 q2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
    pER p1 q1 w -> pER p2 q2 w.
  Proof. 
    move => Hp Hq [pi [? ? Hpi]]. exists pi. split => // n.
    by case: (Hpi n); firstorder.
  Qed.

  Lemma pEU_strengthen (p1 q1 p2 q2 : X -> Prop) w :
    (forall v, p1 v -> p2 v) -> (forall v, q1 v -> q2 v) ->
    pEU p1 q1 w -> pEU p2 q2 w.
  Proof.
    move => Hp Hq [pi [? ? Hpi]]. exists pi. split => //.
    case: Hpi => n n1 n2. exists n; firstorder.
  Qed.

End Characterizations.

(** Dependent Choice *)
Definition DC_ (X : Type) := forall R : X -> X -> Prop, 
    (forall x, exists y, R x y) -> forall x, exists2 f, f 0 = x & path R f.
Definition DC := forall X, DC_ X.


(** ** Formulas *)

Definition var := nat.

Inductive form :=
| fF
| fV   of var
| fImp of form & form
| fAX  of form
| fAR  of form & form
| fAU  of form & form.

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
      | fAU s t => Node 3 [:: pickle s; pickle t]
      | fAR s t => Node 4 [:: pickle s; pickle t]
    end.

  Fixpoint unpickle t :=
    match t with
      | Leaf v  => Some (fV v)
      | Node 0 [::]  => Some (fF)
      | Node 1 [:: t ; t' ] =>
          obind (fun s => obind (fun s' => Some (fImp s s')) (unpickle t')) (unpickle t)
      | Node 2 [:: t ] => obind (fun s => Some (fAX s)) (unpickle t)
      | Node 3 [:: t ; t' ] =>
        obind (fun s => obind (fun s' => Some (fAU s s')) (unpickle t')) (unpickle t)
      | Node 4 [:: t ; t' ] =>
        obind (fun s => obind (fun s' => Some (fAR s s')) (unpickle t')) (unpickle t)
      | _ => None
    end.

  Lemma pickleP : pcancel pickle unpickle.
  Proof. move => s. by elim: s => //= [s -> t ->| s -> | s -> t -> | s -> t -> ]. Qed.
End formChoice.

Definition form_countMixin := PcanCountMixin formChoice.pickleP.
Definition form_choiceMixin := CountChoiceMixin form_countMixin.
Canonical Structure form_ChoiceType := Eval hnf in ChoiceType form form_choiceMixin.
Canonical Structure form_CountType := Eval hnf in CountType form form_countMixin.

(** ** Models

We distinguish thee classes of models

- raw models or or serial transition systems ([sts]): Both, the satisfaction
  relation for the path semantics [satisfies] and the inductive satisfaction
  relation [eval] are refined on this class

- finite models ([fmodel]): models where the type of states is finite and
  everything else is decidable

- classical models ([cmodel]): models [eval] is logically decidable. This is the
  largest class of models for which we can show soundness of the hilbert system.


Unlike for K and Kstar, where stability under double negation would be enough to
prove soundness of the Hilbert system, for CTL we have to require of classical
models that the evaluation relation is not only stable under double negation
but in fact logically decidable. The reason for this is the coinductive modality
AR. Using stability for classical reasoing would violate the guard condition for
coinductive proofs. *)

Definition stable X Y (R : X -> Y -> Prop) := forall x y, ~ ~ R x y -> R x y.
Definition ldec X Y (R : X -> Y -> Prop) := forall x y, R x y \/ ~ R x y.

Record sts := STS {
  state  :> Type;
  trans  : state -> state -> Prop;
  label  : var -> state -> Prop;
  serial : forall w:state, exists v, trans w v
}.
Prenex Implicits trans.

Record fmodel := FModel {
  fstate :> finType;
  ftrans : rel fstate;
  flabel : var -> pred fstate;
  fser w : exists v, ftrans w v
}.
Prenex Implicits ftrans.

Canonical sts_of_fmodel (M : fmodel) : sts := STS (@flabel M) (@fser M).
Coercion sts_of_fmodel : fmodel >-> sts.

(** ** Satisfaction for inductuvice and path semantics *)

Fixpoint satisfies (M : sts) (s : form) := 
  match s with
    | fF       => (fun _ => False)
    | fV v     => label v
    | fImp s t => (fun w => satisfies M s w -> satisfies M t w)
    | fAX s    => cAX (@trans M) (satisfies M s)
    | fAR s t  => pAR trans (satisfies M s) (satisfies M t)
    | fAU s t  => pAU trans (satisfies M s) (satisfies M t)
    end.  

Fixpoint eval (M:sts) (s : form) :=
  match s with
    | fF       => (fun _ => False)
    | fV v     => label v
    | fImp s t => (fun w => eval M s w -> eval M t w)
    | fAX s    => cAX (@trans M) (eval M s)
    | fAR s t  => cAR trans (eval M s) (eval M t)
    | fAU s t  => cAU trans (eval M s) (eval M t)
    end.

Record cmodel := CModel { sts_of :> sts; modelP : ldec (@eval sts_of) }.


(** ** Finite Models 

A model is finite, if the underlying type of states is a finite type.  We that
[eval] is decidable on finite models. For this we need to evaluate the
eventualities. This requires boolean reflections of AU and AR which we obtain
using fixpoint computations. *)

Section Decidability.
  Variables (T: finType) (e : rel T) (p q : pred T).

  Definition AU_fun (X : {set T}) :=
    [set x | q x] :|: [set x | p x && [forall (y | e x y), y \in X]].

  Lemma AU_mono : mono AU_fun.
  Proof.
    move => X Y S. apply: setUS. apply/subsetP => x; rewrite !inE.
    case (p x) => //= ?. apply/forall_inP => y xy. apply: (subsetP S). by apply/forall_inP : y xy.
  Qed.

  Definition AUb w := w \in lfp AU_fun.

  Lemma auP w : reflect (cAU e p q w) (AUb w).
  Proof.
    rewrite /AUb; apply: (iffP idP).
    - move: w. pattern (lfp AU_fun). apply: lfp_ind; first by move => ?; rewrite inE.
      move => X IH w. case/setUP; rewrite !inE; first by move => ?; exact: AU0.
      case/andP => ? A. apply: AUs => // v wv. apply: IH. exact: (forall_inP A).
    - rewrite (lfpE AU_mono). elim => {w} - w; first by rewrite !inE => ->.
      move => pw _ /forall_inP IH. by rewrite !inE (lfpE AU_mono) pw IH /=.
   Qed.

  Definition AR_fun (X : {set T}) :=
    [set x | p x && q x ] :|: [set x | q x && [forall (y | e x y), y \in X]].

  Lemma AR_mono : mono AR_fun.
  Proof.
    move => X Y S. apply: setUS. apply/subsetP => x; rewrite !inE.
    case (q x) => //= ?. apply/forall_inP => y xy. apply: (subsetP S). by apply/forall_inP : y xy.
  Qed.

  Definition ARb w := w \in gfp AR_fun.

  Lemma arP w : reflect (cAR e p q w) (ARb w).
  Proof.
    rewrite /ARb; apply (iffP idP).
    - move: w. cofix arP => w. rewrite (gfpE AR_mono) !inE. 
      case/orP => /andP [x1 x2]; first exact: AR0. 
      apply: ARs => // v wv. apply: arP. exact: (forall_inP x2). 
    - apply: gfp_ind2 => {w} - w X CH. case; first by rewrite !inE; bcase.
      move => qw H. rewrite inE; rightb; rewrite inE qw /=.
      apply/forall_inP => v /H. exact: CH.
  Qed.
                                
End Decidability.

Arguments auP {T e p q w}.
Arguments arP {T e p q w}.

(** Given decidability for AU and AR, decidability of [eval] follows using a
simple induction on formulas *)

Section FiniteModels.
  Variables (M : fmodel).

  Fixpoint evalb s : pred M :=
    match s with
    | fV p => flabel p
    | fF => xpred0
    | fImp s t => fun w => evalb s w ==> evalb t w
    | fAX s => fun w => [forall (v | ftrans w v) , evalb s v]
    | fAU s t => AUb ftrans (evalb s) (evalb t)
    | fAR s t => ARb ftrans (evalb s) (evalb t)
  end.

  Lemma evalP (w:M) s : reflect (eval s w) (evalb s w).
  Proof.
    elim: s w => //=.
    - by constructor.
    - move => * ; exact: idP.
    - move => s IHs t IHt w.
      apply: iffP (@implyP _ _) _ _ => ? /IHs ?; apply/IHt; firstorder.
    - move => s IHs w.
      apply: iffP (@forall_inP _ _ _) _ _ => H v /H /IHs; done.
    - move => s IHs t IHt w.
      apply: (iffP arP); apply: AR_strengthen; intuition; solve [exact/IHs|exact/IHt].
    - move => s IHs t IHt w.
      apply: (iffP auP); apply: AU_strengthen; intuition; solve [exact/IHs|exact/IHt].
  Qed.

  Lemma fin_modelP : ldec (@eval M).
  Proof. move => s w. case : (decP (evalP w s)); tauto. Qed.

End FiniteModels.

Definition cmodel_of_fmodel (M : fmodel) := CModel (@fin_modelP M).
Coercion cmodel_of_fmodel : fmodel >-> cmodel.


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
Proof. move: s => [ [|?|? ?|?|? ?|? ?] [|]] /=; try constructor. exact: isBox_true. Qed.

Definition isDia s := if s is fAX s^- then true else false.

Inductive isDia_spec s : bool -> Type :=
| isDia_true t : s = fAX t^- -> isDia_spec s true
| isDia_false  : isDia_spec s false.

Lemma isDiaP s : isDia_spec s (isDia s).
Proof. move: s => [ [|?|? ?|?|? ?|? ?] [|]] /=; try constructor. exact: isDia_true. Qed.

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
      | fAU s t,true   => supp L t true
                       || supp L s true && ((fAX (fAU s t),true) \in L)
      | fAU s t,false  => supp L t false
                       && (supp L s false || ((fAX (fAU s t),false) \in L))
      | fAR s t,true   => supp L t true
                       && (supp L s true || ((fAX (fAR s t),true) \in L))
      | fAR s t,false  => supp L t false
                       || supp L s false && ((fAX (fAR s t), false) \in L)
      | _,_ => (u,b) \in L
    end.

Notation "C |> s ^ b" := (supp C s b) (at level 30, format "C  |>  s ^ b").
Notation "C |> s ^+"  := (supp C s true) (at level 30, format "C  |>  s ^+").
Notation "C |> s ^-"  := (supp C s false) (at level 30, format "C  |>  s ^-").
Notation "C |> s"     := (supp C s.1 s.2) (at level 30).

(** For a locally consistent clause [L], the collection of formulas
supported by [L] corresponds to an (infinite) Hintikka set. *)

Lemma supp_mon L1 L2 s : L1 `<=` L2 -> L1 |> s -> L2 |> s.
Proof.
  move/subP => sub. case: s.
  elim => //= [|p|s IHs t IHt|s IHs|s IHs t IHt|s IHs t IHt] [|];
    solve [exact: sub| rewrite -?(rwP orP,rwP andP); intuition].
Qed.

Fixpoint f_weight (s : form) :=
  match s with
    | fImp s t => (f_weight s + f_weight t).+1
    | fAU s t  => (f_weight s + f_weight t).+1
    | fAR s t  => (f_weight s + f_weight t).+1
    | _        => 0
  end.
Definition s_weight := [fun s : sform => f_weight (fst s)].

Lemma sweight_lit s : s_weight s = 0 <-> literal s.
Proof. case: s => [[|p|s t|s|s t|s t] [|]] //. Qed.

Lemma supp_lit C s b : literal (s,b) -> supp C s b = ((s,b) \in C).
Proof. by case: s. Qed.

Definition form_slClass := SLClass supp_mon supp_lit sweight_lit.
Canonical Structure form_slType := SLType form_slClass.


Lemma suppC1 : (forall L s, suppC L [fset s] = L |> s)
             * (forall L s b, suppC L [fset (s,b)] = supp L s b).
Proof. split => *; exact: all_fset1. Qed.

Lemma supp0F s : ~~ fset0 |> s.
Proof. 
  case: s => /=. elim => [|x|s IHs t IHt|s IHs|s IHs t IHt|s IHt t IHs] [|] //=; 
    by rewrite ?inE // ?negb_or ?negb_and ?IHs ?IHt.
Qed.

Lemma suppE L s : L |> s -> L != fset0.
Proof. apply: contraTneq => ->. exact: supp0F. Qed.

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
Proof. case: s => [[|p|s t|s|s t|s t] [|]]; by rewrite /R sep1 /= ?fimset1 ?fimset0. Qed.

Lemma R0 : R fset0 = fset0.
Proof. by rewrite /R sep0 fimset0. Qed.

(** ** Subformula Universes *)

Definition sf_closed' (F : {fset sform}) (s:sform) :=
  match s with
    | (fImp s t,b) => ((s,negb b) \in F) && ((t,b) \in F)
    | (fAX s, b) => (s,b) \in F
    | (fAU s t, b) => [&& (fAX (fAU s t),b) \in F, (s,b) \in F & (t,b) \in F]
    | (fAR s t, b) => [&& (fAX (fAR s t),b) \in F, (s,b) \in F & (t,b) \in F]
    | _ => true
  end.
Arguments sf_closed' F !s.

Definition sf_closed (F :{fset sform}) := forall s, s \in F -> sf_closed' F s.

Lemma sf_closed'_mon (X Y : clause) s : sf_closed' X s -> X `<=` Y -> sf_closed' Y s.
Proof.
  case: s. elim => [|x|s IHs t IHt|s IHs|s IHs t IHt|s IHs t IHt] b H /subP sub //=;
    rewrite ?sub //=; by [case/andP: H | case/and3P: H].
Qed.

Lemma sfcU (X Y : {fset sform}) : sf_closed X -> sf_closed Y -> sf_closed (X `|` Y).
Proof.
  rewrite /sf_closed => /= H1 H2 s.
  case/fsetUP => [/H1 | /H2] H; apply: sf_closed'_mon H _; auto with fset.
Qed.


(** subformula closure of single formulas *)

Fixpoint ssub' b s :=
  (s,b) |` match s with
             | fImp s t => ssub' (negb b) s `|` ssub' b t
             | fAX t => ssub' b t
             | fAU s t => (fAX (fAU s t),b) |` (ssub' b s `|` ssub' b t)
             | fAR s t => (fAX (fAR s t),b) |` (ssub' b s `|` ssub' b t)
             | _ => fset0
           end.

Definition ssub (s : sform) := let (t,b) := s in (ssub' b t).

Lemma ssub'_refl s b : (s,b) \in ssub' b s.
Proof. case: s => [|x|s t|s|s t|s t] /=; by rewrite !inE. Qed.

Lemma ssub_refl s : s \in ssub s.
Proof. case: s. exact: ssub'_refl. Qed.


Lemma sf_ssub F s : sf_closed F -> s \in F -> ssub s `<=` F. 
Proof.
  case: s. elim => [|p|s IHs t IHt|s IHs |s IHs t IHt |s IHs t IHt] [|] sfc_F inF //=; 
   rewrite ?fsetU0 ?fsubUset ?fsub1 ?inF ?IHs ?IHt ?andbT //=; 
   move: (sfc_F _ inF) => /=; try bcase.
Qed.

Lemma sfc_ssub s : sf_closed (ssub s).
Proof.
  case: s.
  elim => [|x|s IHs t IHt|s IHs|s IHs t IHt|s IHs t IHt] b //= u; rewrite !inE ?orbF.
  - by move/eqP => -> /=.
  - by move/eqP => -> /=.
  - case/orP => [/eqP ->|H] /=. by rewrite !inE !ssub'_refl.
    apply: sf_closed'_mon (fsubUr _ _).
    case/orP: H => H. apply: sf_closed'_mon (fsubUl _ _). exact: IHs.
    apply: sf_closed'_mon (fsubUr _ _). exact: IHt.
  - case/orP => [/eqP ->|H] /=. by rewrite !inE !ssub'_refl.
    apply: sf_closed'_mon (fsubUr _ _). exact: IHs.
  - case/or3P => [/eqP ->| /eqP -> | H] /=; try by rewrite !inE ?ssub'_refl.
    do 2 apply: sf_closed'_mon (fsubUr _ _).
    case/orP : H => H. apply: sf_closed'_mon (fsubUl _ _). exact: IHs.
    apply: sf_closed'_mon (fsubUr _ _). exact: IHt.
  - case/or3P => [/eqP ->| /eqP -> | H] /=; try by rewrite !inE ?ssub'_refl.
    do 2 apply: sf_closed'_mon (fsubUr _ _).
    case/orP : H => H. apply: sf_closed'_mon (fsubUl _ _). exact: IHs.
    apply: sf_closed'_mon (fsubUr _ _). exact: IHt.
Qed.

(** subformula closure for clauses *)

Definition sfc C : clause := \bigcup_(s in C) ssub s.

Lemma sfc_bigcup (T : choiceType) (C : {fset T}) S :
  (forall s, sf_closed (S s)) -> sf_closed (\bigcup_(s in C) S s).
Proof.
  move => H s. case/cupP => t /= /andP [T1 T2].
  apply: sf_closed'_mon (H t s T2) _. exact: bigU1.
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


(** ** Size *)

Fixpoint f_size (s : form) := 
  match s with
    | fF => 1
    | fV p => 1
    | fImp s t => (f_size s + f_size t).+1
    | fAX s => (f_size s).+1
    | fAU s t  => (f_size s + f_size t).+1
    | fAR s t  => (f_size s + f_size t).+1
  end.

Require Import Lia.

Lemma size_ssub (s : form) (b : bool) : size (ssub (s,b)) <= 2 * f_size s.
Proof. 
  elim: s b => //= [|p|s IHs t IHt|s IHs|s IHs t IHt|s IHs t IHt] b; 
    try by rewrite fsetU0 fset1Es.
  - apply: leq_trans (fsizeU1 _ _) _. apply: leq_ltn_trans (fsizeU _ _) _.
    apply: leq_ltn_trans (leq_add (IHs _) (IHt _)) _.
    apply/leP; rewrite -!(multE,plusE); lia.
  - apply: leq_trans (fsizeU1 _ _) _. apply: leq_ltn_trans (IHs _) _.
    apply/leP; rewrite -!(multE,plusE); lia.
  - apply: leq_trans (fsizeU1 _ _) _. apply: leq_ltn_trans (fsizeU1 _ _) _.
    rewrite mulnS add2n !ltnS mulnDr. 
    apply: leq_trans (fsizeU _ _) _. exact: leq_add. 
  - apply: leq_trans (fsizeU1 _ _) _. apply: leq_ltn_trans (fsizeU1 _ _) _.
    rewrite mulnS add2n !ltnS mulnDr. 
    apply: leq_trans (fsizeU _ _) _. exact: leq_add. 
Qed.
