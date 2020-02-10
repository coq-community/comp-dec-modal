(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert.
Require Import CTL_def hilbert.
Import IC.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Agreement of Paths Semantics and Inductive Semantics *)

(** ** Agreement on Finite Models *)

(** Function choosing infinite paths for serial relations *)

Lemma xchoose_rel (T : choiceType) (e : rel T) : 
  (forall x, exists y, e x y) -> exists f, forall x, e x (f x).
Proof.
  move => serial_e. exists (fun x => xchoose (serial_e x)) => x.
  exact: xchooseP.
Qed.

(** We show that the path semantics agrees with the boolean reflections for the
inductive semantics on finite models. *)

Section Agreement.
  Variables (T: finType) (e : rel T) (p q : pred T).
  Hypothesis serial_e : forall x, exists y, e x y.
  Local Notation AUb := (AUb e p q).
  Local Notation ARb := (ARb e p q).

  Lemma auP2 w : reflect (pAU e p q w) (AUb w).
  Proof.
    rewrite /AUb; apply: introP => [|nLfp].
    - move: w. pattern (lfp (AU_fun e p q)). apply: lfp_ind; first by move => ?; rewrite inE.
      move => X IH w. case/setUP; rewrite !inE. 
      + move => qw pi pi1 pi2. exists 0 => //; congruence.
      + case/andP => pw /forall_inP inX pi pi1 pi2. 
        rewrite -pi2 in inX. move: (IH _ (inX _ (pi1 0)) (ptail pi)).
        repeat case/(_ _)/Wrap => //; first exact: path_ptail.
        case => m m1 m2. exists m.+1 => //. case => //; congruence.
    - pose e' := [rel x y | e x y && (~~ AUb x ==> p x ==> ~~ AUb y)].
      have E x : exists y, e' x y. 
        case: (boolP (AUb x)); case: (boolP (p x)) => px pAU; 
          try by case: (serial_e x) => y xy; exists y => //= ; rewrite ?(negbTE px); bcase.
        move: pAU. rewrite /AUb (lfpE (AU_mono e p q)) !inE negb_or px negb_and negb_forall /=. 
        case/andP => _ /existsP [y]. rewrite negb_imply. case/andP => *. exists y. bcase.
      case: (xchoose_rel E) => f Hf.
      pose pi n := iter n f w.
      have Pe': path (fun x y => e' x y) pi by move => n; move : (Hf (pi n)).
      suff S k : (exists2 m : nat, m < k & ~ p (pi m)) \/ ~~ AUb (pi k).
        apply: pAU_pER. exists pi. split => // n; first by case/andP : (Hf (pi n)).
        case: (S n); first tauto. 
        rewrite /AUb (lfpE (AU_mono e p q)) !inE negb_or => /andP [/negP ? _]. tauto.
      elim: k => [|k IHk]; first by right.
      case: IHk => [[m]|AR]; first by left; exists m => //; exact: ltnW.
      case: (boolP (~~ p (pi k))) => [/negP|/negPn pk] ; first by left; exists k. 
      right. move: (Pe' k). rewrite /= AR pk /=. by bcase.
  Qed.

  Lemma pARE1 w : pAR e p q w -> q w.
  Proof. 
    case: (xchoose_rel serial_e) => f Hf. 
    have pth: path e (fun n => iter n f w) by move => m; exact: Hf.
    move => Hw. case: (Hw (fun n => iter n f w) pth (erefl _) 0) => //. by case. 
  Qed.

  Lemma pARE2 w v : pAR e p q w -> ~~ p w -> e w v -> pAR e p q v.
  Proof. 
    move => Hw pw wv pi p1 p2 n. 
    case/(_ _ (erefl _))/Wrap: (@Hw (pcons w pi)). apply: path_pcons => //; congruence.
    move/(_ n.+1) => /=. intuition. case: H => [[|m]] Hm Hm'. 
    - by rewrite /= (negbTE pw) in Hm'. 
    - left. by exists m.
  Qed.

  Lemma arP2 w : reflect (pAR e p q w) (ARb w).
  Proof.
    apply: (iffP arP).
    - move => H pi p1 p2.
      suff S n : (exists2 m : nat, m < n & p (pi m)) \/ cAR e p q (pi n).
        move => n. case: (S n); first tauto. by case; right.
      elim: n => [|n IHn]; first by right; congruence. 
      case: IHn => [[m]|]; first by left; exists m => //; exact: ltnW.
      case => [? ?|qn CI]; first by left; exists n.
      right. apply CI. exact: p1.
    - move: w. cofix arP2 => w Hw. 
      case: (boolP (p w)) => Hp. 
      * apply: AR0. exact: Hp. exact: pARE1.
      * apply: ARs => [|v wv]. exact: pARE1. apply: arP2. exact: pARE2 wv.
  Qed.
End Agreement.

(** Given the agreement for AU and AR, agreement between the two semantics
follows using a simple induction on formulas *)

Lemma evalP2 (M:fmodel) s (w : M) : satisfies s w <-> eval s w.
Proof.
  apply: rwP2 (evalP w s).
  elim: s w => [|x|s IHs t IHt|s IHs|s IHs t IHt|s IHs t IHt] w /=.
  - by constructor.
  - exact: idP.
  - apply: iffP (@implyP _ _) _ _ => ? /IHs ?; apply/IHt; firstorder.
  - apply: iffP (@forall_inP _ _ _) _ _ => H v /H /IHs; done.
  - apply: iffP (@arP2 _ _ _ _ _ _ ) _ _; first exact: fser;
    apply: pAR_strengthen; intuition; solve [exact/IHs|exact/IHt].
  - apply: iffP (@auP2 _ _ _ _ _ _ ) _ _;first exact: fser;
    apply: pAU_strengthen; intuition; solve [exact/IHs|exact/IHt].
Qed.

(** ** Agreement on General Models 

Even though this is not necesary for the soundness result we prove the
corresponcence lemmas for all characterizations (AU, AG, EU, and EG). *)

Lemma dn (xm : XM) : forall P, ~ ~ P -> P.
Proof. move => P HP. case: (xm P); tauto. Qed.

Lemma dmAll (xm : XM) X (P : X -> Prop) : (~ forall x, P x) -> exists x, ~ P x.
Proof. 
  move => H. apply: (dn xm) => C. apply H => x. apply: (dn xm) => nPx. firstorder. 
Qed.

Lemma nImp (xm : XM) (P Q : Prop) : ~ (P -> Q) -> P /\ ~ Q.
Proof. case: (xm P); tauto.  Qed.

Section Paths.
  Variables (X : Type) (R : X -> X -> Prop) (P Q : X -> Prop).
  Hypothesis (R_serial : forall x, exists y, R x y).

  Implicit Types  (f g : nat -> X).

  Lemma dmAU (xm : XM) w : ~ cAU R P Q w -> cER R (PredC P) (PredC Q) w.
  Proof.
    move: w. cofix dmAU => w Hw.
    have nQw: (~ Q w). move => c. apply Hw. exact: AU0.
    case: (xm (P w)) => [pw|nPw]; last exact: ER0.
    suff {dmAU} [v v1 v2] : exists2 v, R w v & ~ cAU R P Q v.
      apply: ERs v1 _. exact: nQw. exact: dmAU.
    apply: (dn xm) => C. apply: Hw. apply: AUs pw _ => v wv. 
    apply: (dn xm) => C'. apply: C. by exists v.
  Qed.

  Lemma dmAR (xm : XM) w : ~ cAR R P Q w -> cEU R (PredC P) (PredC Q) w.
  Proof.
    move => H. apply: (dn xm) => C. apply: H. 
    move: w C. cofix dmAR => w Hw.
    have Qw : Q w. apply: (dn xm) => H. apply Hw. exact: EU0.
    case: (xm (P w)) => [Pw|nPw]; first exact: AR0.
    apply: ARs Qw _ => v wv. apply: dmAR => C. apply: Hw. exact: EUs C.
  Qed.

  Lemma dmpAR (xm : XM) w : ~ pAR R P Q w -> pEU R (PredC P) (PredC Q) w.
  Proof. 
    move => H. apply: (dn xm) => H'. apply: H => pi p1 p2 n. 
    apply: (dn xm) => C. apply: H'. exists pi. by firstorder.
  Qed.
    
  Lemma EU1 (dc : DC_ X) w : cEU R P Q w -> pEU R P Q w.
  Proof. 
    elim => {w} [w Qw|w v Pw wv _ IH]. 
    + case: (dc _ R_serial w) => f ? ?. exists f. split => //. exists 0 => //. congruence.
    + case: IH => f [f1 f2 [n Bn Qn]]. exists (pcons w f).
      split => //. apply: path_pcons => //; by rewrite f2.
      exists n.+1 => //. by case.
  Qed.

  Lemma EU2 w : pEU R P Q w -> cEU R P Q w.
  Proof.
    case => f [f1 f2 [n n1 n2]]. 
    elim: n w f f1 f2 n1 n2 => [w f _ -> _|n IH w f f1 f2 n1 n2]; first exact: EU0.
    rewrite -f2. apply: EUs (f1 0) _. exact: n1. 
    apply: (IH _ (ptail f)) => //. exact: path_ptail. 
    move => k. rewrite -ltnS. exact: n1.
  Qed.

  Lemma AU1 w : cAU R P Q w -> pAU R P Q w.
  Proof.
    elim => {w} [w Qw|w Pw _ IH].
    - move => f _ f2. exists 0; by [|congruence]. 
    - move => f pf f0. rewrite -f0 in IH. 
      case: (IH _ (pf 0) (ptail f)) => // [|n n1 n2]. exact: path_ptail.
      exists n.+1 => //. case => [|k]. congruence. exact: n1.
  Qed.

  (** This is, up to duality, the converse direction of AU1, see AU2 below *)
  Lemma ER1 (xm : XM ) (dc : DC_ X) w : cER R P Q w -> pER R P Q w.
  Proof.
    move => H.
    pose R' x y := R x y /\ (cER R P Q x -> ~ P x -> cER R P Q y).
    have R'_serial x : exists y, R' x y. 
      case: (xm (cER R P Q x)); case: (xm (P x)); try by case: (R_serial x) => y; exists y.
      move => nPx [//|y]. by exists y.
    case: (dc _ R'_serial w) => f f0 pf. 
    exists f. split => //; first by move => n; apply pf.
    suff S n : cER R P Q (f n) \/ (exists2 k : nat, k < n & P (f k)).
      move => n. case (S n);[ case; tauto|tauto]. 
    elim: n => [|n [IHn|IHn]]; first by rewrite f0; tauto.
    - case: (xm (P (f n))) => HP; [right; by exists n|left]. 
      case: (pf n) => _. by apply.
    - right. case: IHn => k ? ?. exists k => //. exact: ltnW.
  Qed.
End Paths.

Section Paths2.
  Variables (X : Type) (R : X -> X -> Prop).
  Hypothesis (R_serial : forall x, exists y, R x y).

  Lemma AU2 (xm : XM) (dc : DC_ X) P Q w : pAU R P Q w -> cAU R P Q w.
  Proof.
    move => H. apply: (dn xm) => C. 
    apply (dmAU xm) in C. apply (ER1 R_serial xm dc) in C. 
    move: H. exact: pAU_pER.
  Qed.

  Lemma ER2 (xm : XM) P Q w : pER R P Q w -> cER R P Q w.
  Proof.
    move => H. apply: (dn xm) => C. 
    have H' : pER R (PredC (PredC P)) (PredC (PredC Q)) w. 
      apply: pER_strengthen H => v; by firstorder.
    apply pAU_pER in H'. 
    apply: H'. apply: AU1. apply: (dn xm) => C'. apply (dmAU xm) in C'.
    apply: C. apply: ER_strengthen C' => ?; exact: (dn xm).
  Qed.

  Lemma AR1 (xm : XM) (dc : DC_ X) P Q w : pAR R P Q w -> cAR R P Q w.
  Proof. 
    move => H. apply: (dn xm) => C. 
    apply (dmAR xm) in C. apply (EU1 R_serial dc) in C.
    exact: pAR_pEU H.
  Qed.

  Lemma AR2 (xm : XM) P Q w : cAR R P Q w -> pAR R P Q w.
  Proof.
    move => H. apply: (dn xm) => C. apply: cAR_cEU H.
    apply: EU2. exact: dmpAR. 
  Qed.
End Paths2.

(** ** Soundness of Hilbert System for Path Semantics and General Models *)

Section Soundness.

Variables (xm : XM) (dc : DC).

Lemma sts_agreement (M:sts) (w :M) s : eval s w <-> satisfies s w.
Proof.
  elim: s w => //= [s IHs t IH|s IHs|s IHs t IH|s IHs t IH] w.
  - firstorder.
  - firstorder. 
  - split => H. 
    + apply: (AR2 xm). apply: AR_strengthen H => *; by firstorder.
    + apply: (AR1 (@serial M) xm (@dc M)). apply: pAR_strengthen H => *; by firstorder.
  - split => H.
    + apply: AU1. apply: AU_strengthen H => *; by firstorder.
    + apply: (AU2 (@serial M) xm (@dc M)). apply: pAU_strengthen H => *; by firstorder.
Qed.

Lemma sts_path_soundness s : prv s -> forall (M : sts) (w : M), satisfies s w.
Proof. 
  move => H M w. 
  have modelP : ldec (@eval M) by move => *; exact: xm.
  set M' := CModel modelP. apply/sts_agreement. exact: (@soundness _ H M').
Qed.

End Soundness.

Lemma XM_required : 
  (forall s, prv s -> forall (M : sts) (w : M), satisfies s w) -> XM.
Proof.
  move => snd.
  suff S : (forall P, ~ ~ P -> P). 
    move => P. apply: S => C. apply: (C). right => p. apply C. by left.
  move => P.
  pose L (p : var) (w :unit) := P.
  pose R (w v : unit) := True.
  have ser x : exists y, R x y. by exists tt.
  pose M := STS L ser.
  exact: (@snd _ (axDN (fV 0)) M tt).
Qed.

Lemma prv_ER : prv (ER fF (fF ---> fF)).
Proof. 
  rewrite /ER. apply: AU_ind. Intro. Apply. drop. exact: axI.
  Intro. drop. exact: ax_serial.
Qed.

Lemma DC_required : 
  (forall s, prv s -> forall (M : sts) (w : M), satisfies s w) -> DC.
Proof.
  move => snd X R ser_R x. 
  have xm : XM by exact: XM_required.
  pose M := STS (fun _ _ => False) ser_R.
  move: (snd _ prv_ER M x). case/(dmAll xm) => pi H. rewrite-/satisfies in H.
  apply (nImp xm) in H. destruct H as [p1 H].
  apply (nImp xm) in H. destruct H as [p2 _].
  by exists pi.
Qed.
 
(** * Agreement with Disjunctive Release implies LPO

We give a path characterization for AR that is classically equivalent to [pAR]
but does not constructively agree with [cAR] on finite models *)

Definition p_release' X (p q : X -> Prop) pi := 
  (forall n, q (pi n)) \/ (exists2 n, p (pi n) & forall m, m < n -> q (pi m)).

Definition pAR' X (R : X -> X -> Prop) (p q : X -> Prop) (w : X) : Prop := 
  forall pi, path R pi -> pi 0 = w -> p_release' p q pi.

Definition R3 (m n : 'I_3) : bool := 
  match m : nat, n : nat with 
    | 0,0 => true
    | 0,1 => true
    | 1,2 => true
    | 2,2 => true
    | _,_ => false
  end.

Lemma ser_R3 : forall w, exists v, R3 w v.
Proof. case => [[|[|[|n]]]] // i; by [exists ord0| exists (Ordinal (erefl (2 < 3)))]. Qed.

Definition L3 p (w : 'I_3) :=
  match p with
    | 0 => w == 1 :> nat
    | 1 => w < 2
    | _ => false
  end.

Definition M3 := FModel L3 ser_R3.

Lemma AR3_0 : cAR (@trans M3) (eval (fV 0)) (eval (fV 1)) ord0.
Proof.
  cofix AR3_0. apply: ARs; first done. 
  case. case => [|[|n]] i. 
  - suff ->: Ordinal i = ord0. move => _. exact: AR3_0. 
      congr Ordinal. exact: eq_irrelevance.
  - move => _. apply: AR0 => //. 
  - move => H. case: notF. exact: contraTT H.
Qed.

Section LPO.
  Hypothesis hyp_AR : forall (M : fmodel) (w : M) (s t : form), 
    cAR (@trans M) (eval s) (eval t) w -> pAR' (@trans M) (satisfies s) (satisfies t) w.

  Variable f : nat -> bool.

  Definition pi3 (n : nat) : 'I_3 :=
    match n with
      | 0 => ord0
      | n.+1 => if [exists m : 'I_n, f m] then Ordinal (erefl (2 < 3)) else
                  if f n then Ordinal (erefl (1 < 3)) else ord0
    end.
                       
   Lemma path_pi3 : path R3 pi3.
   Proof.
     case => [|n] ; rewrite /pi3 /R3 /=. 
     - case e : (f 0); case : (ifP _) => //=; case/existsP; by case. 
     - case e : (f n) => //=.
       + have -> /= : [exists m : 'I_n.+1, f m]. apply/existsP. by exists ord_max.
         by case: (ifP _).
     - case: (ifP _) => //=. 
       + case/existsP => m fm. 
         suff -> : [exists m : 'I_n.+1, f m] by [].
         apply/existsP. exists (inord m). by rewrite inordK // ltnW // ltnS ltn_ord.
       + move => H. case: (ifP _) => //; last by case: (ifP _).
         case/existsP => m fm /=. apply: contraFT H => _. apply/existsP.
         suff On : m < n by exists (Ordinal On).
         rewrite ltn_neqAle -ltnS ltn_ord andbT. apply: contraTneq fm => ->. 
         by rewrite e.
   Qed.

   Lemma LPO_of_disjunctive_AR : (forall n, f n = false) \/ exists n, f n = true.
   Proof.
     case: (hyp_AR AR3_0 path_pi3 (erefl _)) => H; [left|right].
     - move => n. apply: contraTF (H n.+3) => Hn.
       rewrite /= (_ : [exists m : 'I_n.+2, f m] = true) //=.
       apply/existsP. have On : n < n.+2 by done. by exists (Ordinal On).
     - case: H => [[|n]] //=. do 2 (case: (ifP _) => //=). by exists n.
   Qed.
End LPO.
