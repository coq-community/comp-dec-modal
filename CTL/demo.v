(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base sltype.
Require Import CTL_def dags.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (C D E F : clause) (S T : {fset clause}) (G : rGraph clause).

(** * Relaxed Demos *)

(* ** Demands

Remark: We write [R] for the request and [Rec] for the demands of a clause. *)

Definition AXn C := [fset s in C | isDia s].
Definition Req C := [fset R C] `|` [fset body s |` R C | s <- AXn C].

Lemma in_Req u C : fAX u^- \in C -> u^-|` R C \in Req C.
Proof. move => H. rewrite !inE;rightb. apply/fimsetP. by exists (fAX u^-); rewrite ?inE ?H. Qed.

Lemma inhab_Req C : exists D, D \in Req C.
Proof. exists (R C). by rewrite !inE. Qed.

Lemma Req_RC C D : D \in Req C -> R C `<=` D.
Proof. rewrite !inE. case/predU1P => [->//|/fimsetP [s _ ->]] //. exact: subxx. Qed.

(** ** Relaxed Fulfillment 

We define the fulfillment relations using fixpoint iteration. This turns out to
be technically convenient since we never prove anything by induction on the
fulfillment relations *)


Section Fulfillment.
  Variable S T: {fset clause}.

  Definition fulfillAU_step s t (X : {fset clause}) :=
    [fset Y in T | [all C in Req Y,
       suppS S (t^+ |` C) || [some L in T, suppC L (s^+ |` C) && (L \in X)]]].
  Definition fulfillsAU s t L := L \in fset.lfp T (fulfillAU_step s t).

  Lemma bounded_fulfillAU_step s t : bounded T (fulfillAU_step s t).
  Proof. move => X _. exact: subsep. Qed.

  Lemma monotone_fulfillAU_step s t : monotone (fulfillAU_step s t).
  Proof.
    move => X Y X_sub_Y. apply: sep_sub; first exact: subxx.
    move => ? inS /=. apply: sub_all => C /orP [H|H];[leftb|rightb].
    - exact: sub_has H => L.
    - apply: sub_has H => L. case: (suppC _ _) => //=. exact: (subP X_sub_Y).
  Qed.

  Definition fulfillsAUE s t := fset.lfpE (monotone_fulfillAU_step s t) (bounded_fulfillAU_step s t).

  Definition fulfillAR_step s t (X : {fset clause}) :=
    [fset Y in T |
     [all D in Req Y, suppS S D] && 
      (suppS S (t^- |` R Y) || [some E in T, suppC E (s^- |` R Y) && (E \in X)])].
  Definition fulfillsAR s t L := L \in fset.lfp T (fulfillAR_step s t).

  Lemma bounded_fulfillAR_step s t : bounded T (fulfillAR_step s t).
  Proof. move => X _. exact: subsep. Qed.

  Lemma monotone_fulfillAR_step s t : monotone (fulfillAR_step s t).
  Proof.
    move => X Y X_sub_Y. apply: sep_sub; first exact: subxx.
    move => ? inS /=. case: [all _ in _ , _] => //=.
    case/orP =>[H|H];[by leftb|rightb].
    apply: sub_has H => L. case: (suppC _ _) => //=. exact: (subP X_sub_Y).
  Qed.

  Definition fulfillsARE s t := fset.lfpE (monotone_fulfillAR_step s t) (bounded_fulfillAR_step s t).

End Fulfillment.

Definition AXn_complete (S : {fset clause})  :=
  forall L C, L \in S -> C \in Req L -> exists L', (L' \in S) && suppC L' C.

Record demo (S T : {fset clause})  :=
  Demo { demoT : forall C, C \in T -> lcons C;
         demoSsubT : {subset S <= T};
         demo1 : AXn_complete S;
         demo2 s t L : L \in S -> fAX (fAU s t)^+ \in L -> fulfillsAU S T s t L;
         demo3 s t L : L \in S -> fAX (fAR s t)^- \in L -> fulfillsAR S T s t L}.


(** ** Fragment Demos *)

Section FragmentDemo.
  Variables (S T : {fset clause}).
                                       
  Definition Fs : {fset sform} := \bigcup_(C in S) C.

  Definition req_cond G := 
    forall x : G, ~~ leaf x -> forall D, D \in Req (label x) -> exists2 y, edge x y & suppC (label y) D.

  Definition supp_cond G := 
    forall (x y : G), edge x y -> suppC (label y) (R (label x)).

  Definition ev_cond u G := 
    let C := label (root G) in 
       match u with
         | fAX (fAU s t)^+ => 
           (u \in C) && C |> s^+ -> forall x:G, if leaf x then label x |> t^+ else label x |> s^+
         | fAX (fAR s t)^- => 
           (u \in C) && C |> s^- -> (forall x:G, ~~ leaf x -> label x |> s^-)
                                 /\ (exists x:G, label x |> t^-)
         | _ => True
       end.

  Definition glabels_from (G : graph clause) :=
    forall x : G, if leaf x then label x \in S else label x \in T.

  Record fragment G u L := {
    DG1 : label (root G) = L;
    DG2 : terminates (erel G);
    DG3 : req_cond G;
    DG4 : supp_cond G;
    DG5 : ev_cond u G;
    DG6 : ~~ leaf (root G);
    DG7 : glabels_from G
  }.

  Record fragment_demo :=
    FragmentDemo {
        fd_trees L u :> (u \in Fs) -> (L \in S) -> { G : rGraph clause | fragment G u L };
        fd_sub : {subset S <= T};
        fd_lcons C : C \in T -> lcons C
      }.

  Definition fragment_bound (DD : fragment_demo) n := 
    forall L u (inFs : u \in Fs) (inD : L \in S), #|sval (DD _ _ inFs inD)| <= n. 
End FragmentDemo.


(** * Model Construction 

The model construction for CTL consists of two parts: the construction of
fragments form inductive fulfillment and the assemly of fragments into a
model.

 ** Relaxed Fullfillment to Fragments 

  We now construct the fragments required for the model
  constructioon. There are three cases:

  - Fragments for [fAX (fAU s t)^+ \in C]
  - Fragments for [fAX (fAR s t)^- \in C]
  - Fragments where the eventuallity condition is trivial

  This case split is justfied by the lemma below. *)


Inductive ev_case (C : clause) (s : sform) : Type :=
  | ev_AR u v : s = fAX (fAR u v)^- -> C |> u^- -> C |> fAX (fAR u v)^- -> ev_case C s
  | ev_AU u v : s = fAX (fAU u v)^+ -> C |> u^+ -> C |> fAX (fAU u v)^+ -> ev_case C s
  | ev_x : (forall G, label (root G) = C -> ev_cond s G) -> ev_case C s.

Lemma evP C s : ev_case C s.
Proof with try by apply: ev_x => G; rewrite /ev_cond.
  case: s => [[|x|s t|s|s t|s t]] [|]...
  - case: s => [|x|s t|s|s t|s t]... case: (boolP (C |> fAX (fAU s t)^+)) => /= E.
    case: (boolP (C |> s^+)) => E'. exact: ev_AU E' E.
    apply: ev_x => G; rewrite /ev_cond => ->. by rewrite E (negbTE E').
    apply: ev_x => G; rewrite /ev_cond => ->. by rewrite (negbTE E).
  - case: s => [|x|s t|s|s t|s t]... case: (boolP (C |> fAX (fAR s t)^-)) => /= E.
    case: (boolP (C |> s^-)) => E'. exact: ev_AR E' E.
    apply: ev_x => G; rewrite /ev_cond => ->. by rewrite E (negbTE E').
    apply: ev_x => G; rewrite /ev_cond => ->. by rewrite (negbTE E).
Qed.


Section DemoToFragment.
  Variables (S T : {fset clause}) (demoST : demo S T).

  Section Fragments.
  Variables (s t : form).

    (** Fragments for AU

  The construction of fragments for AU is completely declarative (no recursion
  involved). Even the verification of the fragment conditions does not use
  induction *)

  Definition AU_level C (rC : fulfillsAU S T s t C) : nat := levl (monotone_fulfillAU_step S T s t) rC.

  Definition AUl := [fset C in T | fulfillsAU S T s t C].
  Definition AUr := [fset C in S | C |> t^+].

  Lemma AUlE C : C \in AUl -> fulfillsAU S T s t C.
  Proof. rewrite !inE; bcase. Qed.

  Definition AU_T0 := (seq_sub AUl + seq_sub AUr)%type.
  Definition AU_label (x : AU_T0) := match x with inl x => val x | inr x => val x end.

  Definition AU_rel (x y : AU_T0) :=
    match x,y with
     | inl (SeqSub C rC),inl (SeqSub D rD) =>
       [&& D |> s^+, suppC D (R C) & (AU_level (AUlE rD) < AU_level (AUlE rC))]
     | inl (SeqSub C rC),inr (SeqSub D rD) => suppC D (R C)
     | inr _,_ => false
    end.

  Lemma AU_rel_succ (x : seq_sub AUl) D :
    D \in Req (ssval x) -> exists2 y, AU_rel (inl x) y & suppC (AU_label y) D.
  Proof.
    case: x => /= C /AUlE rC DinReq.
    move : (level1 (monotone_fulfillAU_step S T s t) rC). rewrite -!/(AU_level _).
    rewrite [iter _ _ _]/= {1}/fulfillAU_step inE. case/andP => XinDD.
    move/allP => /(_ _ DinReq). case/orP => [/hasP [E inDD]|/hasP [E inS0]].
    - rewrite suppCU suppC1. case/andP => E_t E_D.
      have SE: E \in AUr. rewrite inE;bcase.
      exists (inr (SeqSub E SE)) => //.
      apply: suppC_sub E_D. exact: Req_RC.
    - rewrite suppCU suppC1 -andbA => /and3P [E_s E_D E_I].
      case/level2 : (E_I) => rE L. rewrite -!/(AU_level _) in L.
      have SE: E \in AUl by rewrite inE inS0.
      exists (inl (SeqSub E SE)) => //.
      rewrite [AUlE SE](bool_irrelevance _ rE) L E_s /= andbT.
      apply: suppC_sub E_D. exact: Req_RC.
  Qed.

  Lemma AU_rel_term : terminates AU_rel.
  Proof.
    pose f (x : AU_T0) := if x is inl (SeqSub C rC) then (AU_level (AUlE rC)).+1 else 0.
    apply: (@terminates_measure _ f) => [[[C rC]|[C rC]]] [[D rD]|[D rD]] //=.
    case/and3P => _ _ ?. by rewrite ltnS.
  Qed.

  Lemma AU_rel_supp x y : AU_rel x (inl y) -> AU_label (inl y) |> s^+.
  Proof. case: x => // x. case: x => ? ?; case: y => ? ? /=; bcase. Qed.

  Lemma frag_AU C : C |> s^+ -> fAX (fAU s t)^+ \in C -> fAX (fAU s t)^+ \in Fs S -> C \in S ->
    {G : rGraph clause | fragment S T G (fAX (fAU s t)^+) C & #|G| <= 2 * size T}.
  Proof.
    move => C1 C2 C3 C4.
    have C4' : C \in T. exact: demoSsubT demoST _ _.
    have CinAUL : C \in [fset C in T | fulfillsAU S T s t C] by rewrite inE C4' demo2.
    pose x0 : AU_T0 := inl (SeqSub C CinAUL).
    pose V := { x : AU_T0 | connect AU_rel x0 x }.
    pose v0 : V := Sub x0 (connect0 _ x0).
    pose E (x y : V) := AU_rel (val x) (val y).
    pose L (x : V) : clause := AU_label (sval x).
    pose G := Graph E L.
    have rP (v : G) : connect E v0 v. exact: connect_subtype.
    pose rG := RGraph rP.
    have lf (x : seq_sub AUr) p : @leaf _ rG (Sub (inr x) p).
      by apply/negP => /existsP [y] //.
    have nlf (x : seq_sub AUl) p : ~~ @leaf _ rG (Sub (inl x) p).
      rewrite negbK. apply/existsP. case: (inhab_Req (@label _ rG (Sub (inl x) p))) => D.
      case/AU_rel_succ => y y1 y2.
      suff H: connect AU_rel x0 y by exists (Sub y H).
      exact: connect_trans p (connect1 _).
    exists rG. split.
    - done.
    - move => x. exact: sn_preimage (AU_rel_term (val x)).
    - case => [[x|x]] p /=; last by rewrite lf.
      move => _ D /AU_rel_succ [y] y1 y2.
      have conn: connect AU_rel x0 y. exact: connect_trans (connect1 y1).
      by exists (Sub y conn).
    - move => x y. case: x => [[[x Hx]|[x Hx]]]; case: y => [[[y Hy]|[y Hy]]] Hx' Hy' ;
        rewrite //= /E /L /=; by bcase.
    - rewrite /ev_cond /v0 /L /= /L /= C2 C1 /= => _ x. 
      case: x => [[x|x]] p. 
      + rewrite -[exist _ _ _]/(Sub (inl x) p) (negbTE (nlf _ _)).
        (* IH not needed *)
        case/connectP : p (p). elim/last_ind => [_ -> p //|pth y _].
        rewrite last_rcons rcons_path => /andP [p1 p2] ? p; subst.
        move: p2. exact: AU_rel_supp.
      + rewrite -[exist _ _ _]/(Sub (inr x) p) lf.
        move: (ssvalP x). rewrite inE /= /L /=. bcase.
    - exact: nlf.
    - move => x.
      case: x => [[x|x]] p.
      - rewrite -[exist _ _ _]/(Sub (inl x) p) (negbTE (nlf _ _)).
        move: (ssvalP x). rewrite inE; by bcase.
      - rewrite -[exist _ _ _]/(Sub (inr x) p) lf.
        move: (ssvalP x). rewrite inE; by bcase.
    - rewrite card_sig. apply: leq_trans (max_card _) _.
      rewrite card_sum mul2n -addnn leq_add // card_seq_sub ?funiq //.
      + exact: subset_size (subsep _ _).
      + apply: (@leq_trans (size S)); apply: subset_size. exact: subsep. apply/subP. exact: demoSsubT.
  Qed.


  (** Fragments for AR

  The construction of fragments for AR is also completely declarative. Unlike for
  AU, the verification of the fragment conditions requires an induction the level
  to locate the clause fulfilling t^-*)

  Definition AR_level C (rC : fulfillsAR S T s t C) : nat := levl (monotone_fulfillAR_step S T s t) rC.

  Definition ARl := [fset C in T | fulfillsAR S T s t C].
  Definition ARr := S.

  Lemma ARlE C : C \in ARl -> fulfillsAR S T s t C.
  Proof. rewrite !inE; bcase. Qed.

  Definition AR_T0 := (seq_sub ARl + seq_sub ARr)%type.

  Definition AR_rel (x y : AR_T0) :=
    match x,y with
      | inl (SeqSub C rC),inl (SeqSub D rD) =>
        [&& D |> s^-, suppC D (R C) & (AR_level (ARlE rD) < AR_level (ARlE rC))]
      | inl (SeqSub C rC),inr (SeqSub D rD) => suppC D (R C)
      | inr _,_ => false
    end.

  Definition AR_label (x : AR_T0) := match x with inl x => val x | inr x => val x end.

  Lemma AR_rel_succ (x : seq_sub ARl) D :
    D \in Req (ssval x) -> exists2 y, AR_rel (inl x) y & suppC (AR_label y) D.
  Proof.
    move: (ssvalP x). rewrite inE => /andP[_ S2] inReq.
    rewrite /fulfillsAR fulfillsARE inE in S2. case/and3P : S2 => _ /allP S2 _.
    move: S2 => /(_ _ inReq). case/hasP => [E E1 E2].
    exists (inr (SeqSub E E1)) => //=. case: x inReq => //= C _ /Req_RC H.
    exact: suppC_sub E2.
  Qed.

  Lemma AR_rel_term : terminates AR_rel.
  Proof.
    pose f (x : AR_T0) := if x is inl (SeqSub C rC) then (AR_level (ARlE rC)).+1 else 0.
    apply: (@terminates_measure _ f) => [[[C rC]|[C rC]]] [[D rD]|[D rD]] //=.
    case/and3P => _ _ ?. by rewrite ltnS.
  Qed.

  Lemma AR_ev_cond (x : seq_sub ARl) :
    exists2 y, connect AR_rel (inl x) y & AR_label y |> t^-.
  Proof.
    pose L x := AR_level (ARlE (ssvalP x)).
    move: {x} (L x).+1 {-2}x (ltnSn (L x)). elim => //. (* induction *)
    - move => n IHn x Hx.
      move: (level1 (monotone_fulfillAR_step S T s t) (ARlE (ssvalP x))).
      rewrite -/(AR_level _) /= inE.
      case/and3P => XinDD _. case/orP => [/hasP [E EinDD]|/hasP [E EinS0]].
      + rewrite suppCU suppC1 => /andP[E_t E_R].
        exists (inr (SeqSub E EinDD)) => //. apply: connect1.
        by case: x E_R {Hx XinDD}.
      + case/andP => suppE. case/level2 => rE bE. rewrite -!/(AR_level _) in bE.
        have El : E \in ARl. by rewrite inE EinS0.
        have/IHn [y y1 y2]: L (Sub E El) < n.
          rewrite /L [ARlE _](bool_irrelevance _ rE). apply: leq_trans bE _.
          by rewrite -ltnS.
        exists y => //. apply: connect_trans (connect1 _) y1.
        case: x bE suppE {XinDD Hx} => //= C rC E1 E2.
        by rewrite -suppC1 andbA -suppCU E2 [_ El](bool_irrelevance _ rE).
  Qed.

  Lemma AR_rel_supp x y : AR_rel x (inl y) -> AR_label (inl y) |> s^-.
  Proof. case: x => // x. case: x => ? ?; case: y => ? ? /=; bcase. Qed.

  Lemma frag_AR C : C |> s^- -> fAX (fAR s t)^- \in C -> fAX (fAR s t)^- \in Fs S -> C \in S ->
    {G : rGraph clause | fragment S T G (fAX (fAR s t)^-) C & #|G| <= 2 * size T}.
  Proof.
    move => C1 C2 C3 C4.
    have C4' : C \in T. exact: demoSsubT demoST _ _. 
    have CinARl : C \in [fset C in T | fulfillsAR S T s t C] by rewrite inE C4' demo3.
    pose x0 : AR_T0 := inl (Sub C CinARl).
    pose V := { x : AR_T0 | connect AR_rel x0 x }.
    pose v0 : V := Sub x0 (connect0 _ x0).
    pose E (x y : V) := AR_rel (val x) (val y).
    pose L (x : V) : clause := AR_label (sval x).
    pose G := Graph E L.
    have rP (v : G) : connect E v0 v. exact: connect_subtype.
    pose rG := RGraph rP.
    have lf (x : seq_sub ARr) p : @leaf _ rG (Sub (inr x) p).
      by apply/negP => /existsP [y] //.
    have nlf (x : seq_sub ARl) p : ~~ @leaf _ rG (Sub (inl x) p).
      rewrite negbK. apply/existsP. case: (inhab_Req (@label _ rG (Sub (inl x) p))) => D.
      case/AR_rel_succ => y y1 y2.
      suff H: connect AR_rel x0 y by exists (Sub y H).
      exact: connect_trans p (connect1 _).
    exists rG. split.
    - done.
    - move => x. exact: sn_preimage (AR_rel_term (val x)).
    - case => [[x|x]] p /=; last by rewrite lf.
      move => _ D /AR_rel_succ [y] y1 y2.
      have conn: connect AR_rel x0 y. exact: connect_trans (connect1 y1).
      by exists (exist _ y conn).
    - move => x y. 
      case: x => [[[x Hx]|[x Hx]]]; case: y => [[[y Hy]|[y Hy]]] Hx' Hy' ;
      rewrite //= /E /L /=; try bcase.
    - rewrite /ev_cond /v0 /L /= /L /= C2 C1 /= => _. split.
      + case => [[x|x]] p; rewrite ?lf // -[exist _ _ _]/(Sub (inl x) p).
        move => _. case/connectP : p (p). elim/last_ind => [_ -> p //|pth z IH].
        rewrite last_rcons rcons_path => /andP [p1 p2] ? p; subst.
        move: p2. exact: AR_rel_supp.
      + case: (AR_ev_cond (Sub C CinARl)) => y y1 y2. by exists (Sub y y1).
    - exact: nlf.
    - move => x.
      case: x => [[x|x]] p.
      - rewrite -[exist _ _ _]/(Sub (inl x) p) (negbTE (nlf _ _)).
        move: (ssvalP x). rewrite inE; by bcase.
      - rewrite -[exist _ _ _]/(Sub (inr x) p) lf. exact: (ssvalP x).
    - rewrite card_sig. apply: leq_trans (max_card _) _.
      rewrite card_sum mul2n -addnn leq_add // card_seq_sub ?funiq //.
      + exact: subset_size (subsep _ _).
      + apply: (@leq_trans (size S)); apply: subset_size => //. exact: subxx. apply/subP. exact: demoSsubT.
  Qed.

  End Fragments.

  Lemma simple_frag s C : (forall G, label (root G) = C -> ev_cond s G) ->
    C \in S -> { G : rGraph clause | fragment S T G s C & #|G| <= 2 * size T}.
  Proof.
    move => ev_s inDD.
    pose xs : seq clause := [fset D in S | suppC D (R C)].
    pose V := option (seq_sub xs).
    pose E := [rel x y : V | ~~ isSome x && isSome y].
    pose L (x:V) : clause := if x is Some v then val v else C.
    pose G := Graph E L.
    have rP (x:G) : connect E None x. case: x => // x. exact: connect1.
    pose rG := RGraph rP.
    have s_cond_C D : D \in Req C -> exists2 y : option (seq_sub xs), y & suppC (L y) D.
      move => inReq. case/(demo1 demoST) : (inReq) => // D' /andP[D1 D2].
      suff in_xs : D' \in xs by exists (Some (Sub D' in_xs)).
      rewrite inE D1. exact: suppC_sub (Req_RC _ ) D2.
    exists rG. split.
    - done.
    - have H x : sn (erel rG) (Some x) by constructor.
      case; first exact: H. constructor => [[y _|//]]. exact: H.
    - move => [x|] H D //= inReq; first by rewrite negbK in H; case/existsP : H.
      exact: s_cond_C.
    - move => [x|] [y|] //=. move: (ssvalP y). by rewrite inE; bcase.
    - exact: ev_s.
    - rewrite negbK. apply/existsP. case: (inhab_Req C) => D /= inReq.
      case/s_cond_C : inReq. eauto.
    - move => x.
      suff H : label x \in S.
        rewrite H [_ \in T](_ : _ = true) ?if_same //. move: H. exact: demoSsubT.
      case: x => [v|//]. move : (ssvalP v). rewrite inE; by bcase.
    - rewrite card_option mul2n -addnn -addn1 leq_add ?card_seq_sub ?funiq //.
      + apply: subset_size. apply: sub_trans (subsep _ _) _. apply/subP. exact: demoSsubT.
      + apply: (@leq_trans (size [fset C])); first by rewrite fset1Es.
        apply subset_size. rewrite fsub1.
        exact: demoSsubT demoST _ _. 
  Qed.


  (** We package the fragments into a fragment demp. Save for the size-bound for
  the constructed model, the construction of models from fragments is
  independent of the size of the fragments. Hence, we keep the [fragment_demo]
  separate from the [ragment_bound]. *)  
  
  Definition bounded_demo (D Dl : {fset clause}) (n : nat) :=
    forall L u (inFs : u \in Fs D) (inD : L \in D), {G : rGraph clause | fragment D Dl G u L & #|G| <= n}.

  Lemma DD_bounded_demo : bounded_demo S T (2 * size T).
  Proof.
    move => C u'. case: (evP C u') => [s t ->|s t ->|]; auto using frag_AR, frag_AU, simple_frag.
  Qed.

  Lemma DD_demo_aux : { FRAG : fragment_demo S T | fragment_bound FRAG (2 * size T) }.
  Proof.
    pose FRAG L u (inFs : u \in Fs S) (inDD : L \in S) :=
      let G := DD_bounded_demo inFs inDD in exist _ (s2val G) (s2valP G).
    exists (FragmentDemo FRAG (demoSsubT demoST) (demoT demoST)).
    move => /= L u inFs inD. rewrite /FRAG /=. exact: (s2valP' (DD_bounded_demo inFs inD)).
  Qed.

  Definition DD_demo : fragment_demo S T := sval DD_demo_aux.

  Lemma DD_fragment_bound : fragment_bound DD_demo (2 * size T).
  Proof. exact: (svalP DD_demo_aux). Qed.
  
End DemoToFragment.

(** ** Fragments to Models *)

(** [interp'] is convertible to the sltype.interp with the [slpType] instance
for formulas given in [hilbert.v]. The local definition avoids a spurious
dependency of the model construction on the Hilbert system *)

Definition interp' s := match s with u^+ => u | u^- => fImp u fF end.

Module ModelConstruction.
Section ModelConstruction.
  Variables (Dl D : {fset clause}) (FD : fragment_demo D Dl).
  
  (** We turn both [Fs D] and [D] into finite types and construct a
  finite matrix of fragments indexed by the finite type [DF * DC] *)

  Definition DF := seq_sub (Fs D).
  Definition DC := seq_sub D.

  (* Welcome to the Matrix! *)
  Definition Frag (p: DF * DC) := (sval (FD.(fd_trees) (ssvalP p.1) (ssvalP p.2))).

  Lemma FragP (p: DF * DC) : fragment D Dl (Frag p) (val p.1) (val p.2).
  Proof. exact: (svalP (FD.(fd_trees) (ssvalP p.1) (ssvalP p.2))). Qed.

  Definition MType := { p : DF * DC &  Frag p }.
  Definition MLabel p (x:MType) := fV p^+ \in label (tagged x).

  (** For the definition of the transistion relation, we use the
  litf_edge construction to lift all the internal edges of the various
  dags to transitions in the model. We define a cyclic next fuction we
  define on finite types *)

  Definition MRel (x y : MType) :=
     lift_edge x y  ||
      (let: (existT p a, (existT q a')) := (x,y) in
       [&& leaf a, q.1 == next p.1, edge (root (Frag q)) a' & label a == val q.2 ]).

  (** Cast from nodes of fragments fo states of the model *)
  Definition Mstate (p: DF * DC) (x : Frag p) : MType := existT p x.

  Unset Printing Records.

  (** To construct a finite model, we need to show that [MRel] is serial *)

  Lemma label_DF (p : DF * DC) (x : Frag p) : leaf x -> label x \in D.
  Proof. move/DG7/(_ x) : (FragP p). by case: (leaf _). Qed.

  Lemma root_internal (p : DF * DC) : ~~ leaf (root (Frag p)).
  Proof. by move/DG6 : (FragP p). Qed.

  Lemma serial_MRel (x : MType) : exists y, MRel x y.
  Proof.
    case: x => p x. case (boolP (leaf x)) => [lf|].
    - have inF := label_DF lf.
      move: (root_internal (next p.1, SeqSub _ inF)). rewrite negbK => /existsP [y xy].
      exists (Mstate y). by rewrite /MRel lf /Mstate xy /= !eqxx.
    - rewrite negbK => /existsP [y xy]. exists (Mstate y).
      by rewrite /MRel lift_eq xy.
  Qed.

  Definition MD := FModel MLabel serial_MRel.

  (** We prove a number of lemmas to extract fragment properties and lift
  porperies from the dags to the model [MD] *)

  Lemma label_root (p : DF * DC) : label (root (Frag p)) = val (p.2).
  Proof. apply/DG1 : (FragP p). Qed.

  Lemma dmat_ev_cond (p : DF * DC) : ev_cond (val p.1) (Frag p).
  Proof. apply/DG5 : (FragP p). Qed.

  Lemma sn_edge (p : DF * DC) (x : Frag p) : sn (edge (g := Frag p)) x.
  Proof. by move/DG2 : (FragP p). Qed.

  Lemma label_Dl (p : DF * DC) (x : Frag p) : ~~ leaf x -> label x \in Dl.
  Proof. move/DG7/(_ x) : (FragP p). by case: (leaf _). Qed.

  Lemma label_lcon (x : MType) : lcons (label (tagged x)).
  Proof.
    case: x => p x.
    case: (boolP (leaf x)) => [/label_DF /FD.(fd_sub) |/label_Dl]; by move/FD.(fd_lcons).
  Qed.

  Lemma rlabel_Fs p : {subset label (root (Frag p)) <= Fs D}.
  Proof. rewrite label_root. case: p => /= _ [C inD]. apply/subP => /=. exact: bigU1. Qed.

  Lemma dag_R (p : DF * DC) (x y : Frag p) : edge x y -> suppC (label y) (R (label x)).
  Proof. by move/DG4: (FragP p) => /(_ x y). Qed.

  Lemma MRel_R (x y : MType) : MRel x y -> suppC (label (tagged y)) (R (label (tagged x))).
  Proof.
    case: x => p x. case: y => p' y. rewrite /MRel. case/orP => [H|].
    - move: (liftE H) => ?; subst. rewrite lift_eq in H. exact: dag_R.
    - case/and4P => [_ /eqP Hp edg /eqP Hl] /=. move: (dag_R edg). by rewrite label_root -Hl.
  Qed.

  Lemma dag_D (p : DF * DC) (x : Frag p) s :
    ~~ leaf x -> fAX s^- \in label x -> exists2 y, edge x y & label y |> s^-.
  Proof.
    move => nl /in_Req H. move/DG3 : (FragP p) => /(_ x nl _ H) [y].
    rewrite suppCU suppC1. exists y => //; bcase.
  Qed.

  Lemma MRel_D (x : MType) s :
    fAX s^- \in label (tagged x) -> exists2 y, MRel x y & label (tagged y) |> s^-.
  Proof.
    case: x => p x. case (boolP (leaf x)) => lf Ls.
    - have inF := label_DF lf.
      move: (root_internal (next p.1, SeqSub _ inF)) => H. set p' := (_,_) in H.
      have Ls' : fAX s^- \in label (root (Frag p')) by rewrite label_root /=.
      case: (dag_D H Ls') => y Hy Lys. by exists (Mstate y); rewrite // /Mstate /MRel Hy /p' lf /= !eqxx.
    - case: (dag_D lf Ls) => y Hy Lys. by exists (Mstate y); rewrite // /Mstate /MRel lift_eq Hy.
  Qed.

  Lemma supp_edge (p : DF * DC) (x y : Frag p) s : label x |> fAX s^+ -> edge x y -> label y |> s^+.
  Proof. rewrite -[_ y |> _]suppC1 => H xy. move: (dag_R xy). apply: suppC_sub. by rewrite fsub1 RE. Qed.

  Prenex Implicits edge.

  (** We define special predicates over [MD] that express the
  eventualities in terms of support instead of [eval]. In the proof of
  the support lemma, this will be what is left to show after the
  induction hypothesis has been applied. *)

  Definition AU_M s t (x : MD) :=
    cAU MRel (fun z => label (tagged z) |> s^+) (fun z => label (tagged z) |> t^+) x.

  Definition EU_M s t (x : MD) :=
    cEU MRel (fun z => label (tagged z) |> s^-) (fun z => label (tagged z) |> t^-) x.

  (** We make use uf the fact, that CTL cannot distinguish between
  equally labeled states that have the same successorts. In particular
  this means that an eventuallity is satisfied at the leaf of one dag,
  if it is satiesfied at the equally labeled root of the next row. *)

  Lemma leaf_root_aux (p : DF * DC) (x : Frag p) (lf : leaf x) :
      forall y, MRel (Mstate (root (Frag (next p.1, SeqSub (label x) (label_DF lf))))) y <->
                MRel (Mstate x) y.
  Proof.
    move => [p' y]. rewrite /MRel /Mstate (negbTE (root_internal _)) [_ && _]/= orbF.
    split => [le|/orP [le|H]].
    - move: (liftE le) => ?;subst. rightb. rewrite lf /= !eqxx. by rewrite lift_eq in le.
    - move: (liftE le) => ?;subst. rewrite lift_eq in le.
      suff: false by []. rewrite -(negbTE lf). apply/existsP. by eexists.
    - case/and4P : H => _. destruct p as [u L]. destruct p' as [u' L'].
      move/eqP => /= ? e; subst. move/eqP => Lx. move: (label_DF lf). rewrite Lx => inDF.
      rewrite [SeqSub _ _](_ : _ = L') ?lift_eq //. apply/eqP. destruct L'. exact: eqxx.
  Qed.

  Lemma leaf_root s t (p : DF * DC) (x : Frag p) (lf : leaf x) :
    AU_M s t (Mstate (root (Frag (next p.1, SeqSub (label x) (label_DF lf))))) ->
    AU_M s t (Mstate x).
  Proof. move => R. apply: cAU_eq R; try by rewrite /= label_root. exact: leaf_root_aux. Qed.

  Lemma leaf_root' s t (p : DF * DC) (x : Frag p) (lf : leaf x) :
    EU_M s t (Mstate (root (Frag (next p.1, SeqSub _ (label_DF lf))))) ->
    EU_M s t (Mstate x).
  Proof. move => R. apply: cEU_eq R; try by rewrite /= label_root. exact: leaf_root_aux. Qed.

  (** Every eventuality is fulfilled at the root of its correspinding dag. *)

  Lemma AU_this (s t : form) (L : DC) (inF : fAX (fAU s t)^+ \in Fs D) :
    let p := (SeqSub (fAX (fAU s t)^+) inF, L) in
    label (root (Frag p)) |> fAU s t^+ -> AU_M s t (Mstate (root (Frag p))).
  Proof.
    move => p. rewrite /=. case/orP => [?|/andP[E2 E3]]; first exact: AU0.
    move: (dmat_ev_cond p). rewrite /ev_cond /= E2 E3 /= => /(_ erefl) GL.
    elim: (sn_edge (root _)) => x _ IHsn.
    move: (GL x). case: (boolP (leaf x)) => nlf ?; first exact: AU0.
    apply: AUs => // [[p' y]]. rewrite /Mstate {1}/MRel (negbTE nlf) [_ && _]/= orbF => l_edge.
    move: (liftE l_edge) => ?; subst. rewrite lift_eq in l_edge. exact: IHsn.
  Qed.

  Lemma EU_this (s t : form) (L : DC) (inF : fAX (fAR s t)^- \in Fs D) :
    let p := (SeqSub (fAX (fAR s t)^-) inF, L) in
    label (root (Frag p)) |> fAR s t^- -> EU_M s t (Mstate (root (Frag p))).
  Proof.
    move => p. rewrite /=. case/orP => [?|/andP[E2 E3]]; first exact: EU0.
    move: (dmat_ev_cond p). rewrite /ev_cond /= E2 E3 /= => /(_ erefl) [E4 [z]].
    case/connectP : (rootP z) => xs.
    elim: xs (root _) => [x|y ys IHys x /=].
    - move => _ -> /= ?. exact: EU0.
    - case/andP => xy pth ? ?.
      have M: MRel (Mstate x) (Mstate y) by rewrite /MRel lift_eq; bcase.
      apply: EUs (M) _ => //=; last exact: IHys.
      apply: E4. rewrite negbK. by apply/existsP; eexists.
  Qed.

  (** We can always defer fullfilling an eventuality to the next row. *)

  Lemma EU_lift (s t : form) (p : DF * DC) (x : Frag p) :
    (forall L', label (root (Frag (next p.1, L'))) |> fAR s t^-
             -> EU_M s t (Mstate (root (Frag (next p.1, L'))))) ->
    label x |> fAR s t^- -> EU_M s t (Mstate x).
  Proof.
    move => Hnext Lx.
    move: (sn_edge x) Lx. elim => {x} x _ IH Lx.
    rewrite /= in Lx. case/orP : Lx => [Lx|/andP [L1 L2]]. exact: EU0.
    case: (boolP (leaf x)) => [lf|Hx].
    + apply: leaf_root'. apply: Hnext => //. by rewrite label_root /=; bcase.
    + case: (dag_D Hx L2) => y xy Hy.
      apply: (EUs (v := Mstate y)) => //; [by rewrite /MRel lift_eq xy|exact: IH].
  Qed.

  Lemma AU_lift (s t : form) (p : DF * DC) (x : Frag p) :
    (forall L', label (root (Frag (next p.1, L'))) |> fAU s t^+
             -> AU_M s t (Mstate (root (Frag (next p.1, L'))))) ->
    label x |> fAU s t^+ -> AU_M s t (Mstate x).
  Proof.
    move => Hnext Lx.
    move: (sn_edge x) Lx. elim => {x} x _ IH Lx.
    case: (boolP (leaf x)) => [lf|Hx].
    + apply: leaf_root. apply: Hnext => //. by rewrite label_root.
    + rewrite /= in Lx. case/orP : Lx => [Lx|/andP [L1 L2]]. exact: AU0.
      apply: AUs => // [[p' y]].
      rewrite /Mstate {1}/MRel (negbTE Hx) [_ && _]/= orbF => l_edge.
      move: (liftE l_edge) => ?; subst. rewrite lift_eq in l_edge. apply: IH (l_edge) _.
      exact: supp_edge l_edge.
  Qed.

  (** Finally, we can prove that every state in the model satisfies
  all signed formulas it supports. The interesting cases are those for
  the eventualities. In either case we first show that it suffices to
  consider eventualities at root of a fragment by defering to the next
  row in the matix. Only after this we start the induction on the
  distance between the current row and the row for the eventuality
  under consideration *)

  Lemma supp_eval s (x : MD) : label (tagged x) |> s -> eval (interp' s) x.
  Proof.
    case: s x. elim => [|p|s IHs t IHt|s IHs|s IHs t IHt|s IHs t IHt] [|] x.
    - rewrite /= => inL. move: (label_lcon x). by rewrite /lcons inL.
    - by simpl.
    - done.
    - rewrite /= => inL.
      case e : (fV p^+ \in label (tagged x)); last by rewrite /MLabel /= e.
      move => _. move: (label_lcon x) => /andP [_ /allP /(_ _ e)]. by rewrite inL.
    - rewrite /=. by case/orP => [/IHs|/IHt] /=; intuition.
    - rewrite /=. case/andP => /IHs A /IHt B. by simpl in *; intuition.
    - rewrite /= -RE => HR y /MRel_R H. apply: (IHs true).
      rewrite -suppC1 /=. apply: suppC_sub H. by rewrite fsub1.
    - rewrite /=. case/MRel_D => y xy Hy. move => /(_ y xy). exact: (IHs false).
    - rewrite [supp]lock /= -lock. move: x. cofix supp_eval => x.
      rewrite /=. case/andP => [/IHt A]. case/orP => [/IHs B|B]; first exact: AR0.
      apply: ARs => //= y /MRel_R => H. apply: supp_eval.
      rewrite -suppC1. apply: suppC_sub H. by rewrite fsub1 RE.
    - move => L_x. apply: cAR_cEU. apply: EU_strengthen (IHs false) (IHt false) _ => {IHs IHt}.
      change (EU_M s t x).
      case: x L_x => p x Lx. rewrite [tagged _]/= in Lx.
      wlog ? : p x Lx / x = root (Frag p) => [W|]; subst.
        apply: EU_lift Lx => L' HL'. exact: W HL' _.
      wlog inF : / fAX (fAR s t)^- \in Fs D => [W|].
        rewrite /= classic_orb in Lx. case/orP : Lx => [?|/and3P [pt ps pX]]. exact: EU0.
        apply: W. exact: rlabel_Fs pX. 
      have Fgt0 : 0 < #|{: DF }|. apply/card_gt0P. by exists (SeqSub _ inF).
      case: p Lx => u E. move En : (dist Fgt0 u (SeqSub _ inF)) => n.
      elim: n u E En => [|n IHn] u E.
      + move/dist0 => -> {u} L. exact: EU_this. 
      + move/distS. move/IHn => {IHn} IHn. apply: EU_lift => L'. exact: IHn.
    - move => L_x. apply: AU_strengthen (IHs true) (IHt true) _ => {IHs IHt}. change (AU_M s t x).
      case: x L_x => p x Lx. rewrite [tagged _]/= in Lx.
      wlog ? : p x Lx / x = root (Frag p) => [W|]; subst.
        apply: AU_lift Lx => L' HL'. exact: W HL' _.
      wlog inF : / (fAX (fAU s t)^+ \in Fs D).
        move => W. rewrite /= classic_orb in Lx. case/orP : Lx => [?|/and3P [Lx ? px]]. exact: AU0.
        apply: W. exact: rlabel_Fs px.
      have Fgt0 : 0 < #|{: DF }|. apply/card_gt0P. by exists (SeqSub _ inF).
      case: p Lx => u. move En : (dist Fgt0 u (SeqSub _ inF)) => n.
      elim: n u En => [|n IHn] u.
      + move/dist0 => -> {u} L Lx. exact: AU_this.
      + move/distS. move/IHn => {IHn} IHn L Lx. apply: AU_lift (Lx) => L' HL'. exact: IHn.
     - move => H /=. apply: cAU_cER. apply: ER_strengthen (IHs false) (IHt false) _ => {IHs IHt}.
       move: x H. cofix supp_eval => x. rewrite /= => /andP [Lt]. case/orP => Ls; first exact: ER0.
       case: (MRel_D Ls) => y xy Ly. apply: ERs xy _. exact: Lt. exact: supp_eval.
  Qed.

  Lemma model_existence u L :
    u \in Fs D -> L \in D -> exists (M : fmodel) (w : M), forall s, L |> s -> eval (interp' s) w.
  Proof.
    move => inF inDF. exists MD.
    pose p := (SeqSub _ inF, SeqSub _ inDF). exists (Mstate (root (Frag p))).
    move => s supp_s. apply: supp_eval. by rewrite /= label_root.
  Qed.

  (** Stronger form of model existence if there is a known bound on the fragment size *)
  Lemma MD_size n : fragment_bound FD n -> #|MD| <= n * (size (Fs D) * size D).
  Proof.
    move => bound_n. rewrite card_tagged.
    apply: leq_trans (@sumn_bound n _ _) _. 
    - move => m. case/mapP => x H ->. exact: bound_n.
    - rewrite leq_mul2l size_map (eqP (tuple.enum_tupleP _)) card_prod. 
      by rewrite !card_seq_sub ?funiq // leqnn.
  Qed.

  Lemma small_model_existence u L n : fragment_bound FD n -> u \in Fs D -> L \in D -> 
     exists2 M : fmodel, #|M| <= n * (size (Fs D) * size D) & 
                 exists (w : M), forall s, L |> s -> eval (interp' s) w.
  Proof.
    move => bound_n inF inDF. exists MD; first exact: MD_size.
    pose p := (SeqSub _ inF, SeqSub _ inDF). exists (Mstate (root (Frag p))).
    move => s supp_s. apply: supp_eval. by rewrite /= label_root.
  Qed.

End ModelConstruction.
End ModelConstruction.
Import ModelConstruction.

(** Variant that emphasizes that all clauses of a demo are satsified by the same model *)

Theorem small_models S T u (inF : u \in Fs S) : 
  demo S T -> exists2 M : fmodel,
   #|M| <= 2 * size (Fs S) * (size T)^2 &
   forall C, C \in S -> exists (w : M), forall s, C |> s -> eval (interp' s) w.
Proof.
  move => H.
  pose FD := (DD_demo H).
  pose FB := DD_fragment_bound H.
  exists (MD FD) => [|C inS].
  - apply: leq_trans (MD_size FB) _.
    rewrite -!mulnA leq_mul2l mulnA [size T * _]mulnC -mulnA expnS expn1 !leq_mul2l.
    rewrite subset_size //. apply/subP. exact: demoSsubT.
  - pose p := (SeqSub _ inF, SeqSub _ inS). exists (Mstate (root (Frag FD p))).
    move => s ?. apply: supp_eval => //. by rewrite /= label_root.
Qed.

(** Unit Model *)

Definition relT {X:Type} := [rel x y : X | true].

Lemma serial_relT (X:Type) : forall x: X, exists y, relT x y.
Proof. move => x. by exists x. Qed.

Definition unit_model := FModel (fun _ => xpred0) (@serial_relT unit).