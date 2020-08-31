(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase base fset modular_hilbert sltype.
Require Import CTL_def dags demo hilbert.
Import IC.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (C D L : clause) (S : {fset clause}).

Arguments prune_sub [T p S].
Prenex Implicits prune_sub.

Section Prune.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Definition U := powerset F.
  Definition S0 := [fset L in U | literalC L && lcons L].

  Lemma Fsub s t X : t \in ssub s -> s \in X -> X \in U -> t \in F.
  Proof.
    move => Hsub sX. 
    rewrite powersetE => /subP /(_ _ sX) /(sf_ssub sfc_F)/subP. by apply.
  Qed.

  Lemma ReqU L C : L \in U -> C \in Req L -> C \in U.
  Proof.
    move => inU. rewrite !inE => /predU1P [->|/fimsetP[s]]; first by rewrite RinU.
    rewrite inE andbC. case: (isDiaP _) => //= t -> inL -> /=.
    rewrite powersetU RinU // andbT powersetE fsub1.
    apply: Fsub inL inU. by rewrite /= !inE ssub_refl.
  Qed.

  (** ** Fulfillment relations

  We define the fulfillment relations using fixpoint iteration. This
  turns out to be technically convenient since we never prove anything
  by induction on the fulfillment relations *)

  Section Fulfillment.
  Variable S : {fset clause}.
  Hypothesis sub_S : S `<=` S0.

  Lemma SsubU : {subset S <= U}.
  Proof. apply/subP. apply: sub_trans sub_S _. exact: subsep. Qed.

  Definition fulfillAU_step s t (X : {fset clause}) := 
    [fset Y in S | [all C in Req Y, [some L in S, suppC L (t^+ |` C) 
                                               || (suppC L (s^+ |` C)) && (L \in X)]]].
  Definition fulfillsAU s t L := L \in fset.lfp S (fulfillAU_step s t).

  Lemma bounded_fulfillAU_step s t : bounded S (fulfillAU_step s t).
  Proof. move => X _. exact: subsep. Qed.

  Lemma monotone_fulfillAU_step s t : monotone (fulfillAU_step s t).
  Proof.
    move => X Y X_sub_Y. apply: sep_sub; first exact: subxx.
    move => ? inS /=. apply: sub_all => C. apply: sub_has => L.
    case: (suppC _ _) => //=. case: (suppC _ _) => //=. exact: (subP X_sub_Y).
  Qed.

  Definition fulfillsAUE s t := 
    fset.lfpE (monotone_fulfillAU_step s t) (bounded_fulfillAU_step s t).

  Definition fulfillAR_step s t (X : {fset clause}) :=
    [fset Y in S | [some L in S, suppC L (t^- |` R Y) 
                              || suppC L (s^- |` R Y) && (L \in X)]].

  Definition fulfillsAR s t L := L \in fset.lfp S (fulfillAR_step s t).

  Lemma bounded_fulfillAR_step s t : bounded S (fulfillAR_step s t).
  Proof. move => X _. exact: subsep. Qed.

  Lemma monotone_fulfillAR_step s t : monotone (fulfillAR_step s t).
  Proof.
    move => X Y X_sub_Y. apply: sep_sub; first exact: subxx.
    move => L inS /=. apply: sub_has => C. do 2 case (suppC _ _) => //=. exact: (subP _).
  Qed.

  Definition fulfillsARE s t := 
    fset.lfpE (monotone_fulfillAR_step s t) (bounded_fulfillAR_step s t).

  End Fulfillment.

  (** * Pruning *)

  Definition pAXn L S :=
    [some C in Req L, ~~ suppS S C].
  Definition pAU C S :=
   [some u in C, if u is fAX (fAU s t)^+ then ~~ fulfillsAU S s t C else false].
  Definition pAR C S :=
   [some u in C, if u is fAX (fAR s t)^- then ~~ fulfillsAR S s t C else false].

  Definition pcond L S := [|| pAXn L S, pAU L S | pAR L S].

  Definition DD := prune pcond S0.

  (** ** Pruning yields a demo  *)

  Definition subDD : {subset DD <= U}.
  Proof. apply: SsubU. exact: prune_sub. Qed.

  Lemma AXn_complete_DD : AXn_complete DD.
  Proof.
    move => L C /pruneE. rewrite !negb_or. case/and3P => [/hasPn H _ _] /H {H L}.
    rewrite negbK. case/hasP => L ? ?. by exists L; bcase.
  Qed.

  Lemma fulfillsAU_DD s t L : L \in DD -> fAX (fAU s t)^+ \in L -> fulfillsAU DD s t L.
  Proof.
    move => inDD inL.
    move: (inDD)  => /pruneE. rewrite !negb_or. case/and3P => [_ H _].
    move/hasPn : H => /(_ _ inL). by rewrite negbK.
  Qed.

  Lemma fulfillsAR_DD s t L : L \in DD -> fAX (fAR s t)^- \in L -> fulfillsAR DD s t L.
  Proof.
    move => inDD inL.
    move: (inDD)  => /pruneE. rewrite !negb_or. case/and3P => [_ _ H].
    move/hasPn : H => /(_ _ inL). by rewrite negbK.
  Qed.

  Lemma lcons_DD C : C \in DD -> lcons C.
  Proof. move/(subP prune_sub) => /sepP []. bcase. Qed.

  (** The notion of fulfillment employed in the model construction (demo.v) is
  sightly more liberal than the notion of fulfillment employed here *)

  Lemma fulfillsAU_DD2 s t L : L \in DD -> fAX (fAU s t)^+ \in L -> demo.fulfillsAU DD DD s t L.
  Proof.
    move => H1 H2. move: (fulfillsAU_DD H1 H2) => {H1 H2}.
    apply: (fset.lfp_ind (P := fun L => demo.fulfillsAU DD DD s t L)) => C S IH.
    rewrite /demo.fulfillsAU fset.lfpE ?inE; auto using demo.bounded_fulfillAU_step,demo.monotone_fulfillAU_step.
    case: (boolP (C \in DD)) => //= ?.
    apply in_sub_all => D inRC. rewrite /suppS -has_predU /predU /=.
    apply in_sub_has => E inDD. rewrite simpl_predE. do 2 (case (suppC _ _)) => //=. exact: IH.
  Qed.

  Lemma fulfillsAR_DD2 s t L : L \in DD -> fAX (fAR s t)^- \in L -> demo.fulfillsAR DD DD s t L.
  Proof.
    move => H1 H2. move: (fulfillsAR_DD H1 H2) => {H1 H2}.
    apply: (fset.lfp_ind (P := fun L => demo.fulfillsAR DD DD s t L)) => C S IH.
    rewrite /demo.fulfillsAR fset.lfpE ?inE; auto using demo.bounded_fulfillAR_step,demo.monotone_fulfillAR_step.
    case: (boolP (C \in DD)) => //= inDD.
    have -> /= : [all D in Req C , suppS DD D].
      apply/allP => E H. apply/hasP. case: (AXn_complete_DD inDD H) => G. exists G; bcase.
    rewrite /suppS -has_predU /predU /=.
    apply in_sub_has => ? ?. rewrite simpl_predE. do 2 (case (suppC _ _)) => //=. exact: IH.
  Qed.

  (** Package everything into a demo *)
   
  Definition DEMO := @Demo DD DD lcons_DD (subP (subxx _)) AXn_complete_DD fulfillsAU_DD2 fulfillsAR_DD2.

  (** Size bounds on the Demo *)

  Lemma DD_size : size DD <= 2^(size F).
  Proof.
    rewrite -powerset_size. apply: subset_size.
    exact: sub_trans (@prune_sub _ _ _) (subsep _ _).
  Qed.

  Lemma Fs_size : size (Fs DD) <= size F.
  Proof.
    apply : subset_size. apply/subP => s. case/cupP => C /and3P[C1 _ C2].
    move/(subP prune_sub) : C1. rewrite inE => /and3P [H _ _].
    move: H. rewrite powersetE. by move/subP; apply.
  Qed.

  (** Size bound on the resulting model *)

  Lemma DD_small_model u L : u \in Fs DD -> L \in DD ->
    exists2 M : fmodel, #|M| <= size F * 2 ^ (2 * (size F) + 1)
                      & exists (w : M), forall s : sform, L |> s -> @eval M (interp s) w.
  Proof.
    move => inFs inDD.
    case: (small_models inFs DEMO) => M M1 M2. exists M; last exact: M2.
    apply: leq_trans M1 _.
    rewrite addn1 [2 ^ _]expnS mulnA [_ * 2]mulnC leq_mul //.
    - by rewrite leq_mul2l Fs_size.
    - by rewrite mulnC expnM leq_exp2r // DD_size.
  Qed.

  Lemma DD_sat u L : u \in Fs DD -> L \in DD ->
    exists (M : fmodel) (w : M), forall s : sform, L |> s -> @eval M (interp s) w.
  Proof. move => inFs inDD. case: (DD_small_model inFs inDD) => M _ M2. by exists M. Qed.

  (** ** Refutation Predicates and corefutability of the pruning demo *)

  Definition coref (ref : clause -> Prop) S :=
    forall C, C \in S0 `\` S -> ref C.

  Record refpred (ref : clause -> Prop) :=
    { R1 S C : C \in U -> coref ref S -> ~~ suppS S C -> ref C;
      R2 C D : D \in Req C -> ref D -> ref C;
      R3 S C : S `<=` S0 -> coref ref S -> C \in S -> pAR C S -> ref C;
      R4 S C : S `<=` S0 -> coref ref S -> C \in S -> pAU C S -> ref C
    }.

  Variable ref : clause -> Prop.
  Hypothesis refP : refpred ref.

  Lemma corefD1 S C : ref C -> coref ref S -> coref ref (S `\` [fset C]).
  Proof.
    move => rC coS D. rewrite !in_fsetD negb_and andb_orr -in_fsetD negbK in_fset1.
    case/orP; first exact: coS. by case/andP => [_ /eqP->].
  Qed.

  Lemma coref_DD : coref ref DD.
  Proof.
    apply: prune_ind => [C|C S]; first by rewrite inE andbN.
    case/or3P.
    - case/hasP => D D1 D2 inS corefS H. apply: corefD1 (corefS).
      apply: R2 (D1) _ => //. apply: R1 D2 => //. apply: ReqU D1. exact: (SsubU H).
    - move => H inS corefS ?. apply: corefD1 (corefS). exact: R4 H.
    - move => H inS corefS ?. apply: corefD1 (corefS). exact: R3 H.
  Qed.

  Lemma DD_refute C : C \in U -> ~~ suppS DD C -> ref C.
  Proof. move => inU. apply: R1 inU _  => //. exact: coref_DD. Qed.

End Prune.

(** * Hilbert Refutations *)

Section RefPred.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Local Notation S0 := (S0 F).
  Local Notation U := (U F).
  Local Notation xaf := (fun L => [af L]).

  Definition ref C := prv ([af C] ---> Bot).

  Ltac Lbase_aux := move => D; rewrite !inE; (try case/orP) =>/eqP->.
  Ltac Lbase1 := Lbase_aux; by rewrite /= ?fsubUset ?fsub1 ?powersetE ?fsubUset ?fsub1 ?inE ?ssub_refl.
  Ltac Lbase3 := Lbase_aux; rewrite /weight /= ?fsumU !fsum1 /= /sltype.f_weight /= -?(plusE,minusE);
                 apply/leP; lia.
  Ltac Lbase4 := move => L; Lbase_aux; by rewrite /sltype.supp /= ?suppCU ?suppC1 /=; bcase.

  (** The lemma below is simple but tedious to prove. The recursive structure is
  provided in [sltype.v] (Lemma [supp_aux]) such that it can be shared between
  all formula types for which Hilbert system and support have been defined. *)

  Lemma base0P C : C \in U ->
     prv ([af C] ---> \or_(L <- sltype.base [fset D in U | literalC D] C) [af L]).
  Proof with try solve [Lbase1|Lbase3|Lbase4].
    apply: (@supp_aux _ ssub) => /= {C} ; last by move => ?; exact: sf_ssub.
    - move => [[|p|s t|s|s t|s t] [|]] //=; try exact: decomp_lit.
      - apply: (decomp_ab (S0 := [fset [fset s^-]; [fset t^+]]))...
        + simpl. rewrite -[fImp s t]/(s ---> t). rewrite -> (axIO s t).
          rule axOE.
          * rewrite -> af1n. apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite -> (af1p t) at 1. apply: (bigOI xaf). by rewrite !inE eqxx.
      - apply: (decomp_ab (S0 := [fset [fset s^+; t^-]]))...
        + rewrite -[interp _]/(~~: (s ---> t)). rewrite -> dmI.
          rewrite -> (af1p s),(af1n t), <- andU at 1.
          apply: (bigOI xaf). by rewrite inE.
      - apply: (decomp_ab (S0 := [fset [fset t^+; fAX (fAR s t)^+]; [fset t^+;s^+]]))...
        + simpl. rewrite -> axAReq,axAODr at 1. rule axOE.
          * rewrite -> (af1p t),(af1p s),<- andU at 1.
            apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite -> (af1p t),(af1p (AX (AR s t))),<- andU at 1.
            apply: (bigOI xaf). by rewrite !inE eqxx.
      - apply: (decomp_ab (S0 := [fset [fset s^-; fAX (fAR s t)^-]; [fset t^-]]))...
        + rewrite -[interp _]/(~~: AR s t). rewrite -> dmAR,axEUeq at 1. rule axOE.
          * rewrite -> (af1n t). apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite <- dmAR, <- dmAX. rewrite -> (af1n s), (af1n (AX (AR s t))), <- andU at 1.
            apply: (bigOI xaf). by rewrite !inE eqxx.
      - apply: (decomp_ab (S0 := [fset [fset s^+; fAX (fAU s t)^+]; [fset t^+]]))...
        + simpl. rewrite -> axAUeq at 1. rule axOE.
          * rewrite -> (af1p t) at 1. apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite -> (af1p s),(af1p (AX (AU s t))),<- andU at 1.
            apply: (bigOI xaf). by rewrite !inE eqxx.
      - apply: (decomp_ab (S0 := [fset [fset t^-; fAX (fAU s t)^-]; [fset t^-;s^-]]))...
        + rewrite -[interp _]/(~~: AU s t). rewrite -> dmAU, axERu, axAODr.
          rewrite <- dmAU, <- dmAX. rewrite /=. rule axOE.
          * rewrite -> af1n, af1n, <- andU. apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite -> af1n, af1n, <- andU. apply: (bigOI xaf). by rewrite !inE eqxx.
  Qed.


  Lemma ax_lcons C : ~~ lcons C -> prv ([af C] ---> Bot).
  Proof.
    rewrite negb_and -has_predC negbK.
    case/orP => [inC|/hasP [[[] //= p [|] //]]].
    - rewrite -> (bigAE _ inC). exact: axI.
    - rewrite negbK => pP pN.
      rewrite -> (axA2 [af C]). rewrite -> (bigAE _ pP) at 2.
      rewrite -> (bigAE _ pN). simpl. rule axAcase. exact: axI.
   Qed.

  Lemma ax_Req C L : C \in Req L -> prv ([af L] ---> EX [af C]).
  Proof.
    rewrite !inE. case/predU1P => [->|].
    - rewrite -> box_request. do 2 Intro. ApplyH ax_serial. Rev.
      ApplyH axN. Rev. apply: rNorm. exact: axContra.
    - case/fimsetP => s. rewrite inE.
      move: s => [[|?|? ?|s|? ?|? ?] [|]] /andP [//=] inL _ ->.
      rewrite -> andU,(axA2 [af L]). rewrite <- af1n.
      rewrite -> (bigAE _ inL),box_request at 1.
      rewrite /=. rule axAcase. rewrite <- (axDN s) at 1. exact: axDBD.
  Qed.

  Section EventualityRefutations.
  Variable S : {fset clause}.
  Hypothesis sub_S : S `<=` S0.
  Hypothesis coref_S : coref F ref S.
  
  Lemma baseP C : C \in U ->
     prv ([af C] ---> \or_(L <- base S C) [af L]).
  Proof.
    move => inU. rewrite -> base0P => //.
    apply: bigOE => L /sepP [/sepP [L1 L2] L3].
    case: (boolP (L \in S)) => LS; first by apply: (bigOI xaf); rewrite inE LS.
    case: (boolP (lcons L)) => LL; last by rewrite -> (ax_lcons LL); exact: axBE.
    have H : L \in S0 `\` S by rewrite !inE LS L1 L2.
    Intro. ApplyH axBE. Rev. exact: (coref_S H).
  Qed.

  Lemma base_eq0 C : C \in U -> base S C == fset0 -> prv ([af C] ---> Bot).
  Proof. move => inU E. rewrite -> baseP => //. rewrite (eqP E) fset0Es big_nil. exact: axI. Qed.

  Definition AU_compound s t Ds := Ds `<=` S /\
    forall L, L \in Ds -> 
      exists2 C, C \in Req L & base S (s^+ |` C) `<=` Ds /\ base S (t^+ |` C) == fset0.

  Lemma unfulfilledAU_compound s t L : L \in S ->  ~~ fulfillsAU S s t L ->
    exists2 Ds : {fset clause}, AU_compound s t Ds & L \in Ds.
  Proof.
    move => LinS Rn.
    exists [fset X in S | ~~ fulfillsAU S s t X]; last by rewrite inE; exact/andP.
    split; first exact: subsep.
    move => L'. rewrite inE => /andP [L1' L3'].
    rewrite /fulfillsAU fulfillsAUE inE L1' /= in L3'. case/allPn : L3' => C CReq.
    move/hasPn => HS.
    exists C => //. split; [apply/subP => X|].
    + rewrite !inE => /andP [inS sXC].
      move: (HS _ inS). rewrite inS sXC negb_or /=. by case/andP.
    + apply/negPn/negP. case/emptyPn => X. rewrite inE => /andP [inS sXC].
      move: (HS _ inS). by rewrite sXC.
   Qed.

  Lemma unfulfilledAU_refute s t L : L \in S -> (fAX (fAU s t)^+ \in L) ->
    ~~ fulfillsAU S s t L -> mprv ([af L] ---> Bot).
  Proof.
    move => H1 H2 H3. case: (unfulfilledAU_compound H1 H3) => D [D1 D2] inD.
    have DER : mprv ((\or_(X <- D) [af X]) ---> EX (ER (~~:s ) (~~: t))).
      apply: EXR_ind. apply: bigOE => X XinD.
      case: (D2 _ XinD) => C inReq [base1 base2].
      have XinU : X \in U. apply: (SsubU sub_S). exact: (subP D1).
      move/(subP sub_S) : H1. rewrite inE => /and3P [H1 _ _].
      rewrite -> (ax_Req inReq). apply: rEXn. ApplyH axAI.
      - have/base_eq0/(_ base2) P : t^+ |` C \in U.
          rewrite powersetU (ReqU sfc_F XinU inReq) powersetE fsub1 andbT.
          apply: Fsub H2 H1 => //. by rewrite /= !inE ssub_refl.
        do 2 Intro. ApplyH P. rewrite -> andU, <- af1p. by ApplyH axAI.
      - rewrite {1}/Or. apply: rAIL. rewrite -> modular_hilbert.axDN, (af1p s), <- andU.
        rewrite -> baseP. rewrite fsetUC. apply: or_sub. exact/subP.
        rewrite powersetU (ReqU sfc_F XinU inReq) powersetE fsub1 /=.
        apply: Fsub H2 H1 => //. by rewrite /= !inE ssub_refl.
    rewrite -> (axA2 [af L]). rewrite -> (bigOI xaf inD) at 2. rewrite -> DER.
    rewrite -> (bigAE _ H2) => /=. rule axAcase.
    do 2 Intro. Have (EX (ER (~~: s) (~~: t) :/\: AU s t)). ApplyH axDBD. drop.
    rewrite -> axAC. ApplyH axDF. apply: rEXn. exact: axAUERF.
  Qed.

  Definition AR_compound s t Ds := Ds `<=` S /\
    (forall L, L \in Ds -> base S (s^- |` R L) `<=` Ds /\ base S (t^- |` R L) == fset0).

  Lemma unfulfilledAR_compound s t L : L \in S -> ~~ fulfillsAR S s t L ->
    exists2 Ds : {fset clause}, AR_compound s t Ds & L \in Ds.
  Proof.
    move: L => L0 H2 H3.
    exists [fset X in S | ~~ fulfillsAR S s t X].
    - split; first exact: subsep.
      move => L. rewrite inE => /andP [HL1 HL3].
      split; [apply/subP => X|]. 
      + rewrite !inE suppCU suppC1 => /and3P [inS sX sR /=].
        rewrite inS /=.
        apply: contraNN HL3 => rnk. rewrite /fulfillsAR fulfillsARE inE HL1 /=.
        apply/hasP; exists X => //. rewrite !suppCU !suppC1 !sX sR /=. by rightb.
      + apply: contraNT HL3. case/emptyPn => E /sepP [E1 E2].
        rewrite /fulfillsAR fulfillsARE inE HL1 /=.
        apply/hasP ;exists E => //. by rewrite E2.
    - by rewrite inE H2 H3.
   Qed.

  Lemma unfulfilledAR_refute s t L : L \in S -> fAX (fAR s t)^- \in L ->
     ~~ fulfillsAR S s t L -> prv ([af L] ---> Bot).
  Proof.
    move: L => L0 H1 H2 H3. case: (unfulfilledAR_compound H1 H3) => D [D1 D2] L0inD.
    have HL : prv ([af L0] ---> fAX (fAR s t) ---> Bot).
      rewrite -> (bigAE _ H2). exact: axI.
    pose u := \or_(L<-D) [af L].
    have: prv ([af L0] ---> u). exact: (bigOI xaf).
    suff: prv (u ---> fAX (fAR s t)).
      move => U1 U2. Intro. ApplyH HL. ApplyH U1. by Rev.
    move/(subP sub_S) : H1. rewrite inE => /and3P [H1 _ _].
    apply: AXR_ind.
    - apply: bigOE => L LinD. move/D2 : (LinD) => [L1 L2].
      have LinU : L \in U. apply: (SsubU sub_S). exact: (subP D1).
      rewrite -> box_request. apply: rNorm. apply: rAI.
      + move/base_eq0 : L2. case/(_ _)/Wrap => [|H].
        * rewrite powersetU RinU // andbT  powersetE fsub1.
          apply: Fsub H2 H1 => //. by rewrite /= !inE ssub_refl.
        * rewrite <- (axDN t). do 2 Intro. ApplyH H.
          rewrite fsetUC. rewrite -> andU, <- af1n. by ApplyH axAI.
      + rewrite /Or. apply: rAIL. rewrite -> (af1n s), <- andU. rewrite fsetUC.
        rewrite -> baseP. apply: or_sub; first exact/subP.
        rewrite powersetU RinU // andbT  powersetE fsub1.
        apply: Fsub H2 H1 => //. by rewrite /= !inE ssub_refl.
  Qed.

  End EventualityRefutations.

  (** Hilbert refutability is a refuation predicate *)

  Lemma refpred_ref : refpred F ref.
  Proof.
    split => [S C inU coS nsupp|||].
    - apply: base_eq0 coS _ inU _ => //. apply: contraNT nsupp.
      case/emptyPn => D. rewrite inE => /andP [? ?]. by apply/hasP; exists D.
    - move => C D /ax_Req H rD. rewrite /ref in rD *.
      rewrite -> H, rD. exact: axDF.
    - move => S C sub0 coS inS. case/hasP. do 3 (case => //). move => s t [//|] inC. 
      exact: unfulfilledAR_refute.
    - move => S C sub0 coS inS. case/hasP. do 3 (case => //). move => s t [|//] inC.  
      exact: unfulfilledAU_refute.
  Qed.
End RefPred.

(** * Main Results *)

(** Some results depend on the agreement between path semantics and inductive semantic *)
Require Import agreement.

Theorem informative_completeness s :
     {(exists2 M : fmodel, #|M| <= f_size s * 2^(4 * f_size s + 2) & exists (w:M), @eval M s w)}
   + { prv (~~: s) }.
Proof.
  pose F := ssub (s^+).
  have sfc_F := @sfc_ssub (s^+).
  case: (boolP [some C in DD F, C |> s^+]) => H;[left|right].
  - case/hasP : H => C inDD suppCs.
    have [t Ht] : exists t, t \in Fs (DD F).
      case/suppE/emptyPn : suppCs => t inC.
      exists t. apply/subP : t inC. exact: bigU1.
      case: (DD_small_model Ht inDD) => M size_M [w] /(_ _ suppCs) Hw.
      exists M; last by exists w. apply: leq_trans size_M _.
      rewrite addn2 expnS mulnA [_ * 2]mulnC leq_mul ?size_ssub // leq_exp2l //.
      by rewrite -[X in _ <= X]addn1 leq_add2r -[4]/(2 * 2) -mulnA leq_mul2l ?size_ssub.
  - rewrite /Neg. rewrite -> (af1p s). apply: (@DD_refute F _ ref) => //.
    + exact: refpred_ref.
    + rewrite powersetE fsub1. exact: ssub_refl.
    + apply: contraNN H. apply: sub_has => C. by rewrite suppC1.
Qed.

Corollary fin_completeness s : (forall (M:fmodel) w, @eval M s w) -> prv s.
Proof.
  move => valid_s.
  case: (informative_completeness (~~: s)) => [[M] _ [w] /=|]; [by firstorder|by rewrite -> modular_hilbert.axDN].
Qed.

Corollary completeness s : (forall (M:sts) w, @satisfies M s w) -> prv s.
Proof. move => valid_s. apply: fin_completeness => M w. apply/evalP2. exact: (valid_s M). Qed.

Lemma fin_path_soundness s : prv s -> forall (M : fmodel) (w:M), @satisfies M s w.
Proof. move => H M w. apply/evalP2. exact: soundness M w. Qed.

Corollary finsat_dec s : decidable (exists (M:fmodel) (w : M), @satisfies M s w).
Proof.
  case: (informative_completeness s) => H; [left|right].
  - case: H => M _ [w] /evalP2; by firstorder.
  - case => M [w]. exact: (fin_path_soundness H).
Qed.

Corollary prv_dec s : decidable (prv s).
Proof.
  case: (informative_completeness (~~: s)) => H;[right|left].
  - move => prv_s. case: H => M _ [w]. apply. exact: (@soundness _ prv_s M).
  - by rule axDN.
Qed.

Corollary fin_adeq s : prv s <-> 
  (forall (M : fmodel) (w:M), 
     #|M| <= (f_size s).+2 * 2^(4 * (f_size s).+2 + 2) -> @satisfies M s w).
Proof.
  split; first by firstorder using fin_path_soundness.
  case: (informative_completeness (~~: s)) => [[M] Hm [w] /evalP2 Hw|]; last by rewrite -> modular_hilbert.axDN.
  case/(_ M w _)/Wrap => //. by rewrite /Neg /= addn1 in Hm.
Qed.

Corollary small_model_theorem s : 
  XM -> DC -> (exists (M : sts) w, @satisfies M s w) ->
  exists2 M : fmodel, 
    #|M| <= f_size s * 2^(4 * f_size s + 2) & exists (w:M), @satisfies M s w.
Proof.
  move => xm dc [M] [w] eval_s_w.
  case: (informative_completeness s) => [[Mf] H [v] /evalP2|]; first by firstorder.
  move/(sts_path_soundness xm dc) => /(_ M w). by simpl.
Qed.

(* informative completeness for clauses -- needs unit model *)
Theorem informative_completenessC C :
    {(exists (M : fmodel) (w:M), {in C, forall s, @eval M (interp s) w})} 
  + { prv ([af C] ---> Bot) }.
Proof.
  pose F := sfc C.
  case: (boolP [some L in DD F, suppC L C]) => H;[left|right].
  - case: (fset0Vmem C) => [->|[u inC]].
    + exists unit_model; exists tt. move => ?. by rewrite inE.
    + case/hasP : H => L inDD suppLC.
      have [t Ht] : exists t, t \in Fs (DD F).
        move/(allP suppLC) : inC. case/suppE/emptyPn => t inL.
        exists t. apply/subP : t inL. exact: bigU1.
      move: (DD_sat Ht inDD) => [M] [w] M2.
      exists M. exists w => s. move/(allP suppLC). exact: M2.
  - apply: (@DD_refute F _ ref) H. 
    + exact: closed_sfc. 
    + exact: refpred_ref (@closed_sfc C).
    + rewrite powersetE. exact: sub_sfc.
Qed.