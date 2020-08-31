(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.
Require Import CTL_def dags demo hilbert relaxed_pruning.
Import IC.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (C D L : clause) (S : {fset clause}).

(** * Completeness of the Hilbert system *)

(** ** Pruning refutations to Hilbert Refutations *)

Section RefPred.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Local Notation S0 := (S0 F).
  Local Notation U := (U F).
  Local Notation xaf := (fun L => [af L]).

  Definition href C := prv ([af C] ---> Bot).

  Lemma refI1n s C : prv ([af C] ---> s) -> href (s^- |` C).
  Proof. 
    move => H. rewrite /href. rewrite -> andU,H,bigA1,axAC. 
    rule axAcase. exact: axContra.
  Qed.

  Lemma refE1n s C : href (s^- |` C) -> prv ([af C] ---> s).
  Proof.
    move => H. rewrite /href in H. rewrite -> andU,bigA1 in H. 
    Intro. ApplyH axDN. Intro. ApplyH H. by ApplyH axAI.
  Qed.

  Ltac Lbase_aux := move => D; rewrite !inE; (try case/orP) =>/eqP->.
  Ltac Lbase1 := Lbase_aux; by rewrite /= ?fsubUset ?fsub1 ?powersetE ?fsubUset ?fsub1 ?inE ?ssub_refl.
  Ltac Lbase3 := Lbase_aux; rewrite /weight /= ?fsumU !fsum1 /= /sltype.f_weight /= -?(plusE,minusE);
                 apply/leP; lia.
  Ltac Lbase4 := move => L; Lbase_aux; by rewrite /sltype.supp /= ?suppCU ?suppC1 /=; bcase.

  (** The lemma below is simple but tedious to prove. The recursive structure is
  provided in [sltype.v] (Lemma [supp_aux]) such that it can be shared between
  all formula types for which Hilbert system and support have been defined. *)

  Lemma base0P C : C \in U ->
     prv ([af C] ---> \or_(L <- base [fset D in U | literalC D] C) [af L]).
  Proof with try solve [Lbase1|Lbase3|Lbase4].
    apply: (@supp_aux _ ssub) => /= {C} ; last by move => ?; exact: sf_ssub.
    - move => [[|p|s t|s|s t|s t] [|]] //=; try exact: decomp_lit.
      - apply: (decomp_ab [fset [fset s^-]; [fset t^+]])...
        + simpl. rewrite -[fImp s t]/(s ---> t). rewrite -> (axIO s t).
          rule axOE.
          * rewrite -> af1n. apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite -> (af1p t) at 1. apply: (bigOI xaf). by rewrite !inE eqxx.
      - apply: (decomp_ab [fset [fset s^+; t^-]])...
        + rewrite -[interp _]/(~~: (s ---> t)). rewrite -> dmI.
          rewrite -> (af1p s),(af1n t), <- andU at 1.
          apply: (bigOI xaf). by rewrite inE.
      - apply: (decomp_ab [fset [fset t^+; fAX (fAR s t)^+]; [fset t^+;s^+]])...
        + simpl. rewrite -> axAReq,axAODr at 1. rule axOE.
          * rewrite -> (af1p t),(af1p s),<- andU at 1.
            apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite -> (af1p t),(af1p (AX (AR s t))),<- andU at 1.
            apply: (bigOI xaf). by rewrite !inE eqxx.
      - apply: (decomp_ab [fset [fset s^-; fAX (fAR s t)^-]; [fset t^-]])...
        + rewrite -[interp _]/(~~: AR s t). rewrite -> dmAR,axEUeq at 1. rule axOE.
          * rewrite -> (af1n t). apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite <- dmAR, <- dmAX. rewrite -> (af1n s), (af1n (AX (AR s t))), <- andU at 1.
            apply: (bigOI xaf). by rewrite !inE eqxx.
      - apply: (decomp_ab [fset [fset s^+; fAX (fAU s t)^+]; [fset t^+]])...
        + simpl. rewrite -> axAUeq at 1. rule axOE.
          * rewrite -> (af1p t) at 1. apply: (bigOI xaf). by rewrite !inE eqxx.
          * rewrite -> (af1p s),(af1p (AX (AU s t))),<- andU at 1.
            apply: (bigOI xaf). by rewrite !inE eqxx.
      - apply: (decomp_ab [fset [fset t^-; fAX (fAU s t)^-]; [fset t^-;s^-]])...
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

  Lemma ax_ReqR C D : D \in Req C -> href D -> href C.
  Proof. move/ax_Req => H rD. rewrite /href in rD *. rewrite -> H, rD. exact: axDF. Qed.

  Section EventualityRefutations.
  Variable S : {fset clause}.
  Hypothesis sub_S : S `<=` S0.
  Hypothesis coref_S : coref F href S.

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

  Lemma coref_supp C : C \in U -> ~~ suppS S C -> href C.
  Proof.
    move => inU sD. rewrite /href. rewrite -> baseP => //. apply: bigOE => D.
    case/sepP => D1 D2. apply: contraN sD. by apply/hasP; exists D.
  Qed.

  Lemma unfulfilledAU_refute s t L : L \in S -> (fAX (fAU s t)^+ \in L) ->
    ~~ fulfillsAU S S0 s t L -> mprv ([af L] ---> Bot).
  Proof.
    move => H1 H2 H3.
    pose I : {fset clause} := [fset X in S | ~~ fulfillsAU S S0 s t X].
    pose u : form := \or_(D <- I) [af D].
    rewrite /= in I u.
    suff sf : prv (u ---> ~~: fAX (fAU s t)).
    { Intro. ApplyH sf; Rev.
      - apply: (bigOI xaf). by rewrite inE H1.
      - rewrite ->(bigAE _ H2). exact: axI. }

    have HI C : C \in I -> exists2 D : clause,
                              D \in Req C & base S (s^+ |` D) `<=` I /\ ~~ suppS S (t^+ |` D).
    { rewrite inE => /andP [L1' L3'].
      rewrite /fulfillsAU fulfillsAUE inE (subP sub_S _ L1') /= in L3'.
      case/allPn : L3' => D DReq.
      rewrite negb_or => /andP [HS /hasPn HS'].
      exists D => //. split => //. apply/subP => X.
      rewrite !inE => /andP [inS sXC].
      move: (HS' _ (subP sub_S _ inS)). by rewrite inS sXC. }
    
    rewrite -> (axDNI (fAU s t)), dmAU. apply: EXR_ind.
    apply: bigOE => X XinD.
      case: (HI _ XinD) => C inReq [base1 base2].
      have XinU : X \in U. apply: (SsubU sub_S). by case/sepP : XinD.
      move/(subP sub_S) : H1. rewrite inE => /and3P [H1 _ _].
      rewrite -> (ax_Req inReq). apply: rEXn. ApplyH axAI.
      - have inU : t^+ |` C \in U.
          rewrite powersetU (ReqU sfc_F XinU inReq) powersetE fsub1 andbT.
          apply: Fsub H2 H1 => //. by rewrite /= !inE ssub_refl.
        apply: rAIL. rewrite -> (af1p t), <- andU, fsetUC. exact: coref_supp.
      - rewrite {1}/Or. apply: rAIL. rewrite -> modular_hilbert.axDN, (af1p s), <- andU, fsetUC.
        rewrite -> baseP. apply: or_sub. exact/subP.
        rewrite powersetU (ReqU sfc_F XinU inReq) powersetE fsub1 /= andbT.
        apply: Fsub H2 H1 => //. by rewrite /= !inE ssub_refl.
  Qed.

  Lemma unfulfilledAR_refute s t C : C \in S -> fAX (fAR s t)^- \in C ->
     ~~ fulfillsAR S S0 s t C -> prv ([af C] ---> Bot).
  Proof.
    move: C => C0 H1 H2 H3.
    have inF : fAX (fAR s t)^- \in F. 
      apply: Fsub (ssub_refl _) H2 _ => //. move/(subP sub_S) : H1. by case/sepP.
    pose I : {fset clause} := [fset D in S | ~~ fulfillsAR S S0 s t D].
    pose u : form := \or_(D<-I) [af D].
    rewrite /= in I u.
        
    have C0u: prv ([af C0] ---> u) by apply: (bigOI xaf); rewrite inE H1.
    have C0x: prv ([af C0] ---> ~~: AX (AR s t)) by rewrite -> (bigAE _ H2); exact: axI.
    suff sf: prv (u ---> fAX (fAR s t)) by Intro; ApplyH C0x; ApplyH sf; ApplyH C0u.

    have I1 C : C \in I -> (exists2 D : clause, D \in Req C & ~~ suppS S D)
                        \/ base S (s^- |` R C) `<=` I /\ ~~ suppS S (t^- |` R C).
    { rewrite inE => /andP [HL1 HL3].
      rewrite /fulfillsAR fulfillsARE inE !negb_and negb_or (subP sub_S _ HL1) /= in HL3.
      case/orP : HL3 => [L1|/andP[L1 L2]];[left;exact/allPn|right].
      split => //. apply/subP => X /sepP. rewrite !inE suppCU suppC1 => [[inS] /andP [sX sR]]. 
      rewrite inS /=. apply: contraNN L2 => rnk. apply/hasP; exists X => //.
      + exact: (subP sub_S).
      + by rewrite !suppCU !suppC1 !sX sR. }

    apply: AXR_ind. apply: bigOE => L LinD.
    have LinU : L \in U. apply: (SsubU sub_S). move: L LinD. apply/subP. exact: subsep.
    move/I1 : (LinD) => [[E E1 E2]|[L1 L2]].
    - suff W: prv ([af L] ---> Bot) by rewrite -> W; exact: axBE.
      apply: ax_ReqR (E1) _. apply: coref_supp E2. exact: ReqU E1.
    - rewrite -> box_request. apply: rNorm. apply: rAI.
      + apply: refE1n. apply: coref_supp => //. 
        rewrite powersetU RinU // andbT  powersetE fsub1. by case/and3P :(sfc_F (sfc_F inF)).
      + rewrite /Or. apply: rAIL => /=. rewrite -> af1n, <- andU. rewrite fsetUC.
        rewrite -> baseP; first (apply: or_sub; exact/subP).
        rewrite powersetU RinU // andbT  powersetE fsub1. by case/and3P :(sfc_F (sfc_F inF)).
  Qed.

  End EventualityRefutations.

  Lemma href_translation C : ref F C -> href C.
  Proof.
    elim => {C}; eauto using coref_supp,ax_ReqR.
    - move => S C sub0 _ coS inS. case/hasP => [[[]//[]// s t [|] //]] inC.
      exact: unfulfilledAR_refute.
    - move => S C sub0 _ coS inS. case/hasP => [[[]//[]// s t [|] //]] inC.
      exact: unfulfilledAU_refute.
  Qed.
End RefPred.

(** ** Informative Completeness and Corollaries *)

Theorem informative_completeness s :
     ( prv (~~: s) )
  +  (exists2 M : fmodel, #|M| <= f_size s * 2^(4 * f_size s + 2) & exists (w:M), eval s w).
Proof.
  pose F := ssub (s^+).
  have sfc_F := @sfc_ssub (s^+).
  have inU : [fset s^+] \in U F by rewrite powersetE fsub1 ssub_refl.
  case (ref_compl sfc_F (ssub_refl _) inU) => H;[left|right].
  - move/(href_translation sfc_F) : H. rewrite /href. by rewrite <- af1p.
  - move: H => [M M1 [w Hw]]. exists M; last by exists w; apply: (Hw _ (fset11 _)).
    apply: leq_trans M1 _. rewrite addn2 expnS mulnA [_*2]mulnC leq_mul ?size_ssub //.
    by rewrite leq_exp2l // addn1 ltnS -[4]/(2*2) -mulnA leq_mul2l size_ssub. 
Qed.


Corollary fin_completeness s : (forall (M:fmodel) (w:M), eval s w) -> prv s.
Proof.
  move => valid_s.
  case: (informative_completeness (~~: s)) => [|[M] _ [w] /=];
    [by rewrite -> modular_hilbert.axDN|by firstorder].
Qed.

Corollary prv_dec s : decidable (prv s).
Proof.
  case: (informative_completeness (~~: s)) => H;[left|right].
  - by rule axDN. 
  - move => prv_s. case: H => M _ [w]. apply. exact: (@soundness _ prv_s M).
Qed.

Corollary sat_dec s : decidable (exists (M:cmodel) (w:M), eval s w).
Proof.
  case: (informative_completeness s) => H;[right|left].
  - case => M [w] Hw. exact: (@soundness _ H M).
  - case: H => M _ [w] ?. by exists M; exists w.
Qed.

Corollary valid_dec s : decidable (forall (M:cmodel) (w:M), eval s w).
Proof.
  case (sat_dec (fImp s fF)) => /= H;[by firstorder|left => M w].
  by case (modelP s w); firstorder.
Qed.

Corollary small_models s :
  (exists (M:cmodel) (w:M), eval s w) -> 
  (exists2 M : fmodel, #|M| <= f_size s * 2^(4 * f_size s + 2) & exists (w:M), eval s w).
Proof.
  move => [M] [w] w_s. case: (informative_completeness s) => //. by move/soundness/(_ M w w_s).
Qed.
