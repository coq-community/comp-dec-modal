(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.
Require Import K_def demo.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (C D : clause).

(** * Hilbert Refutations *)

Section RefPred.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Local Notation S0 := (S0 F).
  Local Notation U := (U F).
  Local Notation xaf := (fun C => [af C]).

  Definition href C := prv ([af C] ---> Bot).

  Ltac Lbase_aux := move => D; rewrite !inE; (try case/orP) =>/eqP->.
  Ltac Lbase1 := Lbase_aux; by rewrite /= ?fsubUset ?fsub1 ?powersetE ?fsubUset ?fsub1 ?inE ?ssub_refl.
  Ltac Lbase3 := Lbase_aux; rewrite /weight /= ?fsumU !fsum1 /= /sltype.f_weight /= -?(plusE,minusE);
                 apply/leP; lia.
  Ltac Lbase4 := move => L; Lbase_aux; by rewrite /sltype.supp /= ?suppCU ?suppC1 /=; bcase.

  (** The lemma below is simple but tedious to prove. The recursive structure is
  provided in the [sltype.v] (Lemma [supp_aux]) such that it can be shared between
  all formula types for which Hilbert system and support have been defined. *)

  Lemma base0P C : C \in U ->
     prv ([af C] ---> \or_(L <- base [fset D in U | literalC D] C) [af L]).
  Proof with try solve [Lbase1|Lbase3|Lbase4].
    apply: (@supp_aux _ ssub) => /= {C} ; last by move => ?; exact: sf_ssub.
    - move => [[|p|s t|s] [|]] //=; try exact: decomp_lit.
      + apply: (decomp_ab [fset [fset s^-]; [fset t^+]]) => /=...
        rewrite -[fImp s t]/(s ---> t). rewrite -> (axIO s t).
        rule axOE.
        * rewrite -> af1n. apply: (bigOI xaf). by rewrite !inE eqxx.
        * rewrite -> (af1p t) at 1. apply: (bigOI xaf). by rewrite !inE eqxx.
      + apply: (decomp_ab [fset [fset s^+; t^-]]) => /=...
        rewrite -[fImp s t]/(s ---> t). rewrite -> dmI.
        rewrite -> (af1p s),(af1n t), <- andU at 1.
        apply: (bigOI xaf). by rewrite inE.
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

  Lemma href_R2 C s : href (s^- |` R C) -> href (fAX s^- |` C).
  Proof.
    rewrite /href. do 2 rewrite -> andU,bigA1. 
    rewrite -[_ (s^-)]/(~~: s) -[_ (fAX s^-)]/(~~: AX s) => /= H.
    rewrite -> dmAX,box_request. rewrite <- axDF. rewrite <- H.
    rule axAcase. apply axDBD.
  Qed.

  Section ContextRefutations.
  Variables (S : {fset clause}) (coref_S : coref F href S).

  Lemma baseP C : C \in U ->
     prv ([af C] ---> \or_(D <- base S C) [af D]).
  Proof.
    move => inU. rewrite -> base0P => //.
    apply: bigOE => L. rewrite !inE andbC => /and3P [L1 L2 L3].
    case: (boolP (L \in S)) => LS; first by apply: (bigOI xaf); rewrite inE LS.
    case: (boolP (lcons L)) => LL; last by rewrite -> (ax_lcons LL); exact: axBE.
    have H : L \in S0 `\` S by rewrite !inE LS LL L2 L3.
    Intro. ApplyH axBE. Rev. exact: (coref_S H).
  Qed.

  Lemma href_R1 C : C \in U -> ~~ suppS S C -> href C.
  Proof. 
    rewrite /href => H1 H2. rewrite -> baseP => //.
    apply: bigOE => D. rewrite inE => /andP [D1 D2]. case:notF.
    apply: contraNT H2 => _. by apply/hasP; exists D.
  Qed.
  
  End ContextRefutations.

  Theorem href_of C : ref F C -> href C.
  Proof. elim  => *;[ apply: href_R1 | apply: href_R2]; eassumption. Qed.
 
End RefPred.

(** ** Completeness *)

Theorem informative_completeness s : 
    prv (fImp s fF)  
  + (exists2 M:fmodel, #|M| <= 2^(f_size s) & exists w:M, eval s w).
Proof.
  set F := ssub (s^+). have ? := @sfc_ssub (s^+).
  case: (@refutation_completeness F _ [fset s^+]) => //.
  - by rewrite powersetE fsub1 ssub_refl.
  - move => /href_of H. left. rewrite /href in H. rewrite <- af1p in H. exact: H.
  - move => H. right. move: H => [M] [w] /(_ (s^+) (fset11 _)) /= ? S.
    exists M; last by exists w.
    apply: leq_trans S _. by rewrite leq_exp2l ?size_ssub.
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


(** ** Small Model Theorem *)

Corollary small_models s:
  (exists (M:cmodel) (w:M), eval s w) ->
  (exists2 M:fmodel, #|M| <= 2^(f_size s) & exists w:M, eval s w).
Proof.
  case: (informative_completeness s) => // /soundness H [M] [w] w_s.
  exfalso. exact: H w_s.
Qed.


(** ** Canonicity of pruning demo *)

Lemma DD_supp_sat F C : suppS (DD F) C -> exists M : cmodel, sat M C.
Proof.
  case/hasP => D inDD /allP H.
  exists (model_of (DD F)). exists (Sub D inDD) => s inC.
  apply: supp_eval. exact: H.
Qed.

Fact DD_supp F (sfc_F : sf_closed F) (C : clause) :
  C \in U F -> reflect (exists M : cmodel, sat M C) (suppS (DD F) C).
Proof.
  move => inU. apply: introP; first exact: DD_supp_sat.
  move => H. apply: href_sound. apply: (href_of sfc_F) => //. apply: R1 => //.
  exact: coref_DD.
Qed.

Fact DD_canonical F (sfc_F : sf_closed F) (C : clause) : 
  reflect (C \in S0 F  /\ exists M : cmodel, sat M C) (C \in DD F).
Proof.
  apply: introP => [HC | HC [inS0]].
  - have inS0 : C \in S0 F. move: C HC. apply/subP. exact: prune_sub.
    split => //. apply: (@DD_supp_sat F). existsb C => //.
    rewrite suppxx //. case/sepP : inS0; bcase.
  - move: (coref_DD sfc_F) => /(_ C).
    rewrite inE HC inS0 => /(_ erefl) /href_of => H.
    apply: href_sound. exact: H.
Qed.

Proposition support_sat C :
  (exists M, sat M C) <->
  (exists D, [/\ D \in S0 (sfc C), (exists M, sat M D) & suppC D C]).
Proof. split.
  - move/(@DD_supp (sfc C) _ _). case/(_ _ _)/Wrap => //.
    case/hasP => [D /DD_canonical [//|*]]. by exists D.
  - case => D [D1 D2 D3]. apply/(@DD_supp (sfc C)) => //. 
    apply/hasP; exists D => //. by apply/DD_canonical.
Qed.
