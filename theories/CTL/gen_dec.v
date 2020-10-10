(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs
 Require Import edone bcase fset base sltype.
From CompDecModal.CTL
 Require Import CTL_def gen_def.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Hint Constructors gen : core.

(** * Decidability of Gentzen Derivability

We show decidability of gen derivability in three steps.

1) Define a syntactic universe that is closed under backward application of the rules

2) Show that this entails that derivability inside a given universe is decidable

3) Show that every annotated clause is contained in some syntactic universe 

*)

(** ** Part 1: Syntactic Universe  *)
Section gen_closure.
  Variable F : {fset sform}.
  Hypothesis sfc_F : sf_closed F.

  Lemma sf_AU s t b : ((fAU s t,b) \in F) = ((fAX (fAU s t),b) \in F).
  Proof. apply/idP/idP; move/sfc_F => //=. by bcase. Qed.

  Lemma sf_AR s t b : ((fAR s t,b) \in F) = ((fAX (fAR s t),b) \in F).
  Proof. apply/idP/idP; move/sfc_F => //=. by bcase. Qed.

  Definition Cs := powerset F.
  Definition Hs := powerset Cs.

  Definition AUs := [fset p in positives F `x` positives F | fAU p.1 p.2^+ \in F].
  Definition ARs := [fset p in negatives F `x` negatives F | fAR p.1 p.2^- \in F].

  Definition As :=
    aVoid |` [fset aAU (p,H) | p <- AUs, H <-Hs ]
         `|` [fset aAXU (p,H) | p <- AUs, H <-Hs ]
         `|` [fset aAR (p,H) | p <- ARs, H <-Hs ]
         `|` [fset aAXR (p,H) | p <- ARs, H <-Hs ].

  Definition U : {fset clause * annot} := Cs `x` As.

  Lemma AsX p H : (aAU (p, H) \in As) = (aAXU (p, H) \in As).
  Proof.
    rewrite /As !inE !eqF //= !in_fimset2 ?curryE ?in_fimset2F //; 
     split; congruence.
  Qed.

  Lemma AsAU s t H : aAU (s,t,H) \in As = [&& fAU s t^+ \in F & H \in Hs].
  Proof.
    rewrite !inE !eqF //= in_fimset2 // ; last by split; congruence.
    rewrite ![aAU _]curryE !in_fimset2F // !orbF !inE in_fsetX !posE /=.
    case e: (fAU _ _^+ \in F) => //. by case/and3P:(sfc_F e) => _ -> ->. 
  Qed.

  Lemma AsAXU s t H : aAXU (s,t,H) \in As = [&& fAX (fAU s t)^+ \in F & H \in Hs].
  Proof. by rewrite -AsX -sf_AU AsAU. Qed.

  Lemma AsX' p H : (aAR (p, H) \in As) = (aAXR (p, H) \in As).
  Proof.
    rewrite /As !inE !eqF //= !in_fimset2 ?curryE ?in_fimset2F //; 
     split; congruence.
  Qed.

  Lemma AsAR s t H : aAR (s,t,H) \in As = [&& fAR s t^- \in F & H \in Hs].
  Proof.
    rewrite !inE !eqF //= in_fimset2 // ; last by split; congruence.
    rewrite ![aAR _]curryE !in_fimset2F // !orbF !inE in_fsetX !negE /=.
    case e: (fAR _ _^- \in F) => //. by case/and3P:(sfc_F e) => _ -> ->. 
  Qed.
    
  Lemma AsAXR s t H : aAXR (s,t,H) \in As = [&& fAX (fAR s t)^- \in F & H \in Hs].
  Proof. by rewrite -AsX' -sf_AR AsAR. Qed.

  Lemma AsV : aVoid \in As.
  Proof. by rewrite !in_fsetU inE. Qed.

  Lemma AU_shift s t C H : (fAU s t^+ |` C \in Cs) && (H \in Hs) = ((C,aAU (s,t,H)) \in U).
  Proof. by rewrite in_fsetX AsAU powersetU powersetE fsub1 -/Cs; bcase. Qed.

  Lemma AXU_shift s t C H : (fAX (fAU s t)^+ |` C \in Cs) && (H \in Hs) = ((C,aAXU (s,t,H)) \in U).
  Proof. by rewrite in_fsetX AsAXU powersetU powersetE fsub1 -/Cs; bcase. Qed.

  Lemma AR_shift s t C H : (fAR s t^- |` C \in Cs) && (H \in Hs) = ((C,aAR (s,t,H)) \in U).
  Proof. by rewrite in_fsetX AsAR powersetU powersetE fsub1 -/Cs; bcase. Qed.

  Lemma AXR_shift s t C H : (fAX (fAR s t)^- |` C \in Cs) && (H \in Hs) = ((C,aAXR (s,t,H)) \in U).
  Proof. by rewrite in_fsetX AsAXR powersetU powersetE fsub1 -/Cs; bcase. Qed.

  (** U is closed under backward application of the rules *)

  Lemma subCs s C : s |` C \in Cs -> s \in F.
  Proof. by rewrite !powersetE fsubUset fsub1; bcase. Qed.

  Lemma subU t X C A :
    (sf_closed' F t -> X `<=` F) -> (t |` C,A) \in U -> (X `|` C,A) \in U.
  Proof.
    move => H. rewrite !in_fsetX ![_ && (A \in _)]andbC. case (A \in As) => //=.
    rewrite !powersetE ![_ `|` C]fsetUC !fsubUset fsub1. case (C `<=` F) => //=.
    by move/sfc_F.
  Qed.

  Lemma genU_ipl s t C E : (fImp s t^+ |` C, E) \in U -> (s^- |` C, E) \in U.
  Proof. apply: subU => /=. auto with fset. Qed.

  Lemma genU_ipr s t C E : (fImp s t^+ |` C, E) \in U -> (t^+ |` C, E) \in U.
  Proof. apply: subU => /=. auto with fset. Qed.

  Lemma genU_in s t C E : (fImp s t^- |` C, E) \in U -> ([fset s^+ , t^- & C], E) \in U.
  Proof. rewrite fsetUA. apply: subU => /=. auto with fset. Qed.

  Lemma genU_aR E : E \in As -> aR E \in As.
  Proof. case: E => //=; try by rewrite AsV. case => [[u v] H]. by rewrite AsX. Qed.
  
  Let RinU := RinU sfc_F.

  Lemma genU_AXn s C E : (fAX s^- |` C , E) \in U -> (s^- |` R C, aR E) \in U.
  Proof.
    rewrite !in_fsetX => /andP [C1 C2]. rewrite genU_aR // andbT.
    move: C1. rewrite powersetU powersetE fsub1 => /andP [/sfc_F ? /RinU ?].
    rewrite powersetU powersetE fsub1. by apply/andP.
  Qed.

  Lemma genU_AUpl s t C E : (fAU s t^+ |` C,E) \in U -> (t^+ |` C,E) \in U.
  Proof. apply: subU => /=. case/and3P => []; auto with fset. Qed.

  Lemma genU_AUpr s t C E : (fAU s t^+ |` C,E) \in U -> ([fset s^+, fAX (fAU s t)^+ & C],E) \in U.
  Proof. rewrite fsetUA. apply: subU => /=. case/and3P => []; auto with fset. Qed.

  Lemma genU_AUnl s t C E : (fAU s t^- |` C, E) \in U -> ([fset s^-, t^- & C], E) \in U.
  Proof. rewrite fsetUA. apply: subU => /=. case/and3P => []; auto with fset. Qed.

  Lemma genU_AUnr s t C E : (fAU s t^- |` C, E) \in U -> ([fset t^-, fAX (fAU s t)^- & C],E) \in U.
  Proof. rewrite fsetUA. apply: subU => /=. case/and3P => []; auto with fset. Qed.

  Lemma genU_foc s t C : (fAU s t^+ |` C , aVoid) \in U -> (C,aAU (s, t, fset0)) \in U.
  Proof. by rewrite -AU_shift in_fsetX AsV [_ \in Hs]powersetE sub0x. Qed.

  Lemma genU_AUhl s t H C : (C, aAU (s, t, H)) \in U -> (t^+ |` C, aVoid) \in U.
  Proof. rewrite -AU_shift => /andP [A _]. apply: (@genU_AUpl s). by rewrite in_fsetX AsV. Qed.

  Lemma genU_AUhr s t H C : (C, aAU (s, t, H)) \in U -> (s^+ |` C, aAXU (s, t, C |` H)) \in U.
  Proof.
    rewrite !in_fsetX -AsX !AsAU powersetU -/Cs -andbA.
    rewrite [_ |` _ \in Hs]powersetU powersetE fsub1 => /and3P [? HF ?].
    apply/and5P ; split => //. rewrite powersetE fsub1. move: (sfc_F HF) => /=. by bcase.
  Qed.

  Lemma genU_jmp C E : (C,E) \in U -> (R C, aR E) \in U.
  Proof. rewrite !in_fsetX /= => /andP [? ?]. rewrite RinU //. exact: genU_aR. Qed.

  Lemma genU_ARpl s t C E : (fAR s t^+ |` C,E) \in U -> ([fset s^+, t^+ & C],E) \in U.
  Proof. rewrite fsetUA. apply: subU => /=. case/and3P => []; auto with fset. Qed.

  Lemma genU_ARpr s t C E : (fAR s t^+ |` C,E) \in U -> ([fset t^+, fAX (fAR s t)^+ & C],E) \in U.
  Proof. rewrite fsetUA. apply: subU => /=. case/and3P => []; auto with fset. Qed.

  Lemma genU_ARnl s t C E : (fAR s t^- |` C,E) \in U -> (t^- |` C,E) \in U.
  Proof. apply: subU => /=. case/and3P => []; auto with fset. Qed.


  Lemma genU_ARnr s t C E : (fAR s t^- |` C,E) \in U -> ([fset s^-, fAX (fAR s t)^- & C],E) \in U.
  Proof. rewrite fsetUA. apply: subU => /=. case/and3P => []; auto with fset. Qed.

  Lemma genU_ARhl s t H C : (C, aAR (s, t, H)) \in U -> (t^- |` C, aVoid) \in U.
  Proof. rewrite -AR_shift => /andP [A _]. apply: (@genU_ARnl s). by rewrite in_fsetX AsV. Qed.

  Lemma genU_ARhr s t H C : (C, aAR (s, t, H)) \in U -> (s^- |` C, aAXR (s, t, C |` H)) \in U.
  Proof.
    rewrite !in_fsetX -AsX' !AsAR powersetU -/Cs -andbA.
    rewrite [_ |` _ \in Hs]powersetU powersetE fsub1 => /and3P [? HF ?].
    apply/and5P ; split => //. rewrite powersetE fsub1. move: (sfc_F HF) => /=. by bcase.
  Qed.

  Lemma genU_foc' s t C : (fAR s t^- |` C, aVoid) \in U -> (C, aAR (s, t, fset0)) \in U.
  Proof. by rewrite -AR_shift in_fsetX AsV [_ \in Hs]powersetE sub0x. Qed.

  Lemma genU_aAXR s t H C : (C, aAXR (s, t, H)) \in U -> (R C, aAR (s, t, H)) \in U.
  Proof.
    rewrite !in_fsetX AsX'. case: (aAXR _ \in _) => //; rewrite ?andbF // !andbT.
    exact: RinU.
  Qed.

  Hint Resolve genU_ipl genU_ipr genU_in genU_AXn genU_AUpl genU_AUpr genU_AUnl genU_AUnr genU_AUhl genU_AUhr genU_foc genU_jmp : core.

  (** ** Part 2: Decidability inside a universe *)

  Definition step_plain_cases (D : {fset clause * annot}) (C : clause) s E :=
    match s with
      | fF^+           => true
      | fV p^+         => fV p^- \in C
      | (fImp t1 t2)^+ => ((t1^- |` C,E) \in D) && ((t2^+ |` C,E) \in D)
      | (fImp t1 t2)^- => ([fset t1^+, t2^- & C],E) \in D
      | fAX s^-        => (s^- |` R C,aR E) \in D
      | fAU s t^+      => ((t^+ |` C,E) \in D) && (([fset s^+, fAX (fAU s t)^+ & C],E) \in D)
      | fAU s t^-      => (([fset s^-, t^- & C], E) \in D) && (([fset t^-, fAX (fAU s t)^- & C],E) \in D)
      | fAR s t^+      => (([fset s^+, t^+ & C], E) \in D) && (([fset t^+, fAX (fAR s t)^+ & C],E) \in D)
      | fAR s t^-      => ((t^- |` C,E) \in D) && (([fset s^-, fAX (fAR s t)^- & C],E) \in D)
      | _              => false
    end.

  Definition step_plain (D : {fset clause * annot}) (A : clause * annot) :=
    [some s in F, [some C in Cs, [some E in As,  (A == (s |` C, E)) && step_plain_cases D C s E]]].

  Definition step_annot (D : {fset clause * annot}) A :=
    let: (C,E) := A in
    match E with
      | aAU (s, t, H) => ((t^+ |` C, aVoid) \in D) && ((s^+ |` C, aAXU (s, t, C |` H)) \in D) || (C \in H)
      | aVoid         => [some s in positives F, [some t in positives F, [some C' in Cs,
                          (C == fAU s t^+ |` C') && ((C', aAU (s, t, fset0)) \in D)]]]
                      || [some s in negatives F, [some t in negatives F, [some C' in Cs,
                          (C == fAR s t^- |` C') && ((C', aAR (s, t, fset0)) \in D)]]]
      | aAR (s, t, H) => ((t^- |` C, aVoid) \in D) && ((s^- |` C, aAXR (s, t, C |` H)) \in D) || (C \in H)
      | aAXR(s ,t, H) => (R C,aAR (s,t,H)) \in D
      | _ => false
    end.

  Definition step_jmp (D : {fset clause * annot}) (A : clause * annot) :=
    let (C,E) := A in (R C, aR E) \in D.

  Definition step (D : {fset clause * annot}) : {fset clause * annot} :=
    [fset A in U | [|| step_plain D A, step_annot D A| step_jmp D A ]].

  Lemma bounded_step : bounded U step.
  Proof. move => C _. by rewrite /step subsep. Qed.

  Lemma mono_step : monotone step.
  Proof.
    move => D D' /subP subD_D'. apply: sep_sub (subxx _) _ => A inU.
    case/or3P => H; apply/or3P; [apply: Or31|apply: Or32|apply: Or33].
    - apply: in_sub_has H => s inF. do 2 apply: in_sub_has => ? ?.
      case (A == _) => //=.
      destruct s as [[|p|s t|s|s t|s t][|]] => //=;
        by [apply: subD_D'|case/andP => ? ?; apply/andP; split; exact: subD_D'].
    - case: A inU H => C [[[s t] H]|[[s t] H]|[[s t] H]|[[s t] H]|] //= _.
      * case e: (C \in H); rewrite ?orbF // ?orbT.
        case/andP => ? ?; apply/andP; split; exact: subD_D'.
      * case e: (C \in H); rewrite ?orbF // ?orbT.
        case/andP => ? ?; apply/andP; split; exact: subD_D'.
      * exact: subD_D'.
      * case/orP => H; [leftb|rightb]; move: H.
        do 3 apply: in_sub_has => ? ?. case (C == _) => //=. exact: subD_D'.
        do 3 apply: in_sub_has => ? ?. case (C == _) => //=. exact: subD_D'.
    - case: A inU H => C E inU H. exact: subD_D'.
  Qed.

  Lemma plainP C u E :
    step_plain_cases (fset.lfp U step) C u E -> (u |` C,E) \in U -> step_plain (fset.lfp U step) (u |` C,E).
  Proof.
    move => H. rewrite in_fsetX powersetU powersetE fsub1 -andbA -/Cs.
    case/and3P => ? ? ?.
    apply/hasP; exists u => //. apply/hasP; exists C => //. apply/hasP; exists E => //.
    by rewrite eqxx.
  Qed.

  Lemma stepP (A : clause * annot) : A \in U -> reflect (gen A) (A \in fset.lfp U step).
  Proof.
    pose lfpE := fset.lfpE mono_step bounded_step.
    move => A_in_U. apply: (iffP idP) => H.
    - move: A H {A_in_U}. apply: fset.lfp_ind => /= A D IH.
      change (clause * annot)%type in A. change {fset clause * annot} in D.
      rewrite inE => /andP [_]. case/or3P.
      + case/hasP => s _. case/hasP => C _. case/hasP => E _. case/andP => [/eqP ->].
        destruct s as [[|p|s t|s|s t|s t][|]] => //=;
          try solve [ move/IH => ?; auto | case/andP => /IH P1 /IH P2; auto ].
        move => H. by rewrite (fset1U H).
      + case: A => C. case => [[[s t] H]|[[s t] H]|[[s t] H]|[[s t] H]|] //=; try case/orP.
        * case/andP => /IH ? /IH;  auto.
        * move => inH. by rewrite (fset1U inH).
        * case/andP => /IH ? /IH;  auto.
        * move => inH. by rewrite (fset1U inH).
        * move/IH. exact: gen_aAXR.
        * case/hasP => s _. case/hasP => t _. case/hasP => C' _.
          case/andP => [/eqP -> /IH]. auto.
        * case/hasP => s _. case/hasP => t _. case/hasP => C' _.
          case/andP => [/eqP -> /IH]. auto.
      + case: A => C E /= /IH. exact: gen_jmp.
     - elim: H A_in_U => {A}.
       + move => C E inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //. exact: plainP inU.
       + move => p C E inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //.
         apply: plainP inU => /=. by rewrite !inE.
       + move => s t C E _ IHs _ IHt inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //.
         apply: plainP (inU) => /=. by rewrite IHs ?IHt //; eauto. 
       + move => s t C E _ IH inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //.
         apply: plainP (inU) => /=. by eauto.
       + move => s C E _ IH inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //.
         apply: plainP (inU) => /=. by eauto.
       + move => s t C E _ IHs _ IHt inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //.
         apply: plainP (inU) => /=. rewrite IHs ?IHt //; by eauto.
       + move => s t C E _ IHs _ IHt inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //.
         apply: plainP (inU) => /=. rewrite IHs ?IHt //; by eauto.
       + move => s t C _ IH inU. rewrite lfpE inE inU (_ : step_annot _ _ ) //=.
         move/genU_foc : (inU). case/fsetXP => ?.
         rewrite AsAU => /andP [/sfc_F /and3P [? Hs Ht] _]. rewrite -!posE in Hs Ht. leftb.
         apply/hasP; exists s => //. apply/hasP; exists t => //. apply/hasP; exists C => //.
         rewrite eqxx /=. by eauto.
       + move => s t H C _ IHs _ IHt inU. rewrite lfpE inE inU (_ : step_annot _ _ ) //=.
         rewrite IHs ?IHt //. exact: genU_AUhr. exact: genU_AUhl inU.
       + move => s t H C inU. by rewrite lfpE inE inU (_ : step_annot _ _ ) //= fset1U1.
       + move => s t C E _ IHs _ IHt inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //.
         apply/plainP: (inU) => /=. rewrite IHs ?IHt //; by auto using genU_ARpl,genU_ARpr.
       + move => s t C E _ IHs _ IHt inU. rewrite lfpE inE inU (_ : step_plain _ _ ) //.
         apply/plainP: (inU) => /=. rewrite IHs ?IHt //; by eauto using genU_ARnl,genU_ARnr.
       + move => s t C _ IH inU. rewrite lfpE inE inU (_ : step_annot _ _ ) //=. rightb.
         move/genU_foc': (inU). case/fsetXP => ?.
         rewrite AsAR => /andP [/sfc_F /and3P [? Hs Ht] _]. rewrite -!negE in Hs Ht.
         apply/hasP; exists s => //. apply/hasP; exists t => //. apply/hasP; exists C => //.
         rewrite eqxx IH //. exact: genU_foc'.
       + move => s t H C _ IHs _ IHt inU. rewrite lfpE inE inU (_ : step_annot _ _ ) //=.
         rewrite IHs ?IHt //. exact: genU_ARhr. exact: genU_ARhl inU.
       + move => s t H C inU. rewrite lfpE inE inU (_ : step_annot _ _ ) //=.
         by rewrite !inE.
       + move => s t H C _ IH inU. rewrite lfpE inE inU (_ : step_annot _ _ ) //=.
         rewrite IH //. exact: genU_aAXR.
       + move => C E _ IH inU. rewrite lfpE inE inU (_ : step_jmp _ _) //=. auto.
   Qed.

  Lemma gen_decF (A : clause * annot) : A \in U -> decidable (gen A).
  Proof. move => H. exact: decP (stepP H). Qed.

End gen_closure.

(** ** Part 3: Existence of universes for all clauses *)

Lemma plain_inU {C} : (C,aVoid) \in U (sfc C).
Proof. by rewrite in_fsetX !inE //= andbT powersetE sub_sfc. Qed.

Lemma aAU_inU {C s t H} : 
  (C,aAU (s, t, H)) \in U (sfc (fAU s t^+ |` C `|` \bigcup_(C' in H) C')).
Proof. 
  rewrite -AU_shift; last exact: closed_sfc. apply/andP; split.
  - apply: power_sub (sub_sfc _). by rewrite powersetE. 
  - rewrite powersetE. apply/subP => D inH. apply: power_sub (sub_sfc _).
    rewrite powersetE. apply: fsubsetU. by rewrite -[D]/(id D) bigU1.
Qed.

Lemma aAR_inU {C s t H} :
  (C,aAR (s, t, H)) \in U (sfc (fAR s t^- |` C `|` \bigcup_(C' in H) C')).
Proof.
  rewrite -AR_shift; last exact: closed_sfc. apply/andP; split.
  - apply: power_sub (sub_sfc _). by rewrite powersetE. 
  - rewrite powersetE. apply/subP => D inH. apply: power_sub (sub_sfc _).
    rewrite powersetE. apply: fsubsetU. by rewrite -[D]/(id D) bigU1.
Qed.

Lemma aAXU_inU {C s t H} :
  (C,aAXU (s, t, H)) \in U (sfc (fAU s t^+ |` C `|` \bigcup_(C' in H) C')).
Proof. rewrite in_fsetX -AsX -in_fsetX -/(U _). exact: aAU_inU. Qed.

Lemma aAXR_inU {C s t H} :
  (C,aAXR (s, t, H)) \in U (sfc (fAR s t^- |` C `|` \bigcup_(C' in H) C')).
Proof. rewrite in_fsetX -AsX' -in_fsetX -/(U _). exact: aAR_inU. Qed.

Lemma gen_dec A : decidable (gen A).
Proof.
  case: A => C [[[s t] H]|[[s t] H]|[[s t] H]|[[s t] H]|] /=;
  eauto using gen_decF, aAU_inU, aAXU_inU, aAR_inU, aAXR_inU, plain_inU, closed_sfc.
Qed.
