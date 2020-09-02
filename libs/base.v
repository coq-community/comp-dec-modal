(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)

From mathcomp Require Import all_ssreflect.
Require Import Relations.
From CompDecModal.libs Require Import edone bcase.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Generic Lemmas not in Ssreflect 

This file contains a number of generic lemmas that might by added to the
Ssreflect libraries *)

Lemma forall_inPn (T : finType) (p q : pred T) : 
  reflect (exists2 x, p x & ~~ q x) (~~ [forall (x | p x), q x]).
Proof. 
  rewrite negb_forall (eq_existsb (P2 := fun x => p x && ~~ q x)) => [|x].
  exact: exists_inP. exact: negb_imply.
Qed.

(** Boolean Logic *)

Definition curry aT1 aT2 rT (f : aT1 * aT2 -> rT) a b := f (a,b).
Lemma curryE aT1 aT2 rT (f : aT1 * aT2 -> rT) a b : f (a,b) = curry f a b. done. Qed.

Lemma eqF (T : eqType) (a b : T) : a <> b -> (a == b) = false.
Proof. move => H. apply/negbTE. apply/negP => /eqP. done. Qed.

Lemma classic_orb a b : a || b = a || ~~ a && b.
Proof. bcase. Qed.

Lemma contraN (b : bool) (P : Prop) : b -> ~~ b -> P. 
Proof. by case b. Qed.

Lemma contraP (b : bool) (P : Prop) : ~~ b -> b -> P.
Proof. by case b. Qed.

(** Strong eliminations for [orb] and [has] *)

Lemma orS b1 b2 : ( b1 || b2 ) -> {b1} + {b2}.
Proof. case: b1 b2 => [|] [|] //= _; first [by left| by right]. Qed.

Lemma hasS (T : eqType) (p : pred T) s : has p s -> {a : T | a \in s & p a}.
Proof.
  case: s => // b s H. pose a := (nth b (b :: s) (find p (b :: s))).
  exists a ; by rewrite ?mem_nth -?has_find ?nth_find.
Qed.

(** Sequences *)

Lemma forall_nil (T : eqType) (P : T -> Prop) :
  (forall x, x \in nil -> P x) <-> True.
Proof. intuition. by rewrite in_nil in H0. Qed.

Lemma forall_cons (T : eqType) (P : T -> Prop) a s :
  (forall x, x \in a :: s -> P x) <-> P a /\ (forall x, x \in s -> P x).
Proof.
  firstorder using mem_head. by apply H; rewrite in_cons H0.
  rewrite in_cons in H0. case/predU1P : H0 => [->//|]. exact: H1.
Qed.

Lemma sub_behead (T : eqType) x (xs ys : seq T) :
  {subset x :: xs <= ys} -> {subset xs <= ys}.
Proof. move => sub a H. apply: sub. by rewrite inE H orbT. Qed.

Lemma sumn_bound n (s : seq nat) : 
  (forall x, x \in s -> x <= n) -> sumn s <= n * size s.
Proof. 
  elim: s => //= m s IHs H. rewrite mulnS leq_add ?H ?IHs ? mem_head //.
  move => x Hx. by rewrite H //= in_cons Hx.
Qed.

Lemma nilp_map aT rT (f : aT -> rT) s : nilp (map f s) = nilp s. 
Proof. by case: s. Qed.

Lemma in_sub_has (T:eqType) (a1 a2 : pred T) s :
  {in s, subpred a1 a2} -> has a1 s -> has a2 s.
Proof. move => H /hasP [x ins Ha]. apply/hasP. exists x => //. exact: H. Qed.

Lemma in_sub_all (T : eqType) (a1 a2 : pred T) (s : seq T) :
   {in s, subpred a1 a2} -> all a1 s -> all a2 s.
Proof. move => sub /allP H. apply/allP => x in_s. by firstorder. Qed.

Lemma sub_all_dom (T : eqType) (s1 s2 : seq T) (p : pred T) :
  {subset s1 <= s2} -> all p s2 -> all p s1.
Proof. move => sub /allP H. apply/allP => x /sub. exact: H. Qed.

Lemma sub_has_dom (T : eqType) (s1 s2 : seq T) (p : pred T) :
  {subset s2 <= s1} -> has p s2 -> has p s1.
Proof. move => H /hasP [x /H Hx] ?. by apply/hasP; exists x. Qed.

Lemma all_inP (T : eqType) (s : seq T) p q :
  reflect {in s, subpred p q} (all (fun x => p x ==> q x) s).
Proof. by apply: (iffP allP) => H x /H /implyP. Qed.

Lemma filter_subset (T: eqType) p (s : seq T) : {subset filter p s <= s}.
Proof. apply: mem_subseq. exact: filter_subseq. Qed.

Definition del (T: eqType) (x:T) := filter [pred a | a != x].

Lemma size_del (T: eqType) (x:T) s : x \in s -> size (del x s) < size s.
Proof.
  move => in_s. rewrite size_filter -(count_predC [pred a | a != x]).
  rewrite -{1}[count _ s]addn0 ltn_add2l -has_count.
  apply/hasP. exists x => //. by rewrite inE /= eqxx.
Qed.

Lemma flattenP (T : eqType) (ss : (seq (seq T))) a :
  reflect (exists2 s, s \in ss & a \in s) (a \in flatten ss).
Proof.
  elim: ss => //= [|s0 ss IHss]. rewrite in_nil. constructor => [[s]]. by rewrite in_nil.
  rewrite mem_cat. apply: (iffP orP) => [[H|/IHss [s in_ss in_s]]|[s]].
  - exists s0; by rewrite ?mem_head.
  - exists s => //. by rewrite in_cons in_ss.
  - rewrite in_cons. case/orP => [/eqP->|*]; auto. right. apply/IHss. by eexists.
Qed.

(**  Injectivity of bitmasking. Required for the size of the powerset. *)
Lemma mask_inj (T : eqType) (m1 m2 : bitseq) (s : seq T) : 
  uniq s -> size m1 == size s -> size m2 == size s -> mask m1 s =i mask m2 s -> m1 == m2.
Proof. 
  elim: s m1 m2 => [m1 m2|a s IHs [|b1 m1] [|b2 m2] // U S1 S2 E].
  - by rewrite /= !size_eq0 => _ /eqP-> /eqP->.
  - rewrite /= in U. move: U => /andP[U1 U2].
    have mask_s : a \in mask _ s = false. 
      move => b. apply: contraNF U1. exact: mem_mask.
    move: (E a). rewrite !mem_mask_cons !eqxx !andbT !mask_s !orbF => b12.
    rewrite eqseq_cons b12 eqxx IHs // => b.
    move: (E b). rewrite !mem_mask_cons. 
    case: (boolP (b == a)) => [/eqP->|_]; by rewrite ?mask_s // ?andbF.
Qed.

Arguments SeqSub [T s].

(** ** A least- and greatest fixpoints for finite types *)

Lemma iter_fix T (F : T -> T) x k n :
  iter k F x = iter k.+1 F x -> k <= n -> iter n F x = iter n.+1 F x.
Proof.
  move => e. elim: n. rewrite leqn0. by move/eqP<-.
  move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
  move/IH => /= IHe. by rewrite -!IHe.
Qed.

Section LeastFixPoint.
  Variable T : finType.
  Definition set_op := {set T} -> {set T}.
  Definition mono (F : set_op)  := forall p q : {set T} , p \subset q -> F p \subset F q.

  Variable F : {set T} -> {set T}.
  Hypothesis monoF : mono F.

  Definition lfp := iter #|T| F set0.

  Lemma lfp_ind (P : {set T} -> Type) : P set0 -> (forall s , P s -> P (F s)) -> P lfp.
  Proof.
    move => P0 Pn. rewrite /lfp. set n := #|T|. elim: n => //= n. exact: Pn.
  Qed.

  Lemma iterFsub n : iter n F set0 \subset iter n.+1 F set0.
  Proof.
    elim: n => //=; first by rewrite sub0set.
    move => n IH /=. by apply: monoF.
  Qed.

  Lemma iterFsubn m n : m <= n -> iter m F set0 \subset iter n F set0.
  Proof.
    elim : n; first by rewrite leqn0 ; move/eqP->.
    move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
    move/IH => /= IHe. apply: subset_trans IHe _. exact:iterFsub.
  Qed.

  Lemma lfpE : lfp = F lfp.
  Proof.
    suff: exists k : 'I_#|T|.+1 , iter k F set0 == iter k.+1 F set0.
      case => k /eqP E. apply: iter_fix E _. exact: leq_ord.
    apply/existsP. rewrite -[[exists _,_]]negbK negb_exists.
    apply/negP => /forallP => H.
    have/(_ #|T|.+1 (leqnn _)): forall k , k <= #|T|.+1 -> k <= #|iter k F set0|.
      elim => // n IHn Hn.
      apply: leq_ltn_trans (IHn (ltnW Hn)) _. apply: proper_card.
      rewrite properEneq iterFsub andbT. exact: (H (Ordinal Hn)).
    apply/negP. rewrite leqNgt negbK. by rewrite ltnS max_card.
  Qed.

End LeastFixPoint.

Section GreatestFixPoint.
  Variable (T : finType) (F : {set T} -> {set T}).
  Hypothesis F_mono : mono F.

  Let F' A := ~: F (~: A).

  Lemma mono_F' : mono F'.
  Proof. move =>  A B. rewrite /F' -setCS [~: F _ \subset _]setCS. exact: F_mono. Qed.
  
  Definition gfp := ~: lfp F'.

  Lemma gfpE : gfp = F gfp.
  Proof. by rewrite /gfp {1}(lfpE mono_F') setCK. Qed.

  Lemma gfp_ind (P : {set T} -> Type) : 
    P setT -> (forall s , P s -> P (F s)) -> P gfp.
  Proof. 
    move => H1 H2. rewrite /gfp /F'. 
    apply lfp_ind => [|A]; rewrite ?setC0 ?setCK //. exact: H2.
  Qed.

  Lemma gfp_ind2 (P : T -> Type) : 
    (forall x (X : {set T}), (forall y, P y -> y \in X) -> P x -> x \in F X) ->
    forall x, P x -> x \in gfp.
  Proof. move => H. apply gfp_ind => [x|*]; first by rewrite inE. exact: H. Qed.

End GreatestFixPoint.


(** ** Cyclic directed distance *)

Lemma ex_dist i j n : (0 < n) -> exists d, (d < n) && (j == i + d %[mod n]).
Proof.
  move => n0. case: (leqP i j) => H.
  - exists ((j - i) %% n). by rewrite ltn_mod n0 /= modnDmr  (subnKC H).
  - exists ((n - i %% n + j %% n) %% n). rewrite ltn_mod n0 /= modnDmr.
    rewrite -(eqn_modDr (i %% n)). set i' := i %% n. set j' := j %% n.
    rewrite -!addnA [j' + _]addnC. rewrite [n - _ +_]addnA subnK.
    by rewrite addnC modnDml eqn_modDl modnDmr modnDl.
    by rewrite ltnW // ltn_mod n0.
Qed.

Lemma unique_dist i j n d d' :
  d < n -> d' < n -> (j = i + d %[mod n]) -> (j = i + d' %[mod n]) -> d = d'.
Proof. move => Hd Hd' -> /eqP. by rewrite eqn_modDl !modn_small // => /eqP. Qed.


Section Dist.
  Variables (T : finType) (Tgt0 : 0 < #|{:T}|).

  Definition dist (s t : T) := xchoose (ex_dist (enum_rank s) (enum_rank t) Tgt0).

  Lemma distP s t : enum_rank t = enum_rank s + dist s t %[mod #|{:T}|].
  Proof.
    apply/eqP.
    by case/andP: (xchooseP (ex_dist (enum_rank s) (enum_rank t) Tgt0)).
  Qed.

  Lemma dist_ltn s t : dist s t < #|{:T}|.
  Proof. by case/andP: (xchooseP (ex_dist (enum_rank s) (enum_rank t) Tgt0)). Qed.

  Lemma dist0 (s t : T) : dist s t = 0 -> s = t.
  Proof.
    move => D0. move : (distP s t). rewrite D0 addn0.
    rewrite !modn_small ?ltn_ord //. move/ord_inj. move/enum_rank_inj.
    by symmetry.
  Qed.

  Lemma next_subproof (s : T) : (enum_rank s).+1 %% #|{: T}| < #|{: T}|.
  Proof. rewrite ltn_mod. apply/card_gt0P. by exists s. Qed.

  Definition next (s : T) := enum_val (Ordinal (next_subproof s)).

  Lemma distS (s t : T) n : dist s t = n.+1 -> dist (next s) t = n.
  Proof.
    move => Dn. move: (distP s t) => H.
    rewrite Dn -addn1 [_ + 1]addnC addnA addn1 -modnDml in H.
    move: (distP (next s) t) => Dn'. rewrite {1}/next enum_valK /= in Dn'.
    apply: unique_dist Dn' H; last rewrite -Dn ltnW //; exact: dist_ltn.
  Qed.
End Dist.

(** Finite Choice Principles *)

Lemma fin_choice_aux (T : choiceType) T' (d : T') (R : T -> T' -> Prop) (xs : seq T) :
  (forall x, x \in xs -> exists y, R x y) -> exists f , forall x, x \in xs -> R x (f x).
Proof.
  elim: xs. move => _. exists (fun _ => d) => ?. by rewrite in_nil.
  move => x s IH step.
  have/IH: forall x : T, x \in s -> exists y, R x y.
    move => z ins. apply: step. by rewrite in_cons ins orbT.
  case => f Hf. (case: (step x); first by rewrite mem_head) => y Rxy.
  exists (fun z => if z == x then y else f z) => z.
  rewrite in_cons; case/orP. move/eqP=>e. by rewrite -e ?eq_refl in Rxy *.
  case e: (z == x); first by rewrite (eqP e). exact: Hf.
Qed.

Lemma cardSmC (X : finType) m : (#|X|= m.+1) -> X.
Proof. rewrite cardE. case e: (enum X) => [|x s] //=. Qed.

Lemma fin_choice (X : finType) Y (R : X -> Y -> Prop) :
  (forall x : X , exists y , R x y) -> exists f, forall x , R x (f x).
Proof.
  case n : (#|X|) => [|m].
  - have F : X -> False. move => x. move : (max_card (pred1 x)). by rewrite card1 n.
    exists (fun x => match F x with end) => x. done.
  - move => step.
    have H : forall x, x \in enum X -> exists y, R x y. by move => *.
    case (step (cardSmC n)) => d.
    move/(fin_choice_aux d) : H => [f Hf].
    exists f => x. apply: Hf. by rewrite mem_enum.
Qed.

Lemma fin_choices (T : finType) (P : T -> Prop) (Pdec : forall x, P x \/ ~ P x) :
  exists A : {set T}, forall x, x \in A <-> P x.
Proof.
  pose R x (b :bool) := b <-> P x.
  have/fin_choice [f Hf]: forall x, exists b, R x b.
    move => x. case (Pdec x); [by exists true|by exists false].
  exists (finset f) => x. rewrite inE. exact: Hf.
Qed.


(** Some tactic notations for boolean logical connectives *)
Ltac rightb := apply/orP; right.
Ltac leftb := apply/orP; left.
Ltac existsb s := apply/hasP; exists s.


(** Types of some Axioms *)
Definition XM := forall P : Prop, P \/ ~ P.
