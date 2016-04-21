(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations Recdef.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Directed Acyclic Graphs *)

(** ** Termination and Transitive Closure *)

Inductive sn (X : Type) (R : X -> X -> Prop) (x : X) : Prop :=
  SN : (forall y, R x y -> sn R y) -> sn R x.

Inductive star (X : Type) (R : X -> X -> Prop) (x : X) : X -> Prop :=
| Star0 : star R x x
| StarL y z : R x z -> star R z y -> star R x y.

Definition terminates X (e : X -> X -> Prop) := forall x, sn e x.

Lemma sn_preimage T1 T2 (e1 : T1 -> T1 -> Prop) (e2 : T2 -> T2 -> Prop) (h : T1 -> T2) x :
  (forall x y, e1 x y -> e2 (h x) (h y)) -> sn e2 (h x) -> sn e1 x.
Proof.
  move eqn:(h x) => v A B. elim: B h x A eqn => {v} v _ ih h x A eqn.
  apply: SN => y /A. rewrite eqn => /ih; eauto.
Qed.

Lemma terminates_gtn : terminates (fun n m => m < n). 
Proof. 
  move => n. elim: n {-2}n (leqnn n) => [|n IHn] m Hm ;constructor. 
  - move => k Hk. by move: (leq_trans Hk Hm).
  - move => k Hk. apply: IHn. rewrite -ltnS. exact: leq_trans Hm.
Qed.

Lemma terminates_measure T (f : T -> nat) (e : T -> T -> Prop)  :
      (forall x y, e x y -> f y < f x) -> terminates e.
Proof. move => H x. exact: sn_preimage (terminates_gtn (f x)). Qed.

(** ** Finite Rooted Labeled Graphs *)

Record graph (L : Type) :=
  Graph { vertex :> finType ; edge : rel vertex ; label : vertex -> L  }.

Record rGraph (L : Type) := RGraph {
    graph_of :> graph L ;
    root : graph_of ;
    rootP x : connect (@edge _ graph_of) root x }.

Section GraphTheory.
  Variables (L : choiceType) (p : L -> {fset L} -> bool).
  Implicit Types (G : graph L) (rG : rGraph L).

  Definition erel G := (@edge _ G).
  Implicit Arguments erel []. (* Why does [Arguements erel G _ _] not work? *)

  Definition glocal G := [forall x : G, p (label x) [fset (label y) | y <- fset (edge x)]].
  Definition respects e G := [forall x : G, forall y : G, edge x y ==> e (label x) (label y)].

  Definition leaf G (x:G) := ~~ [exists y, edge x y].
End GraphTheory.

Arguments erel [L] G _ _.
Arguments existT [A] [P] x _.

(** The reachable subgraph of every element is rooted at that element *)

Definition restrict (T : finType) (P : pred T) (Tp : subType P) (e : rel T) :=
  fun x y : Tp => e (val x) (val y).
Arguments restrict [T P] Tp e x y.

Lemma connect_subtype (T : finType) (x0 : T) (e : rel T) (Tp : subFinType (connect e x0)) :
  forall x p, connect (restrict Tp e) (Sub x0 p) x.
Proof.
  move => x. case: (SubP x) => {x} x Px. 
  case/connectP : Px (Px) => pth. elim/last_ind: pth x => [x _ -> Px /= p|pth y IH x /=].
  - by rewrite (bool_irrelevance p Px) connect0.
  - rewrite rcons_path last_rcons.
    case/andP => Pth xy E Px p. subst.
    have conn : connect e x0 (last x0 pth) by apply/connectP; exists pth.
    apply: connect_trans.
    + exact: IH.
    + apply: connect1. by rewrite /restrict !SubK.
Qed.

(** Disjoint Union of finite graphs *)

Section Disjoint.
  Variables (L : Type) (I:finType) (G : I -> graph L).

  Definition lift_edge (x y : {i : I & G i}) :=
    (tag x == tag y) && edge (tagged x) (tagged_as x y).

  Lemma lift_eq (i : I) (x y : G i)  :
    lift_edge (existT i x) (existT i y) = edge x y.
  Proof. by rewrite /lift_edge /= eqxx tagged_asE. Qed.

  Lemma lift_eqn (ix iy : I) (x : G ix) (y : G iy)  :
    ix != iy -> lift_edge (existT ix x) (existT iy y) = false.
  Proof. by rewrite /lift_edge /= => /negbTE ->. Qed.

  Lemma liftE (i j : I) (x : G i) (y : G j) :
    lift_edge (existT i x) (existT j y) -> j = i.
  Proof. by case/andP => /= /eqP. Qed.

  Lemma lift_connect (i : I) (x y : G i) :
    connect (@edge _ (G i)) x y -> connect lift_edge (existT i x) (existT i y).
  Proof. case/connectP => p.
    elim: p x y => /= [x y _  ->|z p IHp x y /andP [? ?] ?]; first exact: connect0.
    apply: (@connect_trans _ _ (existT i z)); last exact: IHp.
    by rewrite connect1 // lift_eq.
  Qed.
End Disjoint.
