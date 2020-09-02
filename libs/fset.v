(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs Require Import edone bcase base.

(********************************************************************************)
(** * Finite Sets over choice types and countable types                        

This file defines a type [{fset T}] of finite sets over a type [T] with choice.
The type [{fset T}] is implemented as constructive quotient on duplicate free
lists. If [T] is a countable type, then [{fset T}], [{fset {fset T}}], etc. also
are countable types.
                                                                            
For [X,Y : {fset T}] and  [x,y : T] we define.                                  
                                                                            
[x \in X]             == [x] is an element of [X] (i.e., [{fset X}] is a [predType])

[fset0]		      == the empty set                                      

[[fset x]]	      == singleton [x]                                       

[[fset x in X | P]]     == separation (i.e, the elements of [A] satisfying [P])   

[[fset f x | x <- X]]   == replacement (i.e., map)                            

[[fset f x | x <- X,P]] == replacement (i.e., map)                            
                                                                            
[[fset x;..;y]]       == explicit set                                       

[[fset x;..;y & X]]     == [x |` (.. (y |` X))]                                 
                                                                            	      
[X `|` Y]      	      == the union of [X] and [Y]                               

[x  |` X]	      == [[fset x] `|` X]                                     

[X `&` Y]      	      == the intersection of [X] and [Y]                        
                                                                            	      
[\bigcup_(x in X) F]    == the union of all [F x] where [x] ranges over [X]         

[powerset X]          == the poweset of [X] (of type [{fset {fset T}}])         
                                                                            
[X `<=` Y] 	      == [X] is a subset of [Y]                                 

[X `<` Y] 	      == [X] is a proper subset of [Y]                          

[size X]             == the cardinality of [X] (via coercion to [seq T])
                                                                            
[fsum w X] 	      == the sum of the weights of the elements in [X]        
       		      	 ([w : T -> nat])                                
                                                                            
If [F : {fset T} -> {fset T}] is a monotone function bounded by some set      
                                                                            
[lfp F]  	     	      == the least fipoint of [F]                        

[gfp F]		      == the greatest fixpoint of [F]                    
                                                                            
We port a large protion of the lemmas from finset.v. Lemmas corresponding to
lemmas in finset.v have a 'f' prefixed to their name (or the string 'set')  
Otherwise we follow a similar naming convention:                            
                                                                            
0 -- the empty set                                                          

1 -- singleton set                                                          

I -- intersection                                                           

U -- union                                                                  

D -- difference                                                             

S -- subset                                                       

*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Nonrecursive Elimination Schemes.

(** We build finite sets over choice types and countable types by chosing a
unique, duplicate free list as canonical representative of every set. *)

Section FinSets.
  Variable T : choiceType.

  Definition fset_axiom (el : seq T) := uniq el && (el == choose (perm_eq el) el).
  Record fset_type := Fset { elements :> seq T ; _ : fset_axiom elements}.

  Definition fset_of of phant T := fset_type.
  Identity Coercion type_of_fset_of  : fset_of >-> fset_type.

  Canonical Structure fset_subType := [subType for elements by fset_type_rect].
  Canonical Structure fset_eqType := EqType _ [eqMixin of fset_type by <:].
  Canonical Structure fset_predType := PredType (fun (X : fset_type) x => nosimpl x \in elements X).
  Canonical Structure fset_choiceType := Eval hnf in ChoiceType _ [choiceMixin of fset_type by <:].
End FinSets.

(** Additional Canonical Structures in case T is a countType. 
This allows sets of sets of countTypes *)

Canonical Structure fset_countType (T : countType) :=
  Eval hnf in CountType _ [countMixin of fset_type T by <:].
Canonical Structure fset_subCountType (T : countType) :=
  Eval hnf in [subCountType of fset_type T].

(** Notation for fsets using Phant to allow the type checker to infer
the Caonical Structure for the element type *)

Notation "{ 'fset' T }" := (fset_of (Phant T))
  (at level 0, format "{ 'fset'  T }") : type_scope.

Section Extensionality.
  Variables T : choiceType.

  Lemma fset_eq X Y : X =i Y -> X == Y :> {fset T}.
  Proof.
    move: X Y => [xs ax_xs] [ys ax_ys] /= H. 
    change (xs == ys). change (xs =i ys) in H.
    case/andP : ax_xs ax_ys => xs1 /eqP -> /andP [ys1 /eqP ->].
    have ext : perm_eql xs ys by apply/permPl/uniq_perm.
    rewrite -(eq_choose ext). apply/eqP/choose_id => //. exact/permPl.
  Qed.

  Lemma fset_ext  X Y : X =i Y -> X = Y :> {fset T}.
  Proof. move => ?. apply/eqP. exact: fset_eq. Qed.
End Extensionality.

(** In conntrast to finite sets over finite types, where sets are constructed
from predicates, we contruct sets from seqences by chosing a ducplicate free
equivalent. *)

Section SetOfSeq.
  Variable (T : choiceType).

  Definition fseq  (xs : seq T) : seq T :=
    let e := undup xs in choose (perm_eq e) e.

  Lemma fseq_perm_eq xs : perm_eq (undup xs) (fseq xs).
  Proof. exact: chooseP. Qed.

  Lemma fseq_uniq xs : uniq (fseq xs).
  Proof. by rewrite -(perm_uniq (fseq_perm_eq xs)) undup_uniq. Qed.

  Lemma fseq_axiom (xs : seq T) : fset_axiom (fseq xs).
  Proof.
    rewrite /fset_axiom /= fseq_uniq /= {1}/fseq /=. apply/eqP.
    have P := permPl (fseq_perm_eq xs).
    rewrite -(eq_choose P). apply: choose_id => //. exact: fseq_perm_eq.
  Qed.

  Definition set_of xs : {fset T} := Fset (fseq_axiom xs).

  Lemma set_ofE x xs : (x \in set_of xs) = (x \in xs).
  Proof.
    rewrite -[x \in set_of xs]/(x \in fseq xs) -[x \in xs]mem_undup.
    symmetry. exact: (perm_mem (fseq_perm_eq _)).
  Qed.

  Lemma funiq (X : {fset T}) : uniq X.
  Proof. case: X => s H. by case/andP : (H). Qed.

  Lemma set_of_uniq (s : seq T) : uniq s -> perm_eq (set_of s) s.
  Proof. move => U. apply: uniq_perm_eq (funiq _) U _ => x. exact: set_ofE. Qed.
End SetOfSeq.
Global Opaque set_of.

(** ** Primitive operations 

The primitive operations for the construction of sets are separation, union,
singleton, emptyset and replacement (imset). *)

Local Notation sep_def := (fun T X p => @set_of T (filter p (elements X))).
Local Notation fsetU_def := (fun T X Y => @set_of T (elements X ++ elements Y)).
Local Notation fset1_def := (fun T x => @set_of T [:: x]).
Local Notation fset0_def := (fun T => @set_of T [::]).
Local Notation fimset_def := 
  (fun (aT rT : choiceType) f X => @set_of rT (@map aT rT f (elements X))).
Local Notation fimset2_def := (fun (aT aT' rT : choiceType) f X Y => 
  @set_of rT (@allpairs aT aT' rT f (elements X) (elements Y))).

Module Type FsetType.
  Implicit Types (T aT rT : choiceType).
  Parameter sep : forall T, {fset T} -> pred T -> {fset T}.
  Axiom sepE : sep = sep_def.
  Parameter fsetU : forall T, {fset T} -> {fset T} -> {fset T}.
  Axiom fsetUE : fsetU = fsetU_def.
  Parameter fset0_ : forall T, {fset T}.
  Axiom fset0E : fset0_ = fset0_def.
  Parameter fset1 : forall T, T-> {fset T}.
  Axiom fset1E : fset1 = fset1_def.
  Parameter fimset : forall aT rT, (aT -> rT) -> {fset aT} -> {fset rT}.
  Axiom fimsetE : fimset = fimset_def.
  Parameter fimset2 : forall aT aT' rT, (aT -> aT' -> rT) -> {fset aT} -> {fset aT'} -> {fset rT}.
  Axiom fimset2E : fimset2 = fimset2_def.
End FsetType.

Module Fset : FsetType.
  Implicit Types (T aT rT : choiceType).
  Definition sep := sep_def.
  Lemma sepE : sep = sep_def. by []. Qed.
  Definition fsetU := fsetU_def.
  Lemma fsetUE : fsetU = fsetU_def. by []. Qed.
  Definition fset0_ := fset0_def.
  Lemma fset0E : @fset0_ = fset0_def. by []. Qed.
  Definition fset1 := fset1_def.
  Lemma fset1E : fset1 = fset1_def. by []. Qed.
  Definition fimset := fimset_def.
  Lemma fimsetE : fimset = fimset_def. by []. Qed.
  Definition fimset2 := fimset2_def.
  Lemma fimset2E : fimset2 = fimset2_def. by []. Qed.
End Fset.
Export Fset.

(** ** Notations *)

Notation "[ 'fset' x 'in' X | P ]" := (sep X (fun x => P))
  (at level 0, x, X at level 99, format "[ 'fset'  x  'in'  X  |  P ]").

Definition fsetI (T : choiceType) (X Y : {fset T}) := [fset x in X | x \in Y].
Definition fsetD (T : choiceType) (X Y : {fset T}) := [fset x in X | x \notin Y].
Definition subset (T : choiceType) (X Y : {fset T}) := all (mem Y) X.
Definition proper (T : choiceType) (X Y : {fset T}) := subset X Y && ~~ subset Y X.
Definition fsetX (T T' : choiceType) (X : {fset T}) (Y : {fset T'}) := fimset2 pair X Y.


Prenex Implicits fsetU.

Notation "X `|` Y" := (fsetU X Y) (at level 52, left associativity).
Notation "X `&` Y" := (fsetI X Y) (at level 48, left associativity).
Notation "X `\` Y" := (fsetD X Y) (at level 50, left associativity).
Notation "X `<=` Y" := (subset X Y) (at level 70 ,no associativity).
Notation "X `<` Y" := (proper X Y) (at level 70, no associativity).
Notation "[ 'fset' x ]" := (fset1 x) (at level 0,x at level 99, format "[ 'fset'  x ]" ).
Notation fset0 := (@fset0_ _).
Notation "f `@` X" := (fimset f X) (at level 45).
Notation "x |` X" := ([fset x] `|` X) (at level 52, left associativity).
Notation "X `x` Y" := (fsetX X Y) (at level 44, left associativity).

(** This is left recursive to avoid having an explicit fset0 at the end *)
Notation "[ 'fset' x1 ; x2 ; .. ; xn ]" := (fsetU .. (x1 |` [fset x2]) .. [fset xn])
  (at level 0, x1 at level 99, format "[ 'fset'  x1 ;  x2 ; .. ; xn ]").
Notation "[ 'fset' x1 , x2 , .. , xn & X ]" := (x1 |` (x2 |` .. (xn |` X) ..))
  (at level 0, x1 at level 99, format "[ 'fset'  x1 ,  x2 ,  .. ,  xn  &  X ]").
Notation "[ 'all' x 'in' s , p ]" := (all (fun x => p) s)
  (at level 0, x at level 99, format "[ 'all'  x  'in'  s  ,  p ]").
Notation "[ 'some' x 'in' s , p ]" := (has (fun x => p) s)
  (at level 0, x at level 99, format "[ 'some'  x  'in'  s  ,  p ]").

Notation "[ 'fset' E | x <- X ]"  := (fimset (fun x => E) X)
  (at level 0, E, x at level 99, format "[ '[hv' 'fset'  E '/ '  |  x  <-  X ] ']'").
Notation "[ 'fset'  E | a <- A , b <- B ]" :=
  (fimset2 (fun a b => E) A B) (at level 0, E, a, b at level 99).

Definition fimset3 (aT1 aT2 aT3 rT : choiceType) (f : aT1 -> aT2 -> aT3 -> rT) X Y Z :=
  [fset f x y.1 y.2 | x <- X, y <- Y `x` Z].

Notation "[ 'fset'  E | a <- A , b <- B , c <- C ]" :=
  (fimset3 (fun a b c => E) A B C) (at level 0, E, a, b, c at level 99).

(** ** Basic Theory *)

Section OperationsTheory.
  Variable aT1 aT2 aT3 T T': choiceType.
  Implicit Types X Y Z : {fset T}.
  Implicit Types x y z : T.

  Lemma fset0F : set_of [::] = fset0 :> {fset T}. 
  Proof. by rewrite fset0E. Qed.

  Lemma fset1F x : set_of [:: x] = [fset x] :> {fset T}. 
  Proof. by rewrite fset1E. Qed.

  (** For fset0 and fset1 we know the repesentative *)
  Lemma fset1Es x : [fset x] = [:: x] :> seq T.
  Proof. rewrite fset1E. apply: perm_eq_small => //. exact: set_of_uniq. Qed.

  Lemma fset0Es : fset0 = [::] :> seq T.
  Proof. rewrite fset0E. apply: perm_eq_small => //. exact: set_of_uniq. Qed.  

  Lemma in_sep X p x : x \in [fset y in X | p y] = (x \in X) && (p x).
  Proof. by rewrite sepE set_ofE mem_filter andbC. Qed.

  Lemma in_fsetU x X Y : (x \in X `|` Y) = (x \in X) || (x \in Y).
  Proof. by rewrite fsetUE set_ofE mem_cat. Qed.

  Lemma in_fsetD x X Y : (x \in X `\` Y) = (x \in X) && (x \notin Y).
  Proof. exact: in_sep. Qed.

  Lemma in_fsetI x X Y : (x \in X `&` Y) = (x \in X) && (x \in Y).
  Proof. exact: in_sep. Qed.

  Lemma in_fset0 x : (x \in fset0) = false.
  Proof. by rewrite fset0E set_ofE. Qed.

  Lemma in_fset1 x y : (x \in [fset y]) = (x == y).
  Proof. by rewrite fset1E set_ofE inE. Qed.

  Lemma fset11 x : (x \in [fset x]).
  Proof. by rewrite in_fset1 eqxx. Qed.

  Definition in_fset := (in_sep,in_fsetU,in_fset0,fset11,in_fset1).
  Definition inE := (in_fset,inE).

  Section Laws.
    Variables X Y Z : {fset T}.

    Lemma fsetUA : X `|` (Y `|` Z) = X `|` Y `|` Z.
    Proof. apply: fset_ext => x; by rewrite !inE; bcase. Qed.

    Lemma fsetUC : X `|` Y = Y `|` X.
    Proof. apply: fset_ext => x; by rewrite !inE; bcase. Qed.

    Lemma fsetIA : X `&` (Y `&` Z) = X `&` Y `&` Z.
    Proof. apply: fset_ext => x; by rewrite !inE; bcase. Qed.

    Lemma fsetIC : X `&` Y = Y `&` X.
    Proof. apply: fset_ext => x; by rewrite !inE; bcase. Qed.

    Lemma fsetIUr : X `&` (Y `|` Z) = (X `&` Y) `|` (X `&` Z).
    Proof. apply: fset_ext => x; rewrite !inE; bcase. Qed.

    Lemma fsetIUl : (Y `|` Z) `&` X = (Y `&` X) `|` (Z `&` X).
    Proof. apply: fset_ext => x; rewrite !inE; bcase. Qed.

    Lemma fsetUIr : X `|` (Y `&` Z) = (X `|` Y) `&` (X `|` Z).
    Proof. apply: fset_ext => x; rewrite !inE; bcase. Qed.

    Lemma fsetUIl : (Y `&` Z) `|` X = (Y `|` X) `&` (Z `|` X).
    Proof. apply: fset_ext => x; rewrite !inE; bcase. Qed.

    Lemma fset1U x : x \in X -> X = x |` X.
    Proof.
      move => inX. apply/fset_ext => y. rewrite !inE.
      by case (boolP (y == x)) => //= /eqP ->.
    Qed.

    Lemma fset1U1 x : x \in x |` X.
    Proof. by rewrite inE fset11. Qed.

    Lemma fsetUP x : reflect (x \in X \/ x \in Y) (x \in X `|` Y).
    Proof. rewrite !inE. exact: (iffP orP). Qed.

    Lemma fsetU1P y x : reflect (y = x \/ y \in X) (y \in x |` X).
    Proof. rewrite !inE. exact:predU1P. Qed.
  End Laws.

  Lemma fsetUCA (A B C : {fset T}) : A `|` (B `|` C) = B `|` (A `|` C).
  Proof. by rewrite !fsetUA [A `|` B]fsetUC. Qed.

  (** Separation *)
  Lemma sepU X Y p :
    [fset x in X `|` Y | p x] = [fset x in X | p x] `|` [fset x in Y | p x].
  Proof. apply: fset_ext => x. rewrite !inE. by bcase. Qed.

  Lemma sep0 p : [fset x in fset0 | p x] = fset0 :> {fset T}.
  Proof. by rewrite sepE fset0Es fset0E. Qed.

  Lemma sep1 (a : T) (p : pred T) :
    [fset x in [fset a] | p x] = if p a then [fset a] else fset0.
  Proof. rewrite sepE fset1Es /= fun_if fset1E fset0E. by case: (p a). Qed.

  Lemma sepP (p : pred T) X x : reflect (x \in X /\ p x) (x \in [fset x in X | p x]).
  Proof. rewrite !inE. exact: andP. Qed.

  (** Empty Set *)

  Lemma fset0Vmem X : ( X = fset0 ) + { x | x \in X }.
  Proof.
    case: X => [[|x xs] ax_xs];[left|right;exists x;exact: mem_head].
    apply: fset_ext => x; by rewrite inE !unfold_in.
  Qed.

  Lemma emptyPn X : reflect (exists x , x \in X) (X != fset0).
  Proof.
    apply: introP => [|/negPn/eqP-> [x]]; last by rewrite in_fset0. 
    case (fset0Vmem X) => [ -> | [ x inX ] ]; by [rewrite eqxx |exists x].
  Qed.

  Lemma fsetU0 X : X `|` fset0 = X.
  Proof. apply: fset_ext => x; by rewrite !inE. Qed.

  Lemma fset0U X : fset0 `|` X = X.
  Proof. by rewrite fsetUC fsetU0. Qed.

  Lemma fsetI0 X : fset0 `&` X = fset0.
  Proof. apply: fset_ext => x; by rewrite !inE. Qed.

  Lemma fset0I X : X `&` fset0 = fset0.
  Proof. by rewrite fsetIC fsetI0. Qed.

  Lemma fsetD0 X : X `\` fset0 = X.
  Proof. apply: fset_ext => x. by rewrite !inE. Qed.

  (** Imset *)

  Lemma fimsetP X (f : T -> T') a : 
    reflect (exists2 x, x \in X & a = f x) (a \in f `@` X).
  Proof. rewrite fimsetE set_ofE. exact: mapP. Qed.

  Lemma in_fimset x X (f : T -> T') : (x \in X) -> (f x \in f `@` X).
  Proof. move => H. apply/fimsetP. by exists x. Qed.

  Variables (A : {fset aT1}) (B : {fset aT2}) (C : {fset aT3}).

  CoInductive fimset2_spec (rT : choiceType) f (y : rT) :  Prop :=
    fImset_spec a b : y = f a b -> a \in A -> b \in B -> fimset2_spec f y.

  Lemma fimset2P (rT : choiceType) f (y : rT) : 
    reflect (fimset2_spec f y) (y \in fimset2 f A B).
  Proof.
    rewrite fimset2E set_ofE. apply: (iffP allpairsP).
    case => [[a b] /= [? ? ?]]. exact: fImset_spec.
    case => a b *. exists (a,b). by split.
  Qed.

  Lemma mem_fimset2 (rT : choiceType) (f : aT1 -> aT2 -> rT) a b :
    a \in A -> b \in B -> f a b \in fimset2 f A B.
  Proof. move => inA inB. apply/fimset2P. exact: fImset_spec. Qed.

  Definition injective2 (f : aT1 -> aT2 -> T) :=
    forall a1 a2 b1 b2, f a1 b1 = f a2 b2 -> a1 = a2 /\ b1 = b2.
  
  Lemma in_fimset2 (f : aT1 -> aT2 -> T) a b :
    injective2 f -> (f a b \in fimset2 f A B) = (a \in A) && (b \in B).
  Proof.
    move => f_inj. apply/idP/idP; last by case/andP; exact: mem_fimset2.
    case/fimset2P => a' b' /f_inj [-> ->]. by bcase.
  Qed.

  Lemma in_fimset2F (f g : aT1 -> aT2 -> T) a b :
    (forall a b a' b', f a b <> g a' b') -> (f a b \in fimset2 g A B = false).
  Proof. move => H. apply/negbTE. apply/negP. by case/fimset2P => ? ? /H. Qed.

  (** Cross Product *)

  Lemma in_fsetX a b : ((a,b) \in A `x` B) = (a \in A) && (b \in B).
  Proof. 
    apply/fimset2P/idP => [[? ? [-> ->] -> ->] //|/andP []]. 
    exact: fImset_spec.
  Qed.

  Lemma fsetXP a b : reflect (a \in A /\ b \in B) ((a,b) \in A `x` B).
  Proof. rewrite in_fsetX. exact: andP. Qed.

  (** ** Subset *)

  Lemma subP (T1 : choiceType) (X Y : {fset T1}) : reflect {subset X <= Y} (X `<=` Y).
  Proof. exact: allP. Qed.

  Lemma subPn X Y : reflect (exists2 x, x \in X & x \notin Y) (~~ (X `<=` Y)).
  Proof. exact: allPn. Qed.

  Lemma subxx X : X `<=` X.
  Proof. exact/subP. Qed.
  Hint Resolve subxx : core.

  Lemma sub_trans Y X Z : X `<=` Y -> Y `<=` Z -> X `<=` Z.
  Proof. move => /subP ? /subP ?. by apply/subP => x; eauto. Qed.

  Lemma eqEsub X Y : (X == Y) = (X `<=` Y) && (Y `<=` X).
  Proof.
    apply/eqP/andP => [-> //|[/subP H1 /subP H2]].
    apply: fset_ext => x. apply/idP/idP; auto.
  Qed.

  Lemma sub0x X : fset0 `<=` X.
  Proof. apply/subP => x. by rewrite in_fset0. Qed.

  Lemma subx0 X : X `<=` fset0 = (X == fset0).
  Proof. by rewrite eqEsub sub0x. Qed.

  Lemma fsubUr X Y : X `<=` Y `|` X.
  Proof. apply/subP;move => x. by rewrite inE => ->. Qed.

  Lemma fsubUl X Y : X `<=` X `|` Y.
  Proof. apply/subP;move => x. by rewrite inE => ->. Qed.

  Lemma fsubIl X Y : (X `&` Y) `<=` X.
  Proof. apply/subP => x. by rewrite inE; bcase. Qed.

  Lemma fsubIr X Y : (X `&` Y) `<=` Y.
  Proof. apply/subP => x. by rewrite inE; bcase. Qed.

  Lemma fsubDl X Y : X `\` Y `<=` X.
  Proof. apply/subP;move => x. by rewrite inE ; bcase. Qed.

  Hint Resolve sub0x fset11 fsubUr fsubUl fsubDl : core.

  Lemma subsep X (P : pred T) : [fset x in X | P x] `<=` X.
  Proof. apply/subP => x. by rewrite inE; bcase. Qed.

  Lemma sep_sub X X' p q : X `<=` X' -> {in X, subpred p q} -> 
    [fset x in X | p x] `<=` [fset x in X' | q x].
  Proof.
    move => /subP subX sub_p. apply/subP => x.
    rewrite !inE => /andP [? ?]. rewrite subX //=. exact: sub_p.
  Qed.

  Lemma sep_sep X p q : [fset x in sep X p | q x] = [fset x in X | p x && q x].
  Proof. apply: fset_ext => x. by rewrite !in_sep andbA. Qed.

  Lemma sepS X Y p : X `<=` Y -> [fset x in X | p x] `<=` [fset x in Y | p x].
  Proof. move => S. by apply: sep_sub S _ => ?. Qed.

  Lemma fsubUset X Y Z : (X `|` Y `<=` Z) = (X `<=` Z) && (Y `<=` Z).
  Proof. 
    apply/idP/andP => [H | [H1 H2]].
    - by split; apply: sub_trans _ H; rewrite ?fsubUl ?fsubUr.
    - apply/subP => x. rewrite in_fset; case/orP; move: x; exact/subP.
  Qed.

  Lemma fsubUsetP X Y Z: reflect ((X `<=` Z) /\ (Y `<=` Z)) (X `|` Y `<=` Z).
  Proof. rewrite fsubUset. exact: (iffP andP). Qed.

  Lemma fsetUSU X X' Y Y' : X `<=` X' -> Y `<=` Y' -> X `|` Y `<=` X' `|` Y'.
  Proof.
    move => H1 H2.
    by rewrite fsubUset (sub_trans H1 _) ?(sub_trans H2 _) // ?fsubUl ?fsubUr.
  Qed.

  Lemma fsetSU X Y Z : X `<=` Y -> X `|` Z `<=` Y `|` Z.
  Proof. move => H. exact: fsetUSU H (subxx _). Qed.

  Lemma fsetUS X Y Z : X `<=` Y -> Z `|` X `<=` Z `|` Y.
  Proof. exact: fsetUSU (subxx _). Qed.

  Lemma fsub1 x X : ([fset x] `<=` X) = (x \in X).
  Proof. apply/subP/idP => [|H y]; first by apply. by rewrite !inE => /eqP ->. Qed.

  Lemma fsetDSS X X' Y Y' : X `<=` X' -> Y' `<=` Y -> X `\` Y `<=` X' `\` Y'.
  Proof. move=> HX /subP HY. apply: sep_sub => // x _. exact: contra (HY _). Qed.

  Lemma fsetDS X Y Z : X `<=` Y -> Z `\` Y `<=` Z `\` X.
  Proof. exact: fsetDSS. Qed.

  Definition fsetCK Y X : X `<=` Y -> Y `\` (Y `\` X) = X.
  Proof. 
    move/subP => S. apply: fset_ext => x. rewrite !inE. 
    case e: (x \in X) => //=; by rewrite ?andbT ?andbN ?S.
  Qed.  

  Lemma fsetUD X Y : Y `<=` X -> Y `|` (X `\` Y) = X.
  Proof.
    move/subP => sub. apply: fset_ext => x. rewrite !inE.
    case e: (x \in Y) => //=. by rewrite (sub _ e).
  Qed.

  Lemma fsetUD1 x X : x \in X -> x |` (X `\` [fset x]) = X.
  Proof. move => H. by rewrite fsetUD // fsub1. Qed.

  Lemma properE X Y : X `<` Y -> exists2 x, (x \in Y) & (x \notin X).
  Proof. by case/andP => _ /subPn. Qed.

  Lemma properEneq X Y : (X `<` Y) = (X != Y) && (X `<=` Y).
  Proof. rewrite /proper eqEsub. by case e : (X `<=` Y). Qed.

  Lemma properD1 X x : x \in X -> X `\` [fset x] `<` X.
  Proof.
    move => H. rewrite /proper fsubDl /=. apply/subPn.
    by exists x; rewrite ?in_fset; bcase.
  Qed.

  Lemma fproperU X Y : (X `<` Y `|` X) = ~~ (Y `<=` X).
  Proof. by rewrite /proper fsubUr /= fsubUset subxx andbT. Qed.

  Lemma fproper1 x X  : (X `<` x |` X) = (x \notin X).
  Proof. by rewrite fproperU fsub1. Qed.

  Lemma fimsetS X Y (f : T -> T') : X `<=` Y -> f `@` X `<=` f `@` Y.
  Proof. move/subP => S. apply/subP => y /fimsetP [x /S inX ->]. exact: in_fimset. Qed.

  (** Powerset - Definition suggested by Georges Gonthier *)

  Definition powerset X : {fset {fset T}} :=
    let e := elements X in
    let mT := ((size e).-tuple bool) in
      set_of (map (fun m : mT => set_of (mask m e)) (enum {: mT})).

  Lemma powersetE X Y : (X \in powerset Y) = (X `<=` Y).
  Proof.
    case: Y => ys ax_ys. rewrite /powerset !set_ofE /=.
    apply/mapP/subP => [ [ t t1 ->] x | H ] /=. 
    - rewrite set_ofE. exact: mem_mask.
    - exists [tuple of map (mem X) (in_tuple ys)]; first by rewrite !mem_enum.
      apply: fset_ext => x. rewrite set_ofE /= -filter_mask mem_filter /=.
      case: (boolP (x \in X)) => // inX. by rewrite H.
  Qed.

  Lemma powersetP X Y : reflect {subset X <= Y} (X \in powerset Y).
  Proof. rewrite powersetE. exact: subP. Qed.

  Lemma powersetU X1 X2 (X3 : {fset T}) :
    (X1 `|` X2 \in powerset X3) = (X1 \in powerset X3) && (X2 \in powerset X3).
  Proof. by rewrite !powersetE fsubUset. Qed.

  Lemma sub_power X Y Z : X `<=` Y -> Y \in powerset Z -> X \in powerset Z.
  Proof. rewrite !powersetE. exact: sub_trans. Qed.

  Lemma power_sub X Z Z' : X \in powerset Z -> Z `<=` Z' -> X \in powerset Z'.
  Proof. rewrite !powersetE. exact: sub_trans. Qed.

  Lemma power_mon X Y : X `<=` Y -> powerset X `<=` powerset Y.
  Proof. move => H. apply/subP => ? ?. exact: power_sub H. Qed.

  Lemma fsubsetU X Z Z' : (X `<=` Z) || (X `<=` Z') -> (X `<=` Z `|` Z').
  Proof. case/orP => H; exact: sub_trans H _. Qed.

  (** Quantification *)

  Lemma allU X Y p : all p (X `|` Y) = all p X && all p Y.
  Proof.
    rewrite -all_cat. apply/idP/idP; apply: sub_all_dom => ?; by rewrite mem_cat !inE.
  Qed.

  Lemma all_fset1 x p : all p [fset x] = p x.
  Proof. by rewrite fset1Es /=. Qed.

  Lemma all_fset0 (p : pred T) : all p fset0.
  Proof. by rewrite fset0Es. Qed.

  Lemma has_fset1 x p : has p [fset x] = p x.
  Proof. by rewrite fset1Es /=. Qed.

  Lemma has_fset0 (p : pred T) : has p fset0 = false.
  Proof. by rewrite fset0Es. Qed.

  Lemma all_subP (U : {fset T}) (P : pred _) :
    reflect (forall X, X `<=` U -> P X) (all P (powerset U)).
  Proof.
    apply: (iffP allP) => [H X /subP sub| H X]. apply H; exact/powersetP.
    move/powersetP => /subP. exact: H.
  Qed.

End OperationsTheory.
Hint Resolve sub0x fset11 fsubUr fsubUl fsubDl subsep : core.
Arguments subP {T1 X Y}.
Prenex Implicits subP.

Section Fimset3.
  Variables (aT1 aT2 aT3 rT : choiceType) (f : aT1 -> aT2 -> aT3 -> rT).
  Variables (A : {fset aT1}) (B : {fset aT2}) (C : {fset aT3}).

  CoInductive fimset3_spec x : Prop :=
    fImset3_spec a b c : x = f a b c -> a \in A -> b \in B -> c \in C -> fimset3_spec x.

  Lemma fimset3P x :
    reflect (fimset3_spec x) (x \in [fset f a b c | a <- A , b <- B , c <- C]).
  Proof.
    apply: (iffP (fimset2P _ _ _ _)) => [[a [b c] /= ? ? ] | [a b c -> H H1 H2] ].
    - rewrite in_fsetX => /andP [? ?]. exact: fImset3_spec.
    - apply: (@fImset_spec _ _ _ _ _ _ _ _ (b,c))  H _ => //. by rewrite in_fsetX H1 H2.
  Qed.

  Lemma mem_fimset3 a b c:
    a \in A -> b \in B -> c \in C -> f a b c \in fimset3 f A B C.
  Proof. move => H1 H2 H3. apply/fimset3P. exact: fImset3_spec. Qed.
End Fimset3.

(** TODO: if [T] is a finite type, then [{fset T}] should also be a finite type.
   This means there is a universal set and one can form unrestricted
   comprehensions. Hence, for finite T, {fset T} behaves like {set T}. *)

Definition fsetT {T : finType} := set_of (enum T).

Lemma in_fsetT (T : finType) (x : T) : x \in fsetT.
Proof. by rewrite set_ofE mem_enum. Qed.

Definition fset (T: finType) (q : pred T) := [fset x in fsetT | q x].

Lemma fsetE (T: finType) (q : pred T) x : x \in fset q = q x.
Proof. by rewrite in_sep in_fsetT. Qed.

(** ** Big Unions 

[fsetU/fset0] forms a commutative monoid. For any such monoid indexing
with a separation is equivalent to indexing on the base set and filtering. *)

Lemma big_sep (T R : choiceType) (idx : R) (op : Monoid.com_law idx) (F : T -> R) (X : {fset T}) p: 
  \big[op/idx]_(i <- [fset x in X | p x]) F i = \big[op/idx]_(i <- X | p i) F i.
Proof. 
  rewrite -(big_filter _ p). apply: perm_big.
  apply: uniq_perm_eq; try by rewrite ?filter_uniq // funiq.
  move => x. by rewrite !inE mem_filter andbC.
Qed.

Canonical Structure fsetU_law (T : choiceType) := 
  Monoid.Law (@fsetUA T) (@fset0U T) (@fsetU0 T).
Canonical Structure fsetU_comlaw (T : choiceType) := 
  Monoid.ComLaw (@fsetUC T).

Notation "\bigcup_( x 'in' X | P )  F" := 
  (\big[fsetU/fset0]_(x <- elements X | P) F) (at level 41).
Notation "\bigcup_( x 'in' X )  F" := 
  (\bigcup_( x in X | true ) F) (at level 41).


Lemma cupP (T T' : choiceType) (X : {fset T}) (P : pred T) (F : T -> {fset T'}) y :
  reflect (exists x, [&& x \in X , P x & y \in F x]) (y \in \bigcup_(x in X | P x) F x).
Proof.
  apply: (iffP idP) => [|[x] /and3P [X1 X2 X3]].
  - pose Y := [fset x in X | P x && (y \in F x)]. 
    case (fset0Vmem Y) => [Y0|[x]]; last by rewrite inE; exists x.
    rewrite (bigID (fun z => y \in F z)) -big_sep /= -/Y Y0 fset0Es big_nil fset0U.
    move => H. exfalso. move: H. apply/negP. 
    apply big_ind => [|? ?|? /andP[//]]; rewrite !inE ?negb_or; bcase.
  - by rewrite (big_rem x) //= X2 inE X3.
Qed.

Lemma bigU1 (T T' : choiceType) (X : {fset T}) (F : T -> {fset T'}) x :
  x \in X -> F x `<=` \bigcup_(x in X) F x.
Proof. move => H. apply/subP => y Hy. apply/cupP. exists x. by rewrite H Hy. Qed.

(** ** Cardinality / Size *)

Section Size.
  Variable T : choiceType.
  Implicit Types X Y : {fset T}.

  Lemma sizes0 : @size T fset0 = 0. 
  Proof. by rewrite fset0Es. Qed.

  Lemma subset_size X Y : X `<=` Y -> size X <= size Y.
  Proof. move /subP. exact: uniq_leq_size (funiq _). Qed.

  Lemma subsize_eq X Y : X `<=` Y -> size Y <= size X -> X = Y.
  Proof. move => /subP S H. apply: fset_ext. apply leq_size_perm => //. exact: funiq. Qed.

  Lemma sizes_eq0 X : (size X == 0) = (X == fset0).
  Proof. 
    apply/idP/eqP => [|->]; last by rewrite sizes0.
    rewrite -leqn0 -sizes0 => H. symmetry. exact: subsize_eq.
  Qed.

  Lemma size_gt0P X : reflect (exists x, x \in X) (0 < size X).
  Proof. rewrite lt0n sizes_eq0. exact: emptyPn. Qed.

  Lemma size_sep X (p : pred T) : size [fset x in X | p x] <= size X.
  Proof. exact: subset_size (subsep _ _). Qed.

  Lemma properW X Y : X `<` Y ->  X `<=` Y.
  Proof. by case/andP. Qed.

  Lemma proper_size X Y : X `<` Y -> size X < size Y.
  Proof.
    rewrite properEneq ltn_neqAle => /andP [H1 H2].
    rewrite subset_size // andbT eqn_leq. apply/negP => /andP [_ H].
    by rewrite (subsize_eq H2 H) eqxx in H1.
  Qed.

  Lemma size_of_uniq (T0 : choiceType) (s : seq T0) : uniq s -> size (set_of s) = size s.
  Proof. move/set_of_uniq. exact: perm_size. Qed.

  Lemma powerset_size X : size (powerset X) = 2 ^ (size X).
  Proof.
    rewrite /powerset size_of_uniq. 
    - by rewrite size_map -cardE card_tuple card_bool.
    - rewrite map_inj_uniq ?enum_uniq //.
      move: (elements X) (funiq X) => {X} s uniq_s m1 m2 => H.
      have {H} E : mask m1 s =i mask m2 s. move => x. by rewrite -set_ofE H set_ofE.
      apply/eqP. apply: mask_inj E; by rewrite // size_tuple.
  Qed.
End Size.

(** ** Weight function for sets *)

Definition const aT rT (c:rT) (f : aT -> rT) := forall x, f x = c.

Section FSum.
  Variables (T : choiceType) (w : T -> nat).
  Implicit Types X Y : {fset T}.

  Definition fdisj X Y := X `&` Y == fset0.

  Definition fsum X := \sum_(x <- X) w x.

  Lemma fsumID p X : fsum X = fsum [fset x in X | p x ] + fsum [fset x in X | ~~ p x].
  Proof. by rewrite /fsum (bigID p) /= !big_sep. Qed.

  Lemma fsum1 x : fsum [fset x] = w x.
  Proof. by rewrite /fsum fset1Es big_seq1. Qed.

  Lemma fsum0 : fsum fset0 = 0.
  Proof. by rewrite /fsum fset0Es big_nil. Qed.

  Lemma fsumS X p : fsum [fset x in X | p x] = fsum X - fsum [fset x in X | ~~ p x].
  Proof. by rewrite [fsum X](fsumID p) addnK. Qed.

  Lemma fsumI X Y : fsum (X `&` Y) = fsum X - fsum (X `\` Y).
  Proof. by rewrite fsumS. Qed.

  Lemma fsumD X Y : fsum (X `\` Y) = fsum X - fsum (X `&` Y).
  Proof.
    rewrite fsumS (_ : [fset x in X | _] = X `&` Y) //.
    apply: fset_ext => x. by rewrite !inE negbK.
  Qed.

  Lemma fsumU X Y : fsum (X `|` Y) = fsum X + fsum Y - fsum (X `&` Y).
  Proof. apply/eqP.
    rewrite [fsum (_ `|`  _)](fsumID (mem X)) /=.
    rewrite (_ : [fset x in X `|` Y | x \in X] = X);
       last by apply: fset_ext => x; rewrite !inE; bcase.
    rewrite (_ : [fset x in X `|` Y | x \notin X] = Y `\` X);
       last by apply: fset_ext => x; rewrite !inE; bcase.
    rewrite fsumD addnBA fsetIC //. by rewrite fsetIC fsumI leq_subr.
  Qed.

  Lemma fsumDsub X Y : Y `<=` X -> fsum (X `\` Y) = fsum X - fsum Y.
  Proof.
    move => /subP sub. rewrite fsumD [_ `&` _](_ : _ = Y) //. apply/eqP.
    rewrite eqEsub fsubIr /=. apply/subP => x Hx. by rewrite inE Hx (sub _ Hx).
  Qed.

  Lemma fsum_const X n : {in X, const n w} -> fsum X = n * size X.
  Proof.
    move => C. rewrite [fsum X](_ : _ = \sum_(x <- X) n).
    - by rewrite big_const_seq count_predT iter_addn_0.
    - rewrite /fsum !big_seq. exact: congr_big.
  Qed.

  Lemma fsum_eq0 X : fsum X = 0 -> {in X, const 0 w}.
  Proof.
    case: X => r i.
    suff {i} : \sum_(x <- r) w x = 0 -> {in r, const 0 w} by apply.
    move/eqP. elim: r => [_|y r IHr] //=. rewrite big_cons addn_eq0 => /andP [/eqP H /IHr H'].
    move => x. rewrite inE. case/orP => [/eqP ->|] //. exact: H'.
  Qed.

  Lemma fsum_sub X Y : X `<=` Y -> fsum X <= fsum Y.
  Proof.
    move => sub. rewrite [fsum Y](fsumID (mem X)) [Z in _ <= fsum Z + _](_ : _ = X) ?leq_addr //=.
    apply: fset_ext => x. rewrite inE. move/subP : sub => /(_ x) ?. apply/andP/idP; tauto.
  Qed.

  Lemma fsum_replace X Y Z : fsum Z < fsum Y -> Y `<=` X -> fsum (Z `|` X `\` Y) < fsum X.
  Proof.
    move => ltn sub. rewrite fsumU (fsumDsub sub). apply: leq_ltn_trans (leq_subr _ _) _.
    rewrite -ltn_subRL. apply: ltn_sub2l => //. apply: leq_trans ltn _. exact: fsum_sub.
  Qed.
End FSum.

(** cardinality versions of some fsum lemmas *)

Lemma fsum_const1 (T : choiceType) (X : {fset T}) : fsum (fun _ => 1) X = size X.
Proof. rewrite -[size X]mul1n. exact: fsum_const. Qed.

Lemma fsizeU (T : choiceType) (X Y : {fset T}) : size (X `|` Y) <= size X + size Y.
Proof. by rewrite -[size (_ `|` _)]fsum_const1 fsumU !fsum_const1 leq_subr. Qed.

Lemma fsizeU1 (T : choiceType) x (X : {fset T}) : size (x |` X) <= (size X).+1.
Proof. rewrite -addn1 addnC. apply: leq_trans (fsizeU _ _) _. by rewrite fset1Es. Qed.


Lemma fimsetU (aT rT : choiceType) (f : aT -> rT) (A B : {fset aT}) :
 [fset f x | x <- A `|` B] = [fset f x | x <- A] `|` [fset f x | x <- B].
Proof.
  apply/eqP. rewrite eqEsub fsubUset !fimsetS ?fsubUl ?fsubUr ?andbT //.
  apply/subP => x /fimsetP [a] /fsetUP [H|H] ->; by rewrite inE (in_fimset _ H).
Qed.

Lemma fimset1 (aT rT : choiceType) (f : aT -> rT) a : [fset f x | x <- [fset a]] = [fset f a].
Proof. by rewrite fimsetE fset1Es fset1E. Qed.

Lemma fimset0 (aT rT : choiceType) (f : aT -> rT) : [fset f x | x <- fset0 ] = fset0.
Proof. by rewrite fimsetE fset0Es fset0E. Qed.

Lemma fimsetU1 (aT rT : choiceType) (f : aT -> rT)  (B : {fset aT}) a :
 [fset f x | x <- a |` B] = f a |` [fset f x | x <- B].
Proof. by rewrite fimsetU fimset1. Qed.

Section Pick.
  Variables (T:choiceType) (p : pred T) (X : {fset T}).

  Definition fpick :=
    if fset0Vmem [fset x in X | p x] is inr (exist x _) then Some x else None.

  CoInductive fpick_spec : option T -> Type :=
    | fPick x : p x -> x \in X -> fpick_spec (Some x)
    | fNopick : (forall x, x \in X -> ~~ p x) -> fpick_spec None.

  Lemma fpickP : fpick_spec (fpick).
  Proof.
    rewrite /fpick; case (fset0Vmem _) => [H|[x Hx]].
    - constructor => x Hx. apply: contraT. rewrite negbK => px.
      suff: x \in fset0 by rewrite inE. rewrite -H !inE; bcase.
    - rewrite inE in Hx; constructor; bcase.
  Qed.
End Pick.

(* ** Induction Principles *)

Lemma wf_leq X (f : X -> nat) : well_founded (fun x y => f x < f y).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ f) => x y /ltP. Qed.

Lemma nat_size_ind (X:Type) (P : X -> Type) (f : X -> nat) :
   (forall x, (forall y, (f y < f x) -> P y) -> P x) -> forall x, P x.
Proof. move => H. apply: well_founded_induction_type; last exact H. exact: wf_leq. Qed.

Lemma slack_ind (T : choiceType) (P : {fset T} -> Type) (U : {fset T}):
  (forall X, (forall Y, Y `<=` U -> X `<` Y -> P Y) -> X `<=` U -> P X)-> forall X, X `<=` U -> P X.
Proof.
  move => H. apply (nat_size_ind (f := fun X => size U - size X) (P := fun X => X `<=` U -> P X)).
  move => X IH. apply: H => Y inU. move/proper_size => H. apply: IH (inU).
  apply: ltn_sub2l => //. apply: leq_trans H _. exact: subset_size.
Qed.

(** ** Fixpoints *)

Lemma iter_fix T (F : T -> T) x k n :
  iter k F x = iter k.+1 F x -> k <= n -> iter n F x = iter n.+1 F x.
Proof.
  move => e. elim: n. rewrite leqn0. by move/eqP<-.
  move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
  move/IH => /= IHe. by rewrite -!IHe.
Qed.

(** Least Fixpoints *)

Section Fixpoints.
  Variables (T : choiceType) (U : {fset T}) (F : {fset T} -> {fset T}).
  Definition monotone := forall X Y, X `<=` Y -> F X `<=` F Y.
  Definition bounded := forall X, X `<=` U -> F X `<=` U.
  Hypothesis (F_mono : monotone) (F_bound : bounded).

  Definition lfp := iter (size U) F fset0.

  Lemma lfp_ind_aux (P : {fset T} -> Type) : P fset0 -> (forall s , P s -> P (F s)) -> P lfp.
  Proof. move => P0 Pn. rewrite /lfp. elim: (size U) => //= n. exact: Pn. Qed.

  Lemma lfp_ind (P : T -> Type) :
    (forall x X, (forall y, y \in X -> P y) -> x \in F X -> P x) -> forall x, x \in lfp -> P x.
  Proof. move => H. apply lfp_ind_aux => [?| X IH x]; [by rewrite in_fset0| exact: H]. Qed.

  Lemma iterFsub1 n : iter n F fset0 `<=` iter n.+1 F fset0.
  Proof. elim: n => //= n IH. exact: F_mono. Qed.

  Lemma iterFsub n m : n <= m -> iter n F fset0 `<=` iter m F fset0.
  Proof. 
    move/subnK<-. elim: (m-n) => {m} [|m IHm]; first exact: subxx.
    apply: sub_trans IHm _. rewrite addSn. exact: iterFsub1. 
  Qed.

  Lemma iterFbound n : iter n F fset0 `<=` U.
  Proof. elim: n => //= n. exact: F_bound. Qed.

  Lemma lfpE : lfp = F lfp.
  Proof.
    suff: exists k : 'I_(size U).+1 , iter k F fset0 == iter k.+1 F fset0.
      case => k /eqP E. apply: iter_fix E _. exact: leq_ord.
    apply/existsP. apply: contraT. rewrite negb_exists => /forallP H.
    have: forall k , k <= (size U).+1 -> k <= size (iter k F fset0).
      elim => // n IHn Hn. apply: leq_ltn_trans (IHn (ltnW Hn)) _. apply: proper_size.
      rewrite properEneq iterFsub1 andbT. exact: (H (Ordinal Hn)).
    move/(_ (size U).+1 (leqnn _)). rewrite leqNgt ltnS subset_size //. 
    exact: iterFbound.
  Qed.

  Lemma lfp_level_aux x : x \in lfp -> exists n, x \in iter n.+1 F fset0.
  Proof. move => lf. exists (size U). apply/subP : lf. exact: iterFsub1. Qed.

  (** Should be [level] but this is not picked up by coqdoc *)
  Definition levl (x : T) (lx : x \in lfp) := ex_minn (lfp_level_aux lx).

  Lemma level_max (x : T) (lx : x \in lfp) : levl lx < size U.
  Proof. 
    rewrite /levl. case: (ex_minnP _) => m m1 m2. 
    move: lx. rewrite /lfp. case: (size U) => //=. by rewrite inE. 
  Qed.

  Lemma level1 (x : T) (lx : x \in lfp) : x \in iter (levl lx).+1 F fset0.
  Proof. rewrite /levl. by case: (ex_minnP _). Qed.

  Lemma level2 (x y : T) (lx : x \in lfp) : 
    y \in iter (levl lx) F fset0 -> exists ly, @levl y ly < levl lx.
  Proof. 
    move => iter_y. 
    have ly : y \in lfp. 
      move: iter_y. apply: (subP (iterFsub _)). apply: ltnW. exact: level_max.
    exists ly. rewrite {1}/levl. case: (ex_minnP _) => m m1 m2.
    move: iter_y. case e: (levl lx) => [|n]; first by rewrite /= inE.
    exact: m2. 
  Qed.
    
End Fixpoints.

(** Greatest Fixpoints *)

Section GreatestFixpoint.
  Variables (T : choiceType) (U : {fset T}) (F : {fset T} -> {fset T}).
  Hypothesis (F_mono : monotone F) (F_bound : bounded U F).

  Local Notation "~` A" := (U `\` A).

  Let F' A := ~` (F (~` A)).

  Let mono_F' : monotone F'.
  Proof. move =>  A B H. by rewrite /F' fsetDS ?F_mono ?fsetDS. Qed.

  Let bounded_F' : bounded U F'.
  Proof. move =>  A H. by rewrite /F' fsubDl. Qed.

  Definition gfp := ~` (lfp U F').

  Lemma gfpE : gfp = F gfp.
  Proof. by rewrite /gfp {1}(lfpE _) ?fsetCK ?F_bound. Qed.

  Lemma gfp_ind_aux (P : {fset T} -> Type) : P U -> (forall s , P s -> P (F s)) -> P gfp.
  Proof. 
    move => PU Pn. rewrite /gfp /F'. 
    apply lfp_ind_aux => [|A]; rewrite ?fsetD0 ?fsetCK ?F_bound //. exact: Pn.
  Qed.
    
  Lemma gfp_ind (P : T -> Type) :
    (forall x X, (forall y, y \in U -> P y -> y \in X) -> P x -> x \in F X) -> 
    forall x, x \in U -> P x -> x \in gfp.
  Proof. move => H. apply gfp_ind_aux => [//|*]. exact: H. Qed.
End GreatestFixpoint.


(** ** Reachability withing a set *)

Section FsetConnect.
  Variables (T : choiceType) (S : {fset T}) (e : rel T).

  Definition restrict := [rel a b : seq_sub S | e (val a) (val b)].

  Definition connect_in (x y : T) :=
    [exists a, exists b, [&& val a == x, val b == y & connect restrict a b]].

  Lemma connect_in0 (x : T) : x \in S -> connect_in x x.
  Proof. move => inS. do 2 (apply/existsP; exists (SeqSub x inS)). by rewrite /= eqxx connect0. Qed.

  Lemma connect_in1 (x y : T) : x \in S -> y \in S -> e x y -> connect_in x y.
  Proof.
    move => x_inS y_inS xy.
    apply/existsP; exists (SeqSub _ x_inS). apply/existsP; exists (SeqSub _ y_inS).
    by rewrite /= !eqxx connect1.
  Qed.

  Lemma connect_in_trans (z x y : T) : connect_in x z -> connect_in z y -> connect_in x y.
  Proof.
    rewrite /connect_in.
    move => /existsP [a] /existsP [b] /and3P [/eqP ? /eqP ? ?] /existsP [?] /existsP [c] /and3P [/eqP H /eqP ? R].
    subst. apply/existsP; exists a. apply/existsP; exists c. rewrite !eqxx /=.
    apply: connect_trans _ R. by rewrite (val_inj H).
  Qed.

  Lemma connect_inP x y :
    reflect (exists p : seq T, [/\ all (mem S) (x::p), path e x p & y = last x p])
            (connect_in x y).
  Proof.
    apply: (iffP idP).
    - case/existsP => a. case/existsP => b. case/and3P => [/eqP ? /eqP ?]. subst.
      case/connectP => p P1 P2. exists (map val p). rewrite /= ssvalP /=.
      elim: p a P1 P2 => //= [? _ -> //| c p IHp a]. case/andP => [He ?] ?.
      rewrite ssvalP He //=. exact: IHp.
    - case => p. elim: p x => /=.
      + move => x [/andP [inS _] ? ->]. exact: connect_in0.
      + move => z p IHp x [/and3P [x_inS y_inS ?] /andP [? ?] ?].
        apply: (@connect_in_trans z); first exact: connect_in1. by apply: IHp; rewrite y_inS.
  Qed.
End FsetConnect.


(** ** Maximal extensions *)

Section Maximal.
  Variable (T : choiceType) (U : {fset T}) (P : pred {fset T}).

  Definition maximalb (M : {fset T}) := P M && [all Y in powerset U, (M `<` Y) ==> ~~ P Y].
  Definition maximal (M : {fset T}) := P M /\ forall Y, Y `<=` U -> M `<` Y -> ~~ P Y.

  Lemma maximalP M : reflect (maximal M) (maximalb M).
  Proof.
    apply: (iffP andP) => [[H1 /all_subP H2]|[H1 H2]]; split => //.
    - move => Y inU. apply/implyP. exact: H2.
    - apply/all_subP => Y inU. apply/implyP. exact: H2.
  Qed.

  Lemma ex_max X : X `<=` U -> P X -> exists M, [/\ X `<=` M , M `<=` U & maximal M].
  Proof.
    move: X. apply: slack_ind => X IH inU pX.
    case/boolP :(maximalb X) => [/maximalP|]; first by exists X; rewrite subxx.
    rewrite negb_and pX. case/allPn => Y. rewrite powersetE negb_imply negbK => H1 /andP [H2 pY].
    case: (IH _ H1 H2 pY) => M [YM MU Hm]. exists M. split => //. apply: (sub_trans _ YM). exact: properW.
  Qed.
End Maximal.

(** ** Pruning *)

Section Pruning.
  Variables (T:choiceType) (p : T -> {fset T} -> bool).
  Implicit Types (S : {fset T}).

  Function prune S {measure size} :=
    if fpick (p^~ S) S is Some x then prune (S `\` [fset x]) else S.
  Proof.
    move => S x. case: (fpickP _) => // ? Hp inS [?]. subst.
    apply/leP. apply: proper_size. exact: properD1.
  Qed.

  Lemma prune_myind (P : {fset T} -> Type) S :
    P S ->
    (forall x S0, p x S0 -> x \in S0 -> P S0 -> S0 `<=` S -> P (S0 `\` [fset x])) ->
    P (prune S).
  Proof.
    move: S. apply: (nat_size_ind (f := fun X : {fset T} => size X)) => S IH Hp Hstep.
    rewrite prune_equation. case: (fpickP _) => // x px inS. apply: IH.
    - apply: proper_size. exact: properD1.
    - apply: Hstep => //. exact: subxx.
    - move => y S' py inS' PS' sub. apply: Hstep => //. apply: sub_trans sub _.
      exact: fsubDl.
  Qed.

  Lemma prune_sub S : prune S `<=` S.
  Proof.
    apply prune_myind; first by rewrite subxx.
    move => x S' _ _ _. apply: sub_trans. exact: fsubDl.
  Qed.

  Lemma pruneE x S : x \in prune S -> ~~ p x (prune S).
  Proof.
    move: S. apply: (nat_size_ind (f := fun X : {fset T} => size X)) => S IH.
    rewrite prune_equation. case: (fpickP _) => [y pyS yinS|]; last exact.
    apply: IH. apply: proper_size. exact: properD1.
  Qed.
End Pruning.

(** Legacy/compatibility *)

Definition feqEsub := eqEsub.

Lemma set_of_nilp (T : choiceType) (s : seq T) : (set_of s == fset0) = (nilp s).
Proof. 
  apply/idP/nilP; last by rewrite fset0E;move->. 
  apply: contraTeq. case: s => // a l _.
  apply/emptyPn; exists a. by rewrite set_ofE inE eqxx.
Qed.

(* Lemmas that are so far not useful

Lemma fset_rect (T : choiceType) (P : {fset T} -> Type) :
  (P fset0) -> (forall x X, x \notin X -> P X -> P (x |` X)) -> (forall X, P X).
Proof.
  move => P0 Pn X. apply nat_size_ind with (f := fun X : {fset T} => size X).
  move => {X} X IH. case (fset0Vmem X) => [->|[x inX]] //.
  rewrite -(fsetUD1 inX). apply: Pn; first by rewrite !inE inX.
  apply: IH. apply: proper_size.
  rewrite properEneq -{4}[X]fsetD0 fsetDSS ?subxx ?sub0x // andbT.
  apply: contraL inX => /eqP <-. by rewrite !inE.
Qed.
 *)

(** ** Rudimentary Automation *)

Section AutoLemmas.
  Variables (T T':choiceType).
  Implicit Types (X Y Z : {fset T}).

  Lemma fsubU_auto X Y Z : (X `<=` Z) -> (Y `<=` Z) -> (X `|` Y `<=` Z).
  Proof. rewrite fsubUset. by move => -> ->.  Qed.

  Lemma fsub1_auto x X : x \in X -> ([fset x] `<=` X).
  Proof. by rewrite fsub1. Qed.

  Lemma fsetU_auto1 x X Y : x \in X -> x \in X `|` Y.
  Proof. by rewrite inE => ->. Qed.

  Lemma fsetU_auto2 x X Y : x \in Y -> x \in X `|` Y.
  Proof. by rewrite inE => ->. Qed.

  Lemma fsetU_auto3 X Y Z : X `<=` Y -> X `<=` Y `|` Z.
  Proof. move => H. apply: sub_trans H _. by rewrite fsubUl. Qed.

  Lemma fsetU_auto4 X Y Z : X `<=` Y -> X `<=` Z `|` Y.
  Proof. move => H. apply: sub_trans H _. by rewrite fsubUr. Qed.
End AutoLemmas.

Hint Resolve subxx fsetUSU fsubUl fsubUr fsubU_auto fsub1_auto
     fsetU_auto1 fsetU_auto2 fsetU_auto3 fsetU_auto4 fset11 fset1U1 : fset.

Hint Extern 4 (is_true _) => (match goal with [ H : is_true (_ `|` _ `<=` _) |- _ ] => case/fsubUsetP : H end) : fset .
Hint Extern 4 (is_true _) => (match goal with [ H : is_true ((_ \in _) && (_ \in _))|- _ ] => case/andP : H end) : fset .
Hint Extern 4 (is_true _) =>
  match goal with
    | [ H : is_true ((_ \in _) && (_ \in _)) |- _] => case/andP : H
  end : fset. 
