From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.

(* Coq's list library is not very complete.  *)
From stdpp Require list.

(* TODO is this in somewhere of Coq std lib? *)
(* Search "ind" inside PeanoNat. *)
Lemma nat_ind_2 : forall P : nat -> Prop,
  P 0 -> 
  (forall n : nat, (forall m : nat, m <= n -> P m) -> P (S n)) -> 
  forall n : nat, P n.
Proof.
  intros P H IH.
  set (Q:=fun n => (forall m : nat, m <= n -> P m)).
  assert (forall n, Q n) as Hfinal.
  {
    induction n; unfold Q in *; intros.
    - inversion H0. subst. auto.
    - inversion H0; subst.
      + now apply IH.
      + now apply IHn.
  }
  intros. unfold Q in Hfinal. now apply Hfinal with (n:=n).
Qed.

Lemma nat_ind_3 : forall P : nat -> Prop,
  (forall n : nat, (forall m : nat, m < n -> P m) -> P n) -> 
  forall n : nat, P n.
Proof.
  intros P IH.
  set (Q:=fun n => (forall m : nat, m < n -> P m)).
  assert (forall n, Q n) as Hfinal.
  {
    induction n; unfold Q in *; intros.
    - lia.
    - inversion H; subst.
      + now apply IH.
      + now apply IHn.
  }
  intros. unfold Q in Hfinal. apply Hfinal with (n:=S n). lia.
Qed.

Section Sublist_Additional_Lemmas. 

  Lemma sublist_In [A : Type] (l1 l2 : list A) 
    (Hsub : list.sublist l1 l2) (x : A) (Hin : In x l1) : In x l2.
  Proof. 
    eapply list.sublist_submseteq, list.elem_of_submseteq with (x:=x) in Hsub.
    all: now apply base.elem_of_list_In.
  Qed.

  Corollary sublist_cons_remove [A : Type] (x : A) (l1 l2 : list A) 
    (Hsub : list.sublist (x :: l1) l2) : list.sublist l1 l2.
  Proof.
    induction l2 as [ | y l2 IH ].
    - inversion Hsub.
    - inversion Hsub; subst.
      + now constructor.
      + apply list.sublist_cons.
        intuition.
  Qed.

  Corollary sublist_cons_In [A : Type] (x : A) (l1 l2 : list A) 
    (Hsub : list.sublist (x :: l1) l2) : In x l2.
  Proof.
    eapply sublist_In; eauto.
    simpl.
    intuition.
  Qed.

  Fact sublist_map [A B : Type] (f : A -> B) (l1 l2 : list A)
    (Hsub : list.sublist l1 l2) :
    list.sublist (map f l1) (map f l2).
  Proof.
    induction Hsub as [ | x l1 l2 Hsub IHsub | x l1 l2 Hsub IHsub ]; intros.
    - auto.
    - simpl.
      now constructor.
    - simpl.
      now constructor.
  Qed.

  Fact sublist_NoDup [A : Type] (l1 l2 : list A)
    (Hsub : list.sublist l1 l2) (Hnodup : NoDup l2) : NoDup l1.
  Proof.
    induction Hsub as [ | x l1 l2 Hsub IHsub | x l1 l2 Hsub IHsub ]; intros.
    - auto.
    - pose proof (sublist_In _ _ Hsub x).
      rewrite -> NoDup_cons_iff in Hnodup |- *.
      firstorder.
    - pose proof (sublist_In _ _ Hsub x).
      rewrite -> NoDup_cons_iff in Hnodup.
      firstorder.
  Qed.

  Lemma filter_sublist [A : Type] (f : A -> bool) l :
    list.sublist (filter f l) l.
  Proof.
    induction l as [ | x l IH ].
    - reflexivity.
    - simpl.
      now destruct (f x); constructor.
  Qed.

  Fact sublist_StronglySorted [A : Type] (R : A -> A -> Prop) l1 l2
    (H : StronglySorted R l2) (Hsub : list.sublist l1 l2) :
    StronglySorted R l1.
  Proof.
    induction Hsub as [ | x l1 l2 Hsub IHsub | x l1 l2 Hsub IHsub ]; intros.
    - auto.
    - apply StronglySorted_inv in H.
      constructor.
      1: intuition.
      destruct H as (_ & H).
      rewrite -> List.Forall_forall in H |- *.
      pose proof (sublist_In _ _ Hsub).
      firstorder.
    - apply StronglySorted_inv in H.
      intuition.
  Qed.

End Sublist_Additional_Lemmas. 

Lemma NoDup_concat [A : Type] (l : list (list A)) 
  (H : (@List.NoDup A) (concat l)) : Forall (@List.NoDup A) l.
Proof.
  induction l as [ | xs l IH ].
  - auto.
  - simpl in H.
    rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in H.
    destruct H as (H1 & _ & H2).
    constructor; intuition.
Qed.

Lemma NoDup_map_inj [A B : Type] (l : list A) 
  (f : A -> B) (H : List.NoDup (map f l))
  x y (Heq : f x = f y) (Hinx : In x l) (Hiny : In y l) : x = y.
Proof.
  apply base.elem_of_list_In, list.elem_of_Permutation in Hinx.
  destruct Hinx as (l' & Hperm).
  pose proof Hperm as Hperm_backup.
  apply Permutation.Permutation_map with (f:=f), Permutation.Permutation_NoDup in Hperm.
  2: assumption.
  simpl in Hperm.
  apply NoDup_cons_iff in Hperm.
  eapply Permutation.Permutation_in in Hperm_backup.
  2: apply Hiny.
  simpl in Hperm_backup.
  destruct Hperm_backup as [ | Htmp ].
  1: assumption.
  apply in_map with (f:=f) in Htmp.
  intuition congruence.
Qed.

Lemma split_map_fst_snd [A B : Type] (l : list (A * B)) :
  List.split l = (map fst l, map snd l).
Proof.
  induction l as [ | (x, y) l IH ].
  - auto.
  - simpl.
    now rewrite -> IH.
Qed.

Lemma partition_filter [A : Type] (f : A -> bool) l :
  partition f l = (filter f l, filter (fun a => negb (f a)) l).
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl.
    rewrite -> IH.
    now destruct (f x).
Qed.

Lemma map_filter_comm [A B : Type] (f : A -> B) (g : B -> bool) l :
  filter g (map f l) = map f (filter (fun x => g (f x)) l).
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl.
    rewrite -> ! IH.
    now destruct (g (f x)).
Qed.

Fact Forall_filter [A : Type] (f : A -> bool) l (P : A -> Prop) 
  (H : Forall P l) : Forall P (filter f l).
Proof.
  rewrite -> Forall_forall in H |- *.
  setoid_rewrite -> filter_In.
  firstorder.
Qed.

Fact StronglySorted_app [A : Type] (R : A -> A -> Prop) (l1 l2 : list A)
  (H1 : StronglySorted R l1) (H2 : StronglySorted R l2) 
  (H : forall x y, In x l1 -> In y l2 -> R x y) :
  StronglySorted R (l1 ++ l2).
Proof.
  induction l1 as [ | x l1 IH ].
  - now simpl.
  - apply StronglySorted_inv in H1.
    destruct H1 as (H1 & Hx).
    rewrite -> List.Forall_forall in Hx.
    simpl in H |- *.
    constructor.
    + apply IH.
      1: assumption.
      firstorder.
    + rewrite -> List.Forall_app, -> ! List.Forall_forall.
      firstorder.
Qed.

Fact Forall2_forall_exists_l [A B : Type] (P : A -> B -> Prop) l1 l2
  (H : Forall2 P l1 l2) (x : A) (Hin : In x l1) :
  exists y, In y l2 /\ P x y.
Proof.
  induction H as [ | x0 y0 l1 l2 Hp H IH ].
  - inversion Hin.
  - simpl in Hin |- *.
    destruct Hin as [ -> | Hin ]; firstorder.
Qed.

Fact Forall2_forall_exists_r [A B : Type] (P : A -> B -> Prop) l1 l2
  (H : Forall2 P l1 l2) (y : B) (Hin : In y l2) :
  exists x, In x l1 /\ P x y.
Proof.
  induction H as [ | x0 y0 l1 l2 Hp H IH ].
  - inversion Hin.
  - simpl in Hin |- *.
    destruct Hin as [ -> | Hin ]; firstorder.
Qed.

(* a simple swap of map and flat_map over In *)

Fact map_flat_map_In [A B C : Type] (f : B -> C) (g : A -> list B) (l : list A) :
  forall x, In x (map f (flat_map g l)) <-> (exists y, In y l /\ In x (map f (g y))).
Proof. 
  intros x.
  repeat setoid_rewrite -> in_map_iff.
  setoid_rewrite -> in_flat_map.
  firstorder congruence.
Qed.

Fact map_flat_map_In_conv [A B C : Type] (f : B -> C) (g : A -> list B) (l : list A) 
  (x : C) (y : A) (Hin : In y l) (Hin2 : In x (map f (g y))) : In x (map f (flat_map g l)).
Proof. apply map_flat_map_In. eauto. Qed.

Fact Permutation_partition [A : Type] (f : A -> bool) l :
  Permutation.Permutation l ((fst (partition f l)) ++ (snd (partition f l))).
Proof. 
  induction l as [ | x l IH ].
  - now simpl.
  - simpl.
    destruct (partition f l) as (l1, l2).
    simpl in IH |- *.
    destruct (f x); simpl.
    + now constructor.
    + rewrite <- Permutation.Permutation_middle.
      now constructor.
Qed.

Fact in_flat_map_conv : forall [A B : Type] (f : A -> list B) (l : list A) (x : A) (y : B),
  In x l -> In y (f x) -> In y (flat_map f l).
Proof. intros. apply in_flat_map. eauto. Qed.

Fact flat_map_single : forall [A B : Type] (f : A -> list B) (x : A),
  f x = flat_map f (x :: nil).
Proof. intros. simpl. now rewrite -> app_nil_r. Qed.

(* TODO did not find a good union operation for this *)

Lemma find_app [A : Type] (f : A -> bool) (l1 l2 : list A) : 
  find f (l1 ++ l2) = 
  match find f l1 with
  | Some res => Some res
  | None => find f l2
  end.
Proof.
  revert l2.
  induction l1 as [ | x l1 IH ]; intros.
  - reflexivity.
  - simpl.
    destruct (f x) eqn:E.
    + reflexivity.
    + now apply IH.
Qed.

Fact pair_equal_split [A B : Type] (a b : A) (c d : B) 
  (E : (a, c) = (b, d)) : a = b /\ c = d.
Proof. intuition congruence. Qed.

Definition filtermap [A B : Type] (f : A -> bool) (g : A -> B) :=
  fun (l : list A) => 
  let fix filtermap l :=
    match l with
    | nil => nil
    | a :: l' => if f a then (g a) :: filtermap l' else filtermap l'
    end in filtermap l.

Lemma filtermap_correct [A B : Type] (f : A -> bool) (g : A -> B) l :
  filtermap f g l = map g (filter f l).
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl.
    rewrite -> ! IH.
    now destruct (f x).
Qed.

Lemma Forall2_mapself_l [A B : Type] (f : A -> B) (l : list A)
  (P : B -> A -> Prop) :
  Forall2 P (map f l) l <-> Forall (fun x => P (f x) x) l.
Proof.
  induction l as [ | x l IH ].
  - intuition constructor.
  - simpl.
    rewrite -> list.Forall2_cons, -> Forall_cons_iff.
    intuition.
Qed.
