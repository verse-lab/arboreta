From Coq Require Import List Bool Lia PeanoNat Sorting RelationClasses Permutation.
(* From Coq Require ssreflect.
Import ssreflect.SsrSyntax. *)

From stdpp Require list.

(* Search "ind" inside PeanoNat. *)
(*
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
*)
(*
(* see "Wf_nat.lt_wf_ind" *)
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
*)

Section Begin.

(* Sometimes using auto with * is affordable. *)
Local Ltac intuition_solver ::= auto with *.

(* Some additional lemmas about the "sublist" predicate in stdpp. Mostly for adaptation. *)

Section Sublist_Additional_Lemmas.

  Lemma sublist_In [A : Type] [l1 l2 : list A] 
    (Hsub : list.sublist l1 l2) [x : A] (Hin : In x l1) : In x l2.
  Proof. 
    eapply list.sublist_submseteq, list.elem_of_submseteq with (x:=x) in Hsub.
    all: now apply base.elem_of_list_In.
  Qed.

  Corollary sublist_Forall [A : Type] (P : A -> Prop) [l1 l2 : list A]
    (Hsub : list.sublist l1 l2) (H : Forall P l2) : Forall P l1.
  Proof. eapply incl_Forall. 2: apply H. hnf. intros ?. now apply sublist_In. Qed.

  Corollary sublist_cons_remove [A : Type] [x : A] [l1 l2 : list A]
    (Hsub : list.sublist (x :: l1) l2) : list.sublist l1 l2.
  Proof.
    induction l2 as [ | y l2 IH ].
    - inversion Hsub.
    - inversion Hsub; subst.
      + now constructor.
      + apply list.sublist_cons.
        intuition.
  Qed.

  Corollary sublist_cons_In [A : Type] [x : A] [l1 l2 : list A]
    (Hsub : list.sublist (x :: l1) l2) : In x l2.
  Proof.
    eapply sublist_In; eauto.
    simpl.
    intuition.
  Qed.

  Fact sublist_map [A B : Type] (f : A -> B) [l1 l2 : list A]
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

  Fact sublist_NoDup [A : Type] [l1 l2 : list A]
    (Hsub : list.sublist l1 l2) (Hnodup : NoDup l2) : NoDup l1.
  Proof.
    induction Hsub as [ | x l1 l2 Hsub IHsub | x l1 l2 Hsub IHsub ]; intros.
    - auto.
    - pose proof (sublist_In Hsub).
      rewrite -> NoDup_cons_iff in Hnodup |- *.
      firstorder.
    - pose proof (sublist_In Hsub).
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

  Fact sublist_StronglySorted [A : Type] (R : A -> A -> Prop) [l1 l2]
    (Hsub : list.sublist l1 l2) (H : StronglySorted R l2) :
    StronglySorted R l1.
  Proof.
    induction Hsub as [ | x l1 l2 Hsub IHsub | x l1 l2 Hsub IHsub ]; intros.
    - auto.
    - apply StronglySorted_inv in H.
      constructor.
      1: intuition.
      destruct H as (_ & H).
      rewrite -> List.Forall_forall in H |- *.
      pose proof (sublist_In Hsub).
      firstorder.
    - apply StronglySorted_inv in H.
      intuition.
  Qed.

  Fact sublist_Forall2 [A B : Type] (R : A -> B -> Prop) [l1 l2 l3]
    (Hsub : list.sublist l1 l2) (H : Forall2 R l2 l3) :
    exists l3', list.sublist l3' l3 /\ Forall2 R l1 l3'.
  Proof.
    revert l1 Hsub.
    induction H as [ | a b l2 l3 Hab H IH ]; intros.
    - apply list.sublist_nil_r in Hsub.
      subst l1.
      now exists nil.
    - apply list.sublist_cons_r in Hsub.
      destruct Hsub as [ (l3' & Hsub & ?)%IH | (l' & -> & (l3' & Hsub & ?)%IH) ].
      + exists l3'.
        split; [ apply list.sublist_cons_r | ]; auto.
      + exists (b :: l3').
        split; auto.
        econstructor; eauto.
  Qed.

End Sublist_Additional_Lemmas.

Section NoDup_Additional_Lemmas.

  Fact NoDup_app_ [A : Type] (l l' : list A) :
    NoDup (l ++ l') <->
    NoDup l /\ (forall a : A, In a l -> In a l' -> False) /\ NoDup l'.
  Proof.
    (* adapted from stdpp *)
    rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
    repeat setoid_rewrite base.elem_of_list_In.
    reflexivity.
  Qed.

  Lemma NoDup_concat [A : Type] [l : list (list A)] 
    (H : (@List.NoDup A) (concat l)) : Forall (@List.NoDup A) l.
  Proof.
    induction l as [ | xs l IH ].
    - auto.
    - simpl in H.
      rewrite NoDup_app_ in H.
      destruct H as (H1 & _ & H2).
      constructor; intuition.
  Qed.

  Lemma NoDup_map_inj [A B : Type] (f : A -> B) [l : list A]
    (H : List.NoDup (map f l))
    [x y] (Hinx : In x l) (Hiny : In y l) (Heq : f x = f y) : x = y.
  Proof.
    apply base.elem_of_list_In, list.elem_of_Permutation in Hinx.
    destruct Hinx as (l' & Hperm).
    pose proof Hperm as Hperm_backup.
    apply Permutation_map with (f:=f), Permutation_NoDup in Hperm.
    2: assumption.
    simpl in Hperm.
    apply NoDup_cons_iff in Hperm.
    eapply Permutation_in in Hperm_backup.
    2: apply Hiny.
    simpl in Hperm_backup.
    destruct Hperm_backup as [ | Htmp ].
    1: assumption.
    apply in_map with (f:=f) in Htmp.
    intuition congruence.
  Qed.

End NoDup_Additional_Lemmas.

Lemma partition_filter [A : Type] (f : A -> bool) l :
  partition f l = (filter f l, filter (fun a => negb (f a)) l).
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl.
    rewrite -> IH.
    now destruct (f x).
Qed.

Section Permutation_Additional_Lemmas.

  Fact Permutation_partition [A : Type] (f : A -> bool) l :
    Permutation l ((fst (partition f l)) ++ (snd (partition f l))).
  Proof. 
    induction l as [ | x l IH ].
    - now simpl.
    - simpl.
      destruct (partition f l) as (l1, l2).
      simpl in IH |- *.
      destruct (f x); simpl.
      + now constructor.
      + rewrite <- Permutation_middle.
        now constructor.
  Qed.

  Corollary Permutation_split_combine [A : Type] (f : A -> bool) (l : list A) :
    Permutation l (filter f l ++ filter (fun a => negb (f a)) l).
  Proof.
    etransitivity; [ apply Permutation_partition with (f:=f) | ].
    rewrite partition_filter.
    reflexivity.
  Qed. 

  Fact Permutation_in_mutual [A : Type] [l l' : list A] (H : Permutation l l') :
    forall x, In x l <-> In x l'.
  Proof.
    intros; split.
    2: symmetry in H.
    all: now apply Permutation_in.
  Qed.

  Fact Permutation_Forall_flat_map [A B : Type] (f g : A -> list B) [l : list A]
    (H : Forall (fun x => Permutation (f x) (g x)) l) :
    Permutation (flat_map f l) (flat_map g l).
  Proof.
    induction l as [ | x l IH ]; simpl; auto.
    rewrite -> Forall_cons_iff in H.
    destruct H as (H1 & H2).
    apply Permutation_app; auto.
  Qed.

  Fact Permutation_flat_map_innerapp_split [A B : Type] (f g : A -> list B) (l : list A) :
    Permutation (flat_map (fun x => f x ++ g x) l) (flat_map f l ++ flat_map g l).
  Proof.
    induction l as [ | x l IH ]; simpl; auto.
    etransitivity.
    1: apply Permutation_app; [ reflexivity | apply IH ].
    rewrite -> Permutation_app_swap_app.
    etransitivity.
    2: apply Permutation_app; [ apply Permutation_app_comm | reflexivity ].
    now rewrite <- ! app_assoc.
  Qed.

End Permutation_Additional_Lemmas.

Lemma split_map_fst_snd [A B : Type] (l : list (A * B)) :
  List.split l = (map fst l, map snd l).
Proof.
  induction l as [ | (x, y) l IH ].
  - auto.
  - simpl.
    now rewrite -> IH.
Qed.

Lemma partition_ext_Forall [A : Type] (f g : A -> bool) l 
  (H : Forall (fun x => f x = g x) l) :
  partition f l = partition g l.
Proof.
  induction l as [ | x l IH ]; simpl; auto.
  rewrite -> Forall_cons_iff in H.
  destruct H as (H' & H).
  rewrite H', IH; auto.
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

Lemma filter_filter [A : Type] (f g : A -> bool) l :
  filter g (filter f l) = filter (fun a => f a && g a) l.
Proof.
  induction l as [ | x l IH ]; simpl; auto.
  destruct (f x) eqn:E; [ destruct (g x) eqn:E' | ].
  all: simpl; try rewrite E'; try rewrite IH; auto.
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

Section Forall2_Additional_Lemmas. 

  Fact Forall2_forall_exists_l [A B : Type] [P : A -> B -> Prop] [l1 l2]
    (H : Forall2 P l1 l2) [x : A] (Hin : In x l1) :
    exists y, In y l2 /\ P x y.
  Proof.
    induction H as [ | x0 y0 l1 l2 Hp H IH ].
    - inversion Hin.
    - simpl in Hin |- *.
      destruct Hin as [ -> | Hin ]; firstorder.
  Qed.

  Fact Forall2_forall_exists_r [A B : Type] [P : A -> B -> Prop] [l1 l2]
    (H : Forall2 P l1 l2) [y : B] (Hin : In y l2) :
    exists x, In x l1 /\ P x y.
  Proof.
    induction H as [ | x0 y0 l1 l2 Hp H IH ].
    - inversion Hin.
    - simpl in Hin |- *.
      destruct Hin as [ -> | Hin ]; firstorder.
  Qed.

  Fact Forall2_and [A B : Type] (P Q : A -> B -> Prop) l1 l2 :
    Forall2 P l1 l2 /\ Forall2 Q l1 l2 <-> Forall2 (fun a b => P a b /\ Q a b) l1 l2.
  Proof.
    split; [ intros (H & H0) | intros H ]; induction H; rewrite -> ? list.Forall2_cons in *; firstorder.
  Qed.

  Lemma Forall2_mapself_l [A B : Type] (f : A -> B) (P : B -> A -> Prop) l :
    Forall2 P (map f l) l <-> Forall (fun x => P (f x) x) l.
  Proof.
    induction l as [ | x l IH ].
    - intuition constructor.
    - simpl.
      rewrite -> list.Forall2_cons, -> Forall_cons_iff.
      intuition.
  Qed.

  Lemma Forall2_map [A B C D : Type] (f : A -> B) (g : C -> D) (P : B -> D -> Prop) l1 l2 :
    Forall2 (fun a c => P (f a) (g c)) l1 l2 <->
    Forall2 P (map f l1) (map g l2).
  Proof.
    split; intros H.
    - induction H; simpl in *; rewrite -> ? list.Forall2_cons in *; firstorder.
    - remember (map f l1) as l1' eqn:E1.
      remember (map g l2) as l2' eqn:E2.
      revert l1 l2 E1 E2.
      induction H; intros ?? ?%eq_sym ?%eq_sym.
      + apply map_eq_nil in E1, E2.
        now subst.
      + destruct l1 as [ | x' l1 ], l2 as [ | y' l2 ].
        all: simpl in E1, E2; try discriminate; injection E1 as <-; injection E2 as <-.
        subst.
        constructor; auto.
  Qed.

  Fact map_eq_to_Forall2 [A B : Type] (f : A -> B) la lb :
    lb = map f la <-> Forall2 (fun b a => b = f a) lb la.
  Proof.
    split; intros.
    - subst lb.
      now apply Forall2_mapself_l, list.Forall_true.
    - induction H; simpl; congruence.
  Qed.

End Forall2_Additional_Lemmas. 

(* FIXME: move this somewhere else *)
Corollary sublist_map_l_recover [A B : Type] (f : A -> B) [l1 l2]
  (Hsub : list.sublist l1 (map f l2)) :
  exists l2', l1 = map f l2' /\ list.sublist l2' l2.
Proof.
  eapply sublist_Forall2 in Hsub.
  2: rewrite <- map_eq_to_Forall2; reflexivity.
  destruct Hsub as (l2' & Hsub & HH%map_eq_to_Forall2).
  eauto.
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

Fact in_flat_map_conv : forall [A B : Type] (f : A -> list B) (l : list A) (x : A) (y : B),
  In x l -> In y (f x) -> In y (flat_map f l).
Proof. intros. apply in_flat_map. eauto. Qed.

Fact flat_map_single : forall [A B : Type] (f : A -> list B) (x : A),
  f x = flat_map f (x :: nil).
Proof. intros. simpl. now rewrite -> app_nil_r. Qed.

Fact flat_map_map : forall [A B C : Type] (g : A -> list B) (f : B -> C) (l : list A),
  flat_map (fun a => map f (g a)) l = map f (flat_map g l).
Proof. intros. induction l as [ | ?? IH ]; simpl; auto. now rewrite IH, map_app. Qed.

Fact flat_map_flat_map : forall [A B C : Type] (f : A -> list B) (g : B -> list C) (l : list A),
  flat_map (fun a => flat_map g (f a)) l = flat_map g (flat_map f l).
Proof. intros. induction l as [ | ?? IH ]; simpl; auto. now rewrite IH, flat_map_app. Qed.

Fact map_ext_Forall2 : forall [A B : Type] (f : A -> B) (l1 l2 : list A),
  Forall2 (fun a1 a2 => f a1 = f a2) l1 l2 -> map f l1 = map f l2.
Proof. intros. induction H; simpl; intuition. Qed.

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
(*
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
*)
Fact filter_all_true {A : Type} (f : A -> bool) (l : list A) 
  (H : forall x, In x l -> f x = true) : filter f l = l.
Proof.
  induction l as [ | y l IH ]; simpl in *; auto.
  pose proof (H _ (or_introl eq_refl)) as ->.
  f_equal; auto.
Qed.

Fact filter_all_false {A : Type} (f : A -> bool) (l : list A) 
  (H : forall x, In x l -> f x = false) : filter f l = nil.
Proof.
  induction l as [ | y l IH ]; simpl in *; auto.
  pose proof (H _ (or_introl eq_refl)) as ->.
  f_equal; auto.
Qed.

Fact split_app {A B : Type} (l1 l2 : list (A * B)) :
  List.split (l1 ++ l2) = 
  let (l1a, l1b) := List.split l1 in let (l2a, l2b) := List.split l2 in
  (l1a ++ l2a, l1b ++ l2b).
Proof.
  revert l2. 
  induction l1 as [ | (a, b) l1 IH ]; intros; simpl in *.
  - now destruct (List.split l2).
  - rewrite -> IH. 
    now destruct (List.split l1), (List.split l2).
Qed.

Fact map_id_eq [A : Type] (l : list A) : map id l = l.
Proof. induction l; simpl; congruence. Qed.

(* only pose some simple things *)

Fact pointwise_le_sum_le [l1 l2 : list nat] (H : Forall2 Nat.le l1 l2) :
  fold_right Nat.add 0%nat l1 <= fold_right Nat.add 0%nat l2.
Proof. induction H; intros; simpl; try reflexivity. lia. Qed.

Fact pointwise_le_sum_le_ [A : Type] [l1 l2 : list A] 
  (f : A -> nat) (H : Forall2 Nat.le (map f l1) (map f l2)) 
  (IH : Forall2 (fun a1 a2 => f a1 = f a2 -> a1 = a2) l1 l2)
  (H0 : fold_right Nat.add 0%nat (map f l1) = fold_right Nat.add 0%nat (map f l2)) : 
  l1 = l2.
Proof.
  remember (map f l1) as l1' eqn:E1.
  remember (map f l2) as l2' eqn:E2.
  revert l1 l2 E1 E2 IH.
  induction H; intros ?? ?%eq_sym ?%eq_sym ?.
  - apply map_eq_nil in E1, E2.
    now subst.
  - destruct l1 as [ | x' l1 ], l2 as [ | y' l2 ].
    all: simpl in E1, E2; try discriminate; injection E1 as <-; injection E2 as <-.
    subst.
    simpl in H0.
    pose proof (pointwise_le_sum_le H1).
    apply list.Forall2_cons in IH.
    destruct IH as (Hxy & IH).
    f_equal.
    + apply Hxy; lia.
    + apply IHForall2; auto; lia.
Qed.

Fact pointwise_le_sum_le_' [l1 l2 : list nat] (H : Forall2 Nat.le l1 l2) 
  (H0 : fold_right Nat.add 0%nat l1 = fold_right Nat.add 0%nat l2) : l1 = l2.
Proof.
  apply pointwise_le_sum_le_ with (f:=id).
  all: rewrite ? map_id_eq; auto.
  eapply list.Forall2_impl.
  1: apply H.
  auto.
Qed.

Fact length_concat_sum {A : Type} (l : list (list A)) :
  length (concat l) = fold_right Nat.add 0%nat (map length l).
Proof.
  induction l as [ | x l IH ]; intros; simpl; try reflexivity.
  rewrite -> ! app_length.
  now f_equal.
Qed.
(*
Fact length_concat_le {A B : Type} (l1 : list (list A)) (l2 : list (list B))
  (H : Forall2 (fun c1 c2 => length c1 <= length c2) l1 l2) :
  length (concat l1) <= length (concat l2).
Proof. rewrite -> ! length_concat_sum. now apply pointwise_le_sum_le, list.Forall2_fmap_2. Qed.
*)
(* really ad-hoc lemmas; not quite belong to sublist ones *)

Fact sublist_sum_le l1 l2 (Hsub : list.sublist l1 l2) :
  fold_right Nat.add 0%nat l1 <= fold_right Nat.add 0%nat l2.
Proof. induction Hsub; intros; simpl in *; try lia. Qed.

Fact sublist_map_sum_eq_ [A : Type] [l1 l2 : list A] (Hsub : list.sublist l1 l2)
  (f : A -> nat) (Hf : forall a, 0 < f a) :
  fold_right Nat.add 0%nat (map f l1) = fold_right Nat.add 0%nat (map f l2) ->
  l1 = l2.
Proof.
  induction Hsub; intros; simpl in *; try tauto.
  - f_equal; auto with *.
  - apply sublist_map with (f:=f), sublist_sum_le in Hsub.
    specialize (Hf x).
    lia.
Qed.

Fact Forall_impl_impl {A : Type} (P Q : A -> Prop) (l : list A) (H : Forall (fun x => P x -> Q x) l)
  (H0 : Forall P l) : Forall Q l.
Proof. induction l as [ | x l IH ]; auto. rewrite -> Forall_cons_iff in *. intuition. Qed.

(* TODO is this present in stdlib? *)

Fact firstn_skipn_onemore {A : Type} (l : list A) (i : nat) (x : A) (suf : list A)
  (H : skipn i l = x :: suf) :
  firstn (S i) l = firstn i l ++ (x :: nil) /\ skipn (S i) l = suf.
Proof.
  assert (i < length l)%nat as Hlt.
  { 
    destruct (Nat.leb (length l) i) eqn:E; [ apply Nat.leb_le in E | now apply Nat.leb_gt in E ].
    apply skipn_all2 in E; congruence.
  }
  assert (length (firstn i l) = i) as Hlen by (apply firstn_length_le; lia).
  rewrite <- firstn_skipn with (n:=i) (l:=l) at 1 3.
  rewrite -> H.
  split.
  - rewrite <- Hlen, <- Nat.add_1_r at 1. 
    now rewrite -> firstn_app_2.
  - rewrite <- Hlen at 1.
    rewrite -> skipn_app, -> skipn_all2 at 1; try lia.
    replace (S _ - _) with 1 by lia.
    now simpl.
Qed.

Lemma list_ind_3 : forall (A : Type) (P : list A -> Prop),
  P nil ->
  (forall n, (forall l, length l = n -> P l) -> forall l, length l = S n -> P l) ->
  forall l : list A, P l.
Proof.
  intros. 
  remember (length l) as n eqn:E. 
  revert l E.
  induction n as [ | n IH ]; intros.
  - destruct l; simpl in E; congruence.
  - destruct l; try (simpl in E; congruence).
    eapply H0.
    2: now rewrite E.
    auto.
Qed.

(* another way to prove rev_ind *)

Lemma list_ind_2 : forall (A : Type) (P : list A -> Prop),
  P nil ->
  (forall (a : A) (l : list A), P l -> P (l ++ (a :: nil))) ->
  forall l : list A, P l.
Proof.
  intros.
  induction l using list_ind_3; intros; auto.
  assert (l <> nil) as HH by (destruct l; simpl in *; congruence).
  destruct (exists_last HH) as (l' & a & ->).
  rewrite -> last_length in H2. 
  injection H2 as <-.
  auto.
Qed.

Fact Permutation_upto_pick m n (H : m < n) :
  Permutation (seq 0 n) (m :: ((seq 0 m) ++ (seq (S m) (n - (S m))))).
Proof.
  replace n with (m + (S (n - (S m)))) at 1 by lia.
  rewrite -> seq_app.
  simpl. 
  symmetry.
  now apply Permutation_middle.
Qed.

Fact in_pre_suf [A : Type] [pre suf : list A] (sub : A) : In sub (pre ++ sub :: suf).
Proof. rewrite -> in_app_iff. simpl In. tauto. Qed.

(* a little fact ... TODO why this is not in stdlib? *)
Fact nth_error_some_inrange {A : Type} (i : nat) (al : list A) a : 
  nth_error al i = Some a -> (i < length al)%nat.
Proof.
  revert i a. 
  induction al as [ | a' al IH ]; intros; simpl in *.
  - destruct i; now simpl in H.
  - destruct i; try lia. 
    simpl in H. 
    apply IH in H. 
    lia.
Qed.

Fact firstn_last {A : Type} (l : list A) (i : nat) (H : S i <= length l) :
  list.last (firstn (S i) l) = nth_error l i.
Proof.
  revert i H.
  induction l as [ | x l IH ]; intros; simpl in *.
  - now destruct i.
  - destruct i as [ | i ]; simpl; auto.
    apply le_S_n in H.
    rewrite <- IH; auto.
    destruct l; simpl in *.
    1: inversion H.
    reflexivity.
Qed.

Fact list_rev_destruct [A : Type] (l : list A) : {l = nil} + {exists l' x, l = l' ++ x :: nil}.
Proof.
  destruct l eqn:E; [ now left | right ].
  rewrite <- E.
  assert (l <> nil) as (l' & x & ->)%exists_last by now subst.
  eauto.
Qed.

Fact list_ifnil_destruct [A : Type] (l : list A) : {l = nil} + {l <> nil}.
Proof. destruct l; [ now left | now right ]. Qed.

Fact eqdec_must_left [A B : Type] (eqd : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) [b1 b2 : B] (a : A) :
  (if eqd a a then b1 else b2) = b1.
Proof. destruct (eqd _ _); auto; try contradiction. Qed.

Fact eqdec_must_right [A B : Type] (eqd : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) [b1 b2 : B] [a1 a2 : A] (H : a1 <> a2) :
  (if eqd a1 a2 then b1 else b2) = b2.
Proof. destruct (eqd _ _); auto; try contradiction. Qed.

Fact contra_not [P Q : Prop] (H : P -> Q) : ~ Q -> ~ P.
Proof. intuition. Qed.

Definition isSome [A : Type] (o : option A) : bool :=
  match o with Some _ => true | _ => false end.

Global Arguments isSome [_] !_.

(* although this can be defined with firstn and lastn, now use this anyway *)
Fixpoint upd_nth [A : Type] (n : nat) (l : list A) (a : A) :=
  match l with
  | nil => nil
  | x :: l' => match n with O => a :: l' | S n' => upd_nth n' l' a end
  end.

(*
Fact upd_Znth_upd_nth [A : Type] n (l : list A) a (H : (n < length l)%nat):
  upd_Znth (Z.of_nat n) l a = upd_nth n l a.
*)

End Begin.
