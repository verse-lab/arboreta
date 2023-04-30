From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.

(* Coq's list library is not very complete.  *)
From stdpp Require list.

Tactic Notation "removehead" hyp(H) :=
  let qq := fresh "nobody_will_use_this" in
  let qq2 := fresh "nobody_will_use_this2" in
  match (type of H) with
  ?HH -> _ => enough HH as qq; 
    [ pose proof (H qq) as qq2; clear H; rename qq2 into H; clear qq | ]
  end
.

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

(* seemingly a wrapper of find *)

Fixpoint find_first_some [A : Type] (l : list (option A)) : option A :=
  match l with
  | nil => None
  | o :: l' => match o with 
               | Some e => Some e
               | None => find_first_some l'
               end
  end.

Lemma find_first_some_correct [A : Type] (l : list (option A)) : 
  find_first_some l = match find isSome l with Some res => res | None => None end.
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl. now destruct x.
Qed.

Corollary find_first_some_correct' [A : Type] (l : list (option A)) : 
  find_first_some l <-> find isSome l.
Proof. 
  rewrite -> find_first_some_correct. 
  destruct (find isSome l) as [ res | ] eqn:E.
  2: auto.
  apply find_some in E.
  now destruct res.
Qed.

Fact some_In_findsome_iff [A : Type] (l : list (option A)) : 
  find isSome l <-> (exists res, In (Some res) l).
Proof.
  split.
  - intros H.
    destruct (find isSome l) as [ res | ] eqn:E.
    2: now unfold isSome in *.
    apply find_some in E.
    unfold isSome in E.
    destruct res as [ res | ]; [ now exists res | intuition ].
  - intros (res & Hin).
    destruct (find isSome l) as [ res' | ] eqn:E.
    1: auto.
    eapply find_none in E.
    2: apply Hin.
    discriminate.
Qed.

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

Lemma filter_sublist [A : Type] (f : A -> bool) l :
  list.sublist (filter f l) l.
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl.
    now destruct (f x); constructor.
Qed.

Fact Forall_filter [A : Type] (f : A -> bool) l (P : A -> Prop) 
  (H : Forall P l) : Forall P (filter f l).
Proof.
  rewrite -> Forall_forall in H |- *.
  setoid_rewrite -> filter_In.
  firstorder.
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

Section TreeClock.

Context {thread : Type} (thread_eqdec : forall (t1 t2 : thread), {t1 = t2} + {t1 <> t2}).

(* OK, let's try making info_aclk not an option by making the aclk of the root useless. *)

Record nodeinfo : Type := mkInfo {
  info_tid : thread;
  info_clk : nat;
  info_aclk : nat
}.

Definition nodeinfo_eqdec (ni ni' : nodeinfo) : {ni = ni'} + {ni <> ni'}.
Proof.
  decide equality.
  all: apply Nat.eq_dec.
Qed.

Inductive treeclock : Type :=
  Node (ni : nodeinfo) (chn : list treeclock).

(* The automatically generated induction principle is useless.  *)
(* seems can be solved with "Scheme", but that would require a mutually recursive inductive type? *)

Fixpoint tc_height tc : nat := 
  let: Node _ chn := tc in 
  S (List.list_max (map tc_height chn)).

(* maybe no longer useful, but  *)
Fact tc_height_le n chn ch (Hin : In ch chn) (Hle : List.list_max (map tc_height chn) <= n) :
  tc_height ch <= n.
Proof.
  eapply list_max_le, Forall_map, List.Forall_forall in Hle.
  2: apply Hin.
  assumption.
Qed.

Fact tc_height_map_nil chn : List.list_max (map tc_height chn) <= 0 <-> chn = nil.
Proof. 
  split; intros H.
  - destruct chn as [| [(?, ?, ?) ?] ?].
    all: simpl in *; try lia; auto.
  - subst chn. simpl. lia.
Qed.

(* step-indexing is useful. *)
(* emmm, there are other approaches for establishing this, 
  (e.g., check CoqArt book; this is called ltree or rose tree in the literature)
  but anyway.  *)

Lemma treeclock_ind_bounded_height (P : treeclock -> Prop)
  (Hind : forall (ni : nodeinfo) (chn : list treeclock), 
    Forall P chn -> P (Node ni chn)) n : 
  forall (tc : treeclock) (Hh : tc_height tc <= n), P tc.
Proof.
  induction n as [ | n IH ] using nat_ind_2; intros.
  all: destruct tc as (ni & chn); simpl in Hh.
  - lia.
  - apply le_S_n, list_max_le, Forall_map in Hh. 
    apply Hind, List.Forall_impl with (P:=fun x => tc_height x <= n).
    2: assumption.
    intros.
    apply IH with (m:=n).
    + lia.
    + assumption.
Qed.

Lemma treeclock_ind_2 (P : treeclock -> Prop)
  (Hind : forall (ni : nodeinfo) (chn : list treeclock), 
    Forall P chn -> P (Node ni chn)) : 
  forall (tc : treeclock), P tc.
Proof.
  intros tc.
  apply treeclock_ind_bounded_height with (n:=tc_height tc). 
  - assumption.
  - lia.
Qed.

Fixpoint treeclock_eqb tc tc' :=
  let: Node ni chn := tc in
  let: Node ni' chn' := tc' in
  if nodeinfo_eqdec ni ni'
  then 
    (if Nat.eq_dec (length chn) (length chn')
      then 
        List.forallb (fun pp => (fst pp) (snd pp))
          (List.combine (map treeclock_eqb chn) chn')
        (* List.forallb (fun tcp => uncurry treeclock_eqb tcp)
        (List.combine chn chn') *)
        (* this does not pass the decrease check *)
      else false)
  else false.

Lemma treeclock_eqP tc : forall tc', treeclock_eqb tc tc' <-> tc = tc'.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2. 
  intros [ni' chn'].
  simpl.
  destruct (nodeinfo_eqdec ni ni') as [ <- | Hnineq ].
  2: intuition congruence.
  transitivity (chn = chn').
  2: intuition congruence.
  clear ni.
  destruct (Nat.eq_dec (length chn) (length chn')) as [ El | Hlneq ].
  2: intuition congruence.
  unfold is_true.
  rewrite -> forallb_forall.
  rewrite -> List.Forall_forall in IH.
  (* a local induction *)
  revert chn' El.
  induction chn as [ | ch chn IH' ]; intros.
  - destruct chn'.
    2: discriminate.
    intuition.
  - destruct chn' as [ | ch' chn' ].
    1: discriminate.
    simpl in El.
    injection El as El.
    simpl in IH |- *.
    pose proof (IH _ (or_introl eq_refl) ch') as Hch.
    apply IH' in El.
    2: intros x HH; apply IH; intuition.
    split; intros H.
    + f_equal.
      * specialize (H _ (or_introl eq_refl)).
        now apply Hch.
      * apply El.
        intros ? ?.
        eapply H; eauto.
    + injection H as <-.
      subst chn'.
      intros (cmp, tc') [ <- | ]; intuition.
Qed.

Definition treeclock_eqdec (tc tc' : treeclock) : {tc = tc'} + {tc <> tc'}.
Proof.
  destruct (treeclock_eqb tc tc') eqn:E.
  - apply treeclock_eqP in E.
    now left.
  - right.
    intros EE.
    apply treeclock_eqP in EE.
    intuition congruence.
Qed.

Definition tc_init t := Node (mkInfo t 0 0) nil.

Definition tc_rootinfo tc :=
  let: Node ni _ := tc in ni.

Definition tc_rootchn tc :=
  let: Node _ chn := tc in chn.

Definition tc_roottid tc := info_tid (tc_rootinfo tc).

Definition tc_rootclk tc := info_clk (tc_rootinfo tc).

Definition tc_rootaclk tc := info_aclk (tc_rootinfo tc).

Global Arguments tc_roottid !_ /.
Global Arguments tc_rootclk !_ /.
Global Arguments tc_rootaclk !_ /.

Fact tc_rootinfo_tid_inj : forall x y, tc_rootinfo x = tc_rootinfo y -> tc_roottid x = tc_roottid y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

Fact tc_rootinfo_clk_inj : forall x y, tc_rootinfo x = tc_rootinfo y -> tc_rootclk x = tc_rootclk y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

(* this is_left is for better printing of find (has_same_tid t) *)

Definition has_same_tid t tc := is_left (thread_eqdec (tc_roottid tc) t).

Global Arguments has_same_tid _ !_ /.

Fact has_same_tid_true t tc : has_same_tid t tc = true <-> t = tc_roottid tc.
Proof. unfold has_same_tid. destruct (thread_eqdec (tc_roottid tc) t) as [ <- | ]; simpl; intuition congruence. Qed.

Fact has_same_tid_false t tc : has_same_tid t tc = false <-> t <> tc_roottid tc.
Proof. unfold has_same_tid. destruct (thread_eqdec (tc_roottid tc) t) as [ <- | ]; simpl; intuition congruence. Qed.

(* only for some domain-based reasoning; not for finding *)

Fixpoint tc_flatten tc :=
  let: Node ni chn := tc in tc :: (List.flat_map tc_flatten chn).

Definition subtc tc1 tc2 : Prop := In tc1 (tc_flatten tc2).

Fact tc_flatten_self_in tc : In tc (tc_flatten tc).
Proof. destruct tc as [? ?]. simpl. now left. Qed.

Fact tc_flatten_root_chn_split tcs :
  Permutation.Permutation (flat_map tc_flatten tcs)
    (tcs ++ (flat_map tc_flatten (flat_map tc_rootchn tcs))).
Proof.
  induction tcs as [ | [ni chn] tcs IH ].
  1: constructor.
  simpl.
  constructor.
  rewrite -> flat_map_app.
  etransitivity.
  2: apply Permutation.Permutation_app_swap_app.
  now apply Permutation.Permutation_app_head.
Qed.

Fact tc_height_subtree_lt tc :
  Forall (fun tc' => tc_height tc' < tc_height tc) (flat_map tc_flatten (tc_rootchn tc)).
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  rewrite -> List.Forall_forall in IH |- *.
  simpl.
  setoid_rewrite -> in_flat_map.
  intros sub ([ni_ch chn_ch] & Hin_ch & Hin).
  simpl in Hin.
  specialize (IH _ Hin_ch).
  rewrite -> List.Forall_forall in IH.
  simpl in IH.
  unfold lt in IH |- *.
  assert (tc_height (Node ni_ch chn_ch) <= list_max (map tc_height chn)) as H.
  {
    eapply tc_height_le; eauto.
  }
  destruct Hin as [ <- | Hin ].
  - lia.
  - transitivity (S (list_max (map tc_height chn_ch))).
    1: now apply IH.
    simpl in H.
    lia.
Qed.

(* a height-based argument *)

Fact self_not_in_tc_flatten_chn ni chn : ~ In (Node ni chn) (flat_map tc_flatten chn).
Proof.
  pose proof (tc_height_subtree_lt (Node ni chn)) as Hlt.
  simpl in Hlt.
  rewrite -> List.Forall_forall in Hlt.
  intros Hin.
  apply Hlt in Hin.
  simpl in Hin.
  lia.
Qed.

Definition tc_getnode t tc := find (has_same_tid t) (tc_flatten tc).

Global Arguments tc_getnode _ !_ /.

Tactic Notation "tc_getnode_unfold" :=
  repeat match goal with
  | |- context[find (has_same_tid ?t) (tc_flatten ?ch ++ flat_map tc_flatten ?chn)] =>
    rewrite -> find_app; change (find (has_same_tid t) (tc_flatten ch)) with (tc_getnode t ch)
  end.

(* the same as paper, use 0 as default clk *)

Definition tc_getclk t tc :=
  match tc_getnode t tc with
  | Some res => tc_rootclk res
  | _ => 0
  end.

Section Old_Complaints.

  Fixpoint tc_getnode_deprecated t tc :=
    let: Node ni chn := tc in 
    if thread_eqdec t (info_tid ni)
    then Some tc
    else find_first_some (map (tc_getnode_deprecated t) chn).

  Fact tc_getnode_deprecated_has_tid t tc res
    (Hres : tc_getnode_deprecated t tc = Some res) : tc_roottid res = t.
  Proof.
    induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
    simpl in Hres.
    destruct (thread_eqdec t u) as [ <- | Hneq ].
    1:{
      simpl.
      injection Hres as <-.
      intuition.
    }
    rewrite -> find_first_some_correct in Hres.
    destruct (find isSome (map (tc_getnode_deprecated t) chn)) as [ res_chn | ] eqn:E.
    - apply find_some in E.
      destruct res_chn; [ injection Hres as -> | discriminate ].
      destruct E as (E & _).
      rewrite -> in_map_iff in E.
      rewrite -> List.Forall_forall in IH.
      firstorder.
    - discriminate.
  Qed.

  (* essentially not useful ... only add redundancy *)

  Fact tc_getnode_deprecated_useless t tc : tc_getnode_deprecated t tc = tc_getnode t tc.
  Proof.
    induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
    simpl.
    destruct (thread_eqdec t u) as [ <- | ] eqn:E.
    - now rewrite -> E.
    - destruct (thread_eqdec u t) as [ -> | ].
      1: congruence.
      simpl.
      rewrite -> find_first_some_correct.
      clear -IH.
      induction chn as [ | ch chn IH' ].
      1: auto.
      apply Forall_cons_iff in IH.
      destruct IH as (HH & IH).
      specialize (IH' IH).
      simpl.
      tc_getnode_unfold.
      destruct (tc_getnode_deprecated t ch) as [ res | ] eqn:E; simpl.
      + now rewrite <- HH.
      + now rewrite <- HH.
  Qed.

End Old_Complaints.

(* Forall over all subtrees *)
(* it is hard to define this as a recursive function, so use indprop instead *)

Inductive Foralltc (P : treeclock -> Prop) : treeclock -> Prop :=
  Foralltc_intro : forall ni chn, 
    P (Node ni chn) -> Forall (Foralltc P) chn -> Foralltc P (Node ni chn). 

Fact Foralltc_cons_iff P ni chn :
  Foralltc P (Node ni chn) <-> (P (Node ni chn) /\ Forall (Foralltc P) chn).
Proof.
  split; intros.
  - now inversion H.
  - now apply Foralltc_intro.
Qed.

Fact Foralltc_self P tc (H : Foralltc P tc) : P tc.
Proof. destruct tc. now apply Foralltc_cons_iff in H. Qed.

Lemma Foralltc_impl (P Q : treeclock -> Prop) (Hpq : forall tc, P tc -> Q tc) tc 
  (H : Foralltc P tc) : Foralltc Q tc.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  rewrite -> Foralltc_cons_iff in H |- *.
  destruct H as (H & H0).
  split.
  - now apply Hpq.
  - rewrite -> Forall_forall in *. 
    firstorder. 
Qed.

Lemma Foralltc_and (P Q : treeclock -> Prop) tc :
  Foralltc (fun tc => P tc /\ Q tc) tc <-> Foralltc P tc /\ Foralltc Q tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> ! Foralltc_cons_iff, -> ! List.Forall_forall.
  rewrite -> List.Forall_forall in IH.
  firstorder.
Qed.

Lemma Foralltc_idempotent (P : treeclock -> Prop) tc :
  Foralltc (Foralltc P) tc <-> Foralltc P tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> ! Foralltc_cons_iff, -> ! List.Forall_forall.
  rewrite -> List.Forall_forall in IH.
  firstorder.
Qed.

Lemma Foralltc_Forall_subtree (P : treeclock -> Prop) tc :
  Foralltc P tc <-> Forall P (tc_flatten tc).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> ! Foralltc_cons_iff, List.Forall_cons_iff, -> ! List.Forall_forall.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  apply and_iff_compat_l.
  split; intros H.
  - intros sub Hin.
    apply in_flat_map in Hin.
    firstorder.
  - intros ch Hin_ch.
    apply IH.
    1: assumption.
    intros sub Hin.
    eapply H, in_flat_map; eauto.
Qed.

Corollary Foralltc_trivial (P : treeclock -> Prop) (H : forall tc, P tc) tc : Foralltc P tc.
Proof. now apply Foralltc_Forall_subtree, List.Forall_forall. Qed.

Inductive prefixtc : treeclock -> treeclock -> Prop :=
  prefixtc_intro : forall ni chn chn_sub prefix_chn, 
    list.sublist chn_sub chn ->
    Forall2 prefixtc prefix_chn chn_sub ->
    prefixtc (Node ni prefix_chn) (Node ni chn).

Fact prefixtc_inv ni1 ni2 chn1 chn2 (Hprefix: prefixtc (Node ni1 chn1) (Node ni2 chn2)) :
  ni1 = ni2 /\ exists chn2_sub, list.sublist chn2_sub chn2 /\ Forall2 prefixtc chn1 chn2_sub.
Proof. inversion Hprefix; subst. firstorder. Qed.

Fact prefixtc_rootinfo_same tc tc' (Hprefix : prefixtc tc tc') :
  tc_rootinfo tc = tc_rootinfo tc'.
Proof. 
  destruct tc, tc'.
  apply prefixtc_inv in Hprefix.
  intuition congruence.
Qed.

#[export] Instance prefixtc_refl : Reflexive prefixtc.
Proof.
  hnf.
  intros tc.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  econstructor.
  1: reflexivity.
  now apply list.Forall_Forall2_diag.
Qed.

Fact prefixtc_nil_l ni chn : prefixtc (Node ni nil) (Node ni chn).
Proof.
  econstructor.
  2: reflexivity.
  apply list.sublist_nil_l.
Qed.

Lemma prefixtc_flatten_sublist tc1 tc2 (Hprefix : prefixtc tc1 tc2) :
  list.sublist (map tc_rootinfo (tc_flatten tc1)) (map tc_rootinfo (tc_flatten tc2)).
Proof.
  revert tc2 Hprefix.
  induction tc1 as [ni chn1 IH] using treeclock_ind_2; intros.
  destruct tc2 as [ni2 chn2].
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (<- & (chn2_sub & Hsub & Hprefix)).
  simpl.
  apply list.sublist_skip.
  (* seems only induction works here ... *)
  revert chn1 IH Hprefix.
  induction Hsub as [ | ch2 chn2_sub chn2 Hsub IHsub | ch2 chn2_sub chn2 Hsub IHsub ]; intros.
  - destruct chn1; inversion Hprefix.
    reflexivity.
  - destruct chn1 as [ | ch1 chn1 ]. 
    1: inversion Hprefix.
    apply list.Forall2_cons in Hprefix.
    destruct Hprefix as (Hpf & Hprefix).
    apply Forall_cons_iff in IH.
    destruct IH as (IHsingle & IH).
    simpl.
    rewrite -> ! map_app.
    apply list.sublist_app.
    all: firstorder.
  - simpl.
    rewrite -> map_app.
    apply list.sublist_inserts_l.
    firstorder.
Qed.
(*
Fact tc_getnode_some t tc res
  (Hres : tc_getnode t tc = Some res) : In res (tc_flatten tc) /\ tc_roottid res = t.
Proof.
  apply find_some in Hres.
  destruct res as [(u, ?, ?) ?].
  simpl in Hres |- *.
  now destruct (thread_eqdec u t).
  (* 
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  simpl in Hres.
  destruct (thread_eqdec t u) as [ <- | Hneq ].
  1:{
    simpl.
    injection Hres as <-.
    intuition.
  }
  rewrite -> find_first_some_correct in Hres.
  destruct (find isSome (map (tc_getnode t) chn)) as [ res_chn | ] eqn:E.
  - apply find_some in E.
    destruct res_chn; [ injection Hres as -> | discriminate ].
    destruct E as (E & _).
    (* OK. after some attempts now I do not think I can solve this easily. *)
    simpl.
    rewrite -> in_map_iff in E.
    rewrite -> in_flat_map.
    rewrite -> List.Forall_forall in IH.
    firstorder.
  - discriminate.
  *)
Qed.

(* just an excerpt of the proof above ... *)

Fact tc_getnode_some_list t chn res
  (Hres : In (Some res) (map (tc_getnode t) chn)) : In res (flat_map tc_flatten chn) /\ tc_roottid res = t.
Proof.
  rewrite -> in_map_iff in Hres.
  destruct Hres as (ch & Hres & Hin_ch).
  apply tc_getnode_some in Hres.
  rewrite -> in_flat_map.
  firstorder.
Qed.

Fact tc_getnode_complete t tc sub (Hin : In sub (tc_flatten tc))
  (Et : tc_roottid sub = t) : exists res, tc_getnode t tc = Some res.
Proof.
  destruct (tc_getnode t tc) eqn:E.
  1: eauto.
  eapply find_none in E.
  2: apply Hin.
  destruct sub as [(u, ?, ?) ?].
  simpl in Et, E.
  now destruct (thread_eqdec u t).
  (*
  revert sub Hin Et.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  simpl in Hin |- *.
  destruct (thread_eqdec t u) as [ <- | Hneq ].
  1: eauto.
  destruct Hin as [ <- | Hin ].
  1: simpl in Et; congruence.
  apply in_flat_map in Hin.
  destruct Hin as (ch & Hin_ch & Hin_sub).
  rewrite -> List.Forall_forall in IH.
  specialize (IH _ Hin_ch _ Hin_sub Et).
  destruct IH as (res_ch & IH).
  rewrite -> find_first_some_correct.
  destruct (find isSome (map (tc_getnode t) chn)) as [ res_chn | ] eqn:E.
  - apply find_some in E.
    destruct res_chn; [ eauto | intuition discriminate ].
  - eapply find_none in E; eauto.
    2: apply in_map, Hin_ch.
    now destruct (tc_getnode t ch).
  *)
Qed.

Fact tc_getnode_complete_nodup t tc sub (Hin : In sub (tc_flatten tc))
  (Et : tc_roottid sub = t) (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc))) : 
  tc_getnode t tc = Some sub.
Proof.
  pose proof (tc_getnode_complete _ _ _ Hin Et) as (res & Hres).
  pose proof Hres as Hres_backup.
  apply tc_getnode_some in Hres.
  destruct Hres as (Hin' & <-).
  eapply NoDup_map_inj in Hnodup.
  2: apply Et.
  2-3: assumption.
  now subst.
Qed.

(* just an excerpt of the proof above ... *)

Fact tc_getnode_complete_list t chn sub
  (Hin_flat : In sub (flat_map tc_flatten chn))
  (Et : tc_roottid sub = t) : exists res, In (Some res) (map (tc_getnode t) chn).
Proof.
  apply in_flat_map in Hin_flat.
  destruct Hin_flat as (ch & Hin_ch & Hin_flat).
  eapply tc_getnode_complete in Hin_flat.
  2: apply Et.
  destruct Hin_flat as (res & Hin_flat).
  setoid_rewrite -> in_map_iff.
  eauto.
Qed.

(* TODO should be a part of a solver ... *)

Fact tc_getnode_ch_in_chn t ch chn (Hres : tc_getnode t ch) (Hin_ch : In ch chn) :
  exists res, In (Some res) (map (tc_getnode t) chn).
Proof.
  destruct (tc_getnode t ch) as [ res | ] eqn:E; [ | discriminate ].
  apply tc_getnode_some in E.
  eapply tc_getnode_complete_list.
  2: apply (proj2 E).
  eapply in_flat_map_conv; intuition eauto.
Qed.

Fact tc_getnode_complete_nodup_list t chn sub
  (Hin_flat : In sub (flat_map tc_flatten chn))
  (Et : tc_roottid sub = t) 
  (Hnodup : List.NoDup (map tc_roottid (flat_map tc_flatten chn))) : 
  (* the final statement can be stronger ... *)
  forall ch res, In ch chn -> tc_getnode t ch = Some res -> sub = res.
Proof.
  pose proof (tc_getnode_complete_list _ _ _ Hin_flat Et) as (res & Hres).
  pose proof Hres as Hres_backup.
  apply tc_getnode_some_list in Hres.
  destruct Hres as (Hin_flat' & <-).
  pose proof Hnodup as Hnodup_backup.
  eapply NoDup_map_inj in Hnodup.
  2: apply Et.
  2-3: assumption.
  subst.
  rewrite -> in_map_iff in Hres_backup.
  destruct Hres_backup as (ch & Hres & Hin_ch).
  intros ch' res' Hin_ch' Hres'.
  apply tc_getnode_some in Hres, Hres'.
  destruct Hres' as (Hin' & Et').
  assert (In res' (flat_map tc_flatten chn)) by (eapply in_flat_map; eauto).
  eapply NoDup_map_inj in Hnodup_backup.
  2: apply Et'.
  2-3: assumption.
  now subst.
Qed.

Corollary tc_getnode_none t tc (Hres : tc_getnode t tc = None) : 
  forall sub, In sub (tc_flatten tc) -> tc_roottid sub <> t.
Proof.
  intros sub Hin <-.
  apply tc_getnode_complete with (t:=(tc_roottid sub)) in Hin; auto.
  firstorder congruence.
Qed.
*)
(*
Corollary tc_getnode_subtc_iff t tc : 
  In t (map tc_roottid (tc_flatten tc)) <-> tc_getnode t tc.
Proof.
  rewrite -> in_map_iff.
  split.
  - intros (sub & <- & Hin).
    eapply tc_getnode_complete in Hin.
    2: reflexivity.
    destruct Hin as (? & H).
    now rewrite -> H.
  - destruct (tc_getnode t tc) as [ res | ] eqn:E.
    2: now unfold isSome.
    intros _.
    apply tc_getnode_some in E.
    firstorder.
Qed.
*)
(* TODO re-prove the above things *)

Lemma tc_getnode_in_iff t tcs : 
  In t (map tc_roottid tcs) <-> find (has_same_tid t) tcs.
Proof.
  rewrite -> in_map_iff.
  split.
  - intros (sub & <- & Hin).
    destruct (find (has_same_tid (tc_roottid sub)) tcs) eqn:E.
    1: auto.
    eapply find_none in E.
    2: apply Hin.
    now rewrite -> has_same_tid_false in E.
  - destruct (find (has_same_tid t) tcs) as [ res | ] eqn:E.
    2: intros; discriminate.
    intros _.
    apply find_some in E.
    destruct E as (Hin & E).
    rewrite -> has_same_tid_true in E.
    eauto.
Qed.

Corollary tc_getnode_subtc_iff t tc : 
  In t (map tc_roottid (tc_flatten tc)) <-> tc_getnode t tc.
Proof. apply tc_getnode_in_iff. Qed.

(* TODO how to deal with the above things? *)
(*
Lemma find_tid_unique_result [A : Type] (f : treeclock -> A)
  (Hf : forall x y, f x = f y -> tc_roottid x = tc_roottid y)
  tcs (Hnodup : NoDup (map tc_roottid (flat_map tc_flatten tcs)))
  res (Hin : In (f res) (map f (flat_map tc_flatten tcs))) 
  res' (Hres' : find (has_same_tid (tc_roottid res)) (flat_map tc_flatten tcs) = Some res') :
  f res' = f res.
Proof.
  rewrite -> in_map_iff in Hin.
  destruct Hin as (sub & Ef & Hin_flat).
  apply find_some in Hres'.
  destruct Hres' as (Hin_flat' & Et').
  rewrite -> has_same_tid_true in Et'.
  pose proof (Hf _ _ Ef) as Et.
  rewrite <- Ef.
  f_equal.
  eapply NoDup_map_inj; eauto.
  congruence.
Qed.

Corollary find_tid_unique_result_full [A : Type] (f : treeclock -> A)
  (Hf : forall x y, f x = f y -> tc_roottid x = tc_roottid y)
  tcs (Hnodup : NoDup (map tc_roottid (flat_map tc_flatten tcs)))
  res (Hin : In (f res) (map f (flat_map tc_flatten tcs))) : 
  exists res', find (has_same_tid (tc_roottid res)) (flat_map tc_flatten tcs) = Some res' /\
  f res' = f res.
Proof.
  destruct (find (has_same_tid (tc_roottid res)) (flat_map tc_flatten tcs)) as [ res' | ] eqn:E.
  2:{
    rewrite -> in_map_iff in Hin.
    destruct Hin as (sub & Ef & Hin).
    eapply find_none in E.
    2: apply Hin.
    rewrite -> has_same_tid_false in E.
    firstorder congruence.
  }
  exists res'.
  split; [ reflexivity | ].
  eapply find_tid_unique_result; eauto.
Qed.

(* (full or not) * (single or not) * every instantiation *)

Corollary find_tid_unique_result_full_single [A : Type] (f : treeclock -> A)
  (Hf : forall x y, f x = f y -> tc_roottid x = tc_roottid y)
  tc (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  res (Hin : In (f res) (map f (tc_flatten tc))) : 
  exists res', find (has_same_tid (tc_roottid res)) (tc_flatten tc) = Some res' /\
  f res' = f res.
Proof. 
  setoid_rewrite -> flat_map_single. eapply find_tid_unique_result_full; eauto. 
  all: now rewrite <- flat_map_single.
Qed.
*)
Fact tid_nodup_find_self tcs (Hnodup : List.NoDup (map tc_roottid tcs)) :
  Forall (fun tc => find (has_same_tid (tc_roottid tc)) tcs = Some tc) tcs.
Proof.
  induction tcs as [ | tc tcs IH ].
  1: constructor.
  simpl in Hnodup |- *.
  apply NoDup_cons_iff in Hnodup.
  destruct Hnodup as (Hnotin & Hnodup).
  specialize (IH Hnodup).
  constructor.
  - unfold has_same_tid.
    destruct (thread_eqdec (tc_roottid tc) (tc_roottid tc)).
    2: contradiction.
    now simpl.
  - rewrite -> List.Forall_forall in IH |- *.
    intros tc' Hin.
    destruct (has_same_tid (tc_roottid tc') tc) eqn:E.
    + rewrite -> has_same_tid_true in E.
      apply in_map with (f:=tc_roottid) in Hin.
      congruence.
    + now apply IH.
Qed.

Corollary tid_nodup_find_self_sub tc (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc))) 
  sub (Hin_sub : In sub (tc_flatten tc)) :
  base.fmap tc_rootinfo (tc_getnode (tc_roottid sub) tc) = Some (tc_rootinfo sub).
Proof.
  pose proof (tid_nodup_find_self (tc_flatten tc) Hnodup) as H.
  rewrite -> List.Forall_forall in H.
  specialize (H _ Hin_sub).
  unfold tc_getnode.
  now rewrite -> H.
Qed.

(*
Corollary find_tid_unique_info tcs 
  (Hnodup : NoDup (map tc_roottid (flat_map tc_flatten tcs)))
  res (Hin : In (tc_rootinfo res) (map tc_rootinfo (flat_map tc_flatten tcs))) 
  res' (Hres' : find (has_same_tid (tc_roottid res)) (flat_map tc_flatten tcs) = Some res') :
  tc_rootinfo res' = tc_rootinfo res.
Proof.
  eapply find_tid_unique_result; eauto.
  intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence.
Qed.
*)
(* domain inclusion property of prefix *)
(*
Lemma dom_incl_tc_getnode_impl tc tc' 
  (Hincl : incl (map tc_rootinfo (tc_flatten tc)) (map tc_rootinfo (tc_flatten tc')))
  t res (Hres : tc_getnode t tc = Some res) : exists res', tc_getnode t tc' = Some res'.
Proof.
  (* destruct (tc_getnode t tc) as [ res | ] eqn:E.
  2: discriminate. *)
  apply tc_getnode_some in Hres.
  destruct Hres as (Hin & Et).
  hnf in Hincl.
  repeat setoid_rewrite -> in_map_iff in Hincl.
  specialize (Hincl (tc_rootinfo res)).
  removehead Hincl.
  2: now exists res.
  destruct Hincl as (res' & Einfo & Hin').
  assert (tc_roottid res' = t) as Et' by (destruct res as [(?, ?, ?) ?], res' as [(?, ?, ?) ?]; simpl in *; intuition congruence).
  eapply tc_getnode_complete in Hin'; eauto.
Qed.

Corollary prefix_tc_getnode_impl tc tc' (Hprefix : prefixtc tc tc')
  t res (Hres : tc_getnode t tc = Some res) : exists res', tc_getnode t tc' = Some res'.
Proof.
  revert Hres.
  apply dom_incl_tc_getnode_impl.
  hnf.
  intros ?.
  now apply sublist_In, prefixtc_flatten_sublist.
Qed.

(* since this is for prefix, maybe not entire subtree equal *)

Corollary prefix_tc_getnode_nodup_sameinfo tc tc' (Hprefix : prefixtc tc tc')
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc')))
  t res (Hres : tc_getnode t tc = Some res) 
  res' (Hres' : tc_getnode t tc' = Some res') : tc_rootinfo res = tc_rootinfo res'.
Proof.
  pose proof (tc_getnode_some _ _ _ Hres) as (Hin & <-).
  pose proof (tc_getnode_some _ _ _ Hres') as (Hin' & Et).
  apply in_map with (f:=tc_rootinfo) in Hin, Hin'.
  pose proof (prefixtc_flatten_sublist _ _ Hprefix) as HH.
  eapply sublist_In in Hin.
  2: apply HH.
  unfold tc_roottid in Hnodup.
  rewrite <- map_map in Hnodup.
  eapply NoDup_map_inj in Hnodup.
  2: apply Et.
  2-3: assumption.
  congruence.
Qed.
*)
(*
Notation "tc '@' t" := (tc_getnode t tc) (at level 50).
Notation "tc '@clk' t" := (tc_getclk t tc) (at level 50).
*)

(* return a tree instead of a stack? *)
(* compute prefix(tc') that should be updated in tc; assume that 
    at least the root of tc' must be updated in tc
*)
(* considering the simulation with imperative code, maybe this process 
    should not be too declarative. therefore takes a recursion on list
    as a sub-procedure
*)

Fixpoint tc_get_updated_nodes_join tc tc' : treeclock :=
  let fix tc_get_updated_nodes_join_aux tc u' chn_u' : list treeclock :=
  match chn_u' with
  | nil => nil
  | tc' :: chn_u'' => 
    let: Node (mkInfo v' clk_v' aclk_v') chn_v' := tc' in
    (* <? is slightly hard to use *)
    if clk_v' <=? (tc_getclk v' tc)
    then 
      (if aclk_v' <=? (tc_getclk u' tc)
        then nil
        else (tc_get_updated_nodes_join_aux tc u' chn_u''))
    else (tc_get_updated_nodes_join tc tc') :: (tc_get_updated_nodes_join_aux tc u' chn_u'')
  end in
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (info_tid info_u') chn_u')
.

(* TODO this is awkward. the inner aux must be an external function to work with
    since implementing it as a mutual recursion does not pass the arg decrease check *)

Fixpoint tc_get_updated_nodes_join_aux tc u' chn_u' : list treeclock :=
  match chn_u' with
  | nil => nil
  | tc' :: chn_u'' => 
    let: Node (mkInfo v' clk_v' aclk_v') chn_v' := tc' in
    if clk_v' <=? (tc_getclk v' tc)
    then 
      (if aclk_v' <=? (tc_getclk u' tc)
        then nil
        else (tc_get_updated_nodes_join_aux tc u' chn_u''))
    else (tc_get_updated_nodes_join tc tc') :: (tc_get_updated_nodes_join_aux tc u' chn_u'')
  end.

Lemma tc_get_updated_nodes_join_eta tc tc' : 
  tc_get_updated_nodes_join tc tc' = 
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (info_tid info_u') chn_u').
Proof. destruct tc'. reflexivity. Qed.

Tactic Notation "tc_get_updated_nodes_join_unfold" :=
  cbn delta -[tc_get_updated_nodes_join] iota beta;
  rewrite -> tc_get_updated_nodes_join_eta.

Tactic Notation "tc_get_updated_nodes_join_unfold" "in_" hyp(H) :=
  cbn delta -[tc_get_updated_nodes_join] iota beta in H;
  rewrite -> tc_get_updated_nodes_join_eta in H.

(* given a tree and a list of targets, return a pivot tree and a list of splitted trees *)

Fixpoint tc_detach_nodes subtree_tc' tc : treeclock * list treeclock :=
  let: Node ni chn := tc in
  let: (new_chn, res) := List.split (map (tc_detach_nodes subtree_tc') chn) in
  let: (res', new_chn') := List.partition (fun tc' => tc_getnode (tc_roottid tc') subtree_tc')
    new_chn in
  (Node ni new_chn', (List.concat res) ++ res').

(* return a reconstructed tree to be added into the pivot *)

Fixpoint tc_attach_nodes forest tc' : treeclock :=
  let: Node info_u' chn' := tc' in
  (* try finding a tree in the forest with the same root thread *)
  (* let: u_pre := List.find (fun tc => thread_eqdec (tc_roottid tc) (info_tid info_u')) forest in *)
  let: u_pre := List.find (has_same_tid (info_tid info_u')) forest in
  let: chn_u := (match u_pre with Some u => tc_rootchn u | None => nil end) in
  (* for u', inherit clk and aclk anyway; prepend all children of u' *)
  Node info_u' ((map (tc_attach_nodes forest) chn') ++ chn_u).

Definition tc_join tc tc' :=
  let: mkInfo z' clk_z' aclk_z' := tc_rootinfo tc' in
  if clk_z' <=? (tc_getclk z' tc)
  then tc
  else 
    let: subtree_tc' := tc_get_updated_nodes_join tc tc' in
    let: (pivot, forest) := tc_detach_nodes subtree_tc' tc in
    let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
    let: Node info_z chn_z := pivot in 
    Node info_z ((Node (mkInfo w clk_w (info_clk info_z)) chn_w) :: chn_z).

Definition tc_ge (tc_larger tc : treeclock) : Prop := 
  Foralltc (fun tc'' => let: Node (mkInfo w clk_w _) _ := tc'' in 
    clk_w <= tc_getclk w tc_larger) tc.

Definition dmono_single (tc_larger : treeclock) tc : Prop :=
  let: Node (mkInfo u clk_u _) _ := tc in
  clk_u <= (tc_getclk u tc_larger) -> tc_ge tc_larger tc.

Definition imono_single (tc_larger : treeclock) tc: Prop :=
  let: Node (mkInfo u _ _) chn := tc in
  Forall (fun tc_v => let: Node (mkInfo v _ aclk_v) _ := tc_v in
    aclk_v <= (tc_getclk u tc_larger) -> tc_ge tc_larger tc_v) chn. 

Record tc_respect tc (tc' : treeclock) : Prop := {
  dmono : Foralltc (dmono_single tc') tc;
  imono : Foralltc (imono_single tc') tc
}.

(*
(* this requires tc to be map-like *)
#[export] Instance tc_ge_refl : Reflexive tc_ge.
*)

Fact tc_ge_all_getclk_ge tc tc_larger (H : tc_ge tc_larger tc) 
  t : tc_getclk t tc <= tc_getclk t tc_larger.
Proof.
  unfold tc_getclk at 1.
  destruct (tc_getnode t tc) as [ [(t', clk', aclk') chn'] | ] eqn:E.
  - apply find_some in E.
    rewrite -> has_same_tid_true in E.
    simpl in E.
    destruct E as (Hin' & <-).
    hnf in H.
    rewrite -> Foralltc_Forall_subtree, List.Forall_forall in H.
    specialize (H _ Hin').
    firstorder.
  - lia.
Qed.

Fact all_getclk_ge_tc_ge tc tc_larger
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc)))
  (H : forall t, tc_getclk t tc <= tc_getclk t tc_larger) :
  tc_ge tc_larger tc.
Proof.
  unfold tc_ge.
  pose proof (tid_nodup_find_self _ Hnodup) as Hself.
  rewrite -> Foralltc_Forall_subtree.
  rewrite -> List.Forall_forall in Hself |- *.
  intros [(t, clk, aclk) chn] Hin.
  specialize (Hself _ Hin).
  simpl in Hself.
  replace clk with (tc_getclk t tc).
  2: unfold tc_getclk, tc_getnode; now rewrite -> Hself.
  now apply H.
Qed.

#[export] Instance tc_ge_trans : Transitive tc_ge.
Proof.
  hnf.
  intros tc_x tc_y tc_z Hge1 Hge2.
  hnf in Hge2 |- *.
  rewrite -> Foralltc_Forall_subtree, List.Forall_forall in Hge2 |- *.
  intros [(t, clk, aclk) chn] Hin.
  specialize (Hge2 _ Hin).
  simpl in Hge2.
  pose proof (tc_ge_all_getclk_ge _ _ Hge1 t).
  lia.
Qed.

Section Pointwise_Treeclock.

  Variables (tc1 tc2 tc_max : treeclock).
  Hypotheses (Hpmax : forall t, tc_getclk t tc_max = Nat.max (tc_getclk t tc1) (tc_getclk t tc2))
    (Hnodup1 : List.NoDup (map tc_roottid (tc_flatten tc1)))
    (Hnodup2 : List.NoDup (map tc_roottid (tc_flatten tc2))).

  Fact tc_ge_from_pointwise_max : tc_ge tc_max tc1 /\ tc_ge tc_max tc2.
  Proof.
    eapply all_getclk_ge_tc_ge with (tc_larger:=tc_max) in Hnodup1, Hnodup2.
    2-3: intros t; rewrite -> Hpmax; lia.
    intuition.
  Qed.

  Lemma dmono_single_pointwise_max_preserve tc 
    (Hdmono1 : dmono_single tc1 tc)
    (Hdmono2 : dmono_single tc2 tc) :
    dmono_single tc_max tc.
  Proof.
    hnf in Hdmono1, Hdmono2 |- *.
    destruct tc as [(t, clk, aclk) chn].
    intros Hle.
    pose proof tc_ge_from_pointwise_max as Hge.
    rewrite -> Hpmax in Hle.
    apply Nat.max_le in Hle.
    destruct Hle as [ Hle | Hle ].
    1: specialize (Hdmono1 Hle); transitivity tc1; auto.
    2: specialize (Hdmono2 Hle); transitivity tc2; auto.
    all: intuition.
  Qed.

  Lemma imono_single_pointwise_max_preserve tc 
    (Himono1 : imono_single tc1 tc)
    (Himono2 : imono_single tc2 tc) :
    imono_single tc_max tc.
  Proof.
    hnf in Himono1, Himono2 |- *.
    destruct tc as [(u, clk_u, aclk_u) chn].
    rewrite -> List.Forall_forall in Himono1, Himono2 |- *.
    intros [(v, clk_v, aclk_v) chn_v] Hin Hle.
    pose proof tc_ge_from_pointwise_max as Hge.
    rewrite -> Hpmax in Hle.
    apply Nat.max_le in Hle.
    destruct Hle as [ Hle | Hle ].
    1: specialize (Himono1 _ Hin Hle); transitivity tc1; auto.
    2: specialize (Himono2 _ Hin Hle); transitivity tc2; auto.
    all: intuition.
  Qed.

  Corollary tc_respect_pointwise_max_preserve tc 
    (Hrespect1 : tc_respect tc tc1)
    (Hrespect2 : tc_respect tc tc2) :
    tc_respect tc tc_max.
  Proof.
    destruct Hrespect1 as (Hdmono1 & Himono1), Hrespect2 as (Hdmono2 & Himono2).
    constructor.
    - rewrite -> Foralltc_Forall_subtree, List.Forall_forall in Hdmono1, Hdmono2 |- *.
      intros sub Hin.
      apply dmono_single_pointwise_max_preserve; firstorder.
    - rewrite -> Foralltc_Forall_subtree, List.Forall_forall in Himono1, Himono2 |- *.
      intros sub Hin.
      apply imono_single_pointwise_max_preserve; firstorder.
  Qed.

End Pointwise_Treeclock.

Fact tc_respect_chn ni chn tc' (H : tc_respect (Node ni chn) tc') :
  Forall (fun ch => tc_respect ch tc') chn.
Proof.
  rewrite -> List.Forall_forall.
  intros ch Hin.
  constructor.
  1: apply dmono in H.
  2: apply imono in H.
  all: rewrite -> Foralltc_cons_iff, List.Forall_forall in H.
  all: firstorder.
Qed.

Definition tc_chn_aclk_decsorted tc := 
  let: Node _ chn := tc in
  StronglySorted ge (map tc_rootaclk chn). 

Definition tc_chn_aclk_ub tc: Prop :=
  let: Node (mkInfo _ clk_u _) chn := tc in
  Forall (fun tc' => tc_rootaclk tc' <= clk_u) chn. 

(* TODO make this record or class? *)

Record tc_shape_inv tc : Prop := {
  (* tid_nodup: List.NoDup (map info_tid (tc_flatten tc)); *)
  tid_nodup: List.NoDup (map tc_roottid (tc_flatten tc));
  aclk_upperbound: Foralltc tc_chn_aclk_ub tc;
  aclk_decsorted: Foralltc tc_chn_aclk_decsorted tc
  (* this is only useful to guarantee that the domain of join is the union of two operands *)
  (* clk_lowerbound: Foralltc (fun tc' => 0 < tc_rootclk tc') tc *)
}.

Lemma tid_nodup_chn_ch chn ch
  (H : List.NoDup (map tc_roottid (flat_map tc_flatten chn)))
  (Hin : In ch chn) : List.NoDup (map tc_roottid (tc_flatten ch)).
Proof.
  rewrite -> flat_map_concat_map, -> concat_map, -> map_map in H.
  apply NoDup_concat in H.
  rewrite -> List.Forall_map, List.Forall_forall in H.
  now apply H.
Qed.

(* this essentially tells that tid_nodup iff all subtrees are tid_nodup *)

Lemma tid_nodup_Foralltc_id tc : 
  List.NoDup (map tc_roottid (tc_flatten tc)) <->
  Foralltc (fun tc => List.NoDup (map tc_roottid (tc_flatten tc))) tc.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> Foralltc_cons_iff.
  simpl.
  split; [ | intuition ].
  intros H.
  split.
  1: assumption.
  rewrite -> List.Forall_forall in IH |- *.
  intros tc Hin.
  rewrite <- IH.
  2: assumption.
  apply NoDup_cons_iff in H.
  destruct H as (_ & H).
  now eapply tid_nodup_chn_ch; eauto.
Qed.

Lemma tid_nodup_prefix_preserve tc tc' (Hprefix : prefixtc tc tc') 
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc'))) : 
  List.NoDup (map tc_roottid (tc_flatten tc)).
Proof.
  (* use prefix domain *)
  revert tc' Hprefix Hnodup.
  induction tc as [(u, clk, aclk) chn_sp IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn].
  pose proof (prefixtc_flatten_sublist _ _ Hprefix) as Hdomsub. 
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  injection Htmp as <-.
  subst clk' aclk'.
  simpl in Hnodup, Hdomsub |- *.
  apply sublist_map with (f:=info_tid) in Hdomsub.
  simpl in Hdomsub.
  rewrite -> ! map_map in Hdomsub.
  fold tc_roottid in Hdomsub.
  eapply sublist_NoDup; eauto.
Qed.

Lemma tid_nodup_root_chn_split tcs
  (Hnodup : List.NoDup (map tc_roottid (flat_map tc_flatten tcs))) : 
  List.NoDup (map tc_roottid tcs) /\ List.NoDup (map tc_roottid (flat_map tc_flatten (flat_map tc_rootchn tcs))).
Proof.
  pose proof (tc_flatten_root_chn_split tcs) as Hperm.
  apply Permutation.Permutation_map with (f:=tc_roottid) in Hperm.
  rewrite -> map_app in Hperm.
  apply Permutation.Permutation_NoDup in Hperm.
  2: assumption.
  now rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hperm.
  (*
  induction tcs as [ | tc tcs IH ].
  1: constructor.
  simpl in Hnodup |- *.
  rewrite -> map_app in Hnodup.
  rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hnodup.
  repeat setoid_rewrite -> base.elem_of_list_In in Hnodup.
  destruct Hnodup as (_ & Hnoits & Hnodup).
  specialize (IH Hnodup).
  destruct tc as [(u, ?, ?) ?].
  simpl in Hnoits |- *.
  constructor.
  - specialize (Hnoits _ (or_introl eq_refl)).
    intros Hin.
    rewrite -> in_map_iff in Hin.
    destruct Hin as (tc & E & Hin).
    pose proof (in_map tc_roottid _ _ (in_flat_map_conv _ _ _ _ Hin (tc_flatten_self_in tc))) as Hin'.
    now rewrite -> E in Hin'.
  - apply IH.
  *)
Qed.

Fact tc_shape_inv_conj_iff tc : 
  tc_shape_inv tc <-> 
    (List.NoDup (map tc_roottid (tc_flatten tc))
    /\ Foralltc tc_chn_aclk_ub tc
    /\ Foralltc tc_chn_aclk_decsorted tc).
Proof.
  split.
  - now intros [? ? ?].
  - intros.
    now constructor.
Qed.

Lemma tc_shape_inv_sub tc (Hshape : tc_shape_inv tc) : Forall tc_shape_inv (tc_flatten tc).
Proof.
  apply tc_shape_inv_conj_iff in Hshape.
  rewrite -> ! Foralltc_Forall_subtree in Hshape.
  change tc_shape_inv with (fun tc' => tc_shape_inv tc').
  setoid_rewrite -> tc_shape_inv_conj_iff.
  repeat apply Forall_and.
  2-3: now rewrite <- Foralltc_Forall_subtree, -> Foralltc_idempotent, -> Foralltc_Forall_subtree.
  now rewrite <- Foralltc_Forall_subtree, <- tid_nodup_Foralltc_id.
Qed.

Corollary tc_shape_inv_chn ni chn (Hshape : tc_shape_inv (Node ni chn)) :
  Forall tc_shape_inv chn.
Proof.
  apply tc_shape_inv_sub in Hshape.
  simpl in Hshape.
  apply Forall_cons_iff, proj2, Forall_flat_map in Hshape.
  rewrite -> List.Forall_forall in Hshape |- *.
  intros [? ?] Hin.
  specialize (Hshape _ Hin).
  simpl in Hshape.
  now apply Forall_cons_iff, proj1 in Hshape.
Qed.

(* prefix also have shape inv *)

Lemma tc_shape_inv_prefix_preserve tc tc' (Hprefix : prefixtc tc tc') 
  (Hshape : tc_shape_inv tc') : tc_shape_inv tc.
Proof.
  revert tc' Hprefix Hshape.
  induction tc as [(u, clk, aclk) chn_sp IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn].
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  injection Htmp as <-.
  subst clk' aclk'.
  pose proof (sublist_In _ _ Hsub) as Hsub_in.
  pose proof (Forall2_forall_exists_l _ _ _ Hcorr) as Hcorr_in.
  pose proof (tc_shape_inv_chn _ _ Hshape) as Hshape_chn.
  rewrite -> List.Forall_forall in IH, Hshape_chn.
  assert (forall x, In x chn_sp -> tc_shape_inv x) as Hshape_sp.
  {
    intros x Hin.
    destruct (Hcorr_in _ Hin) as (y & Hin_sub & Hprefix_sub).
    specialize (Hsub_in _ Hin_sub).
    firstorder.
  }
  pose proof Hcorr as Hrootinfo.
  eapply list.Forall2_impl in Hrootinfo.
  2: apply prefixtc_rootinfo_same.
  pose proof (Forall2_forall_exists_l _ _ _ Hrootinfo) as Hrootinfo_in.
  constructor.
  - apply tid_nodup in Hshape.
    eapply tid_nodup_prefix_preserve; eauto.
    econstructor; eauto.
  - constructor.
    + apply aclk_upperbound, Foralltc_self in Hshape.
      simpl in Hshape |- *.
      rewrite -> List.Forall_forall in Hshape |- *.
      unfold tc_rootaclk in Hshape |- *.
      firstorder congruence.
    + rewrite -> List.Forall_forall.
      firstorder.
  - constructor.
    + apply aclk_decsorted, Foralltc_self in Hshape.
      simpl in Hshape |- *.
      assert (map tc_rootaclk chn_sp = map tc_rootaclk chn_sub) as ->.
      {
        clear -Hrootinfo.
        induction Hrootinfo.
        - auto.
        - simpl. unfold tc_rootaclk in *. congruence.
      }
      eapply sublist_map with (f:=tc_rootaclk) in Hsub.
      eapply sublist_StronglySorted; eauto.
    + rewrite -> List.Forall_forall.
      firstorder.
Qed.

(* exploit some simple cases, which may be not generalizable but simpler ... *)

Lemma tc_shape_inv_prepend_child ni chn (Hshape : tc_shape_inv (Node ni chn))
  tc_new (Hshape_new : tc_shape_inv tc_new)
  (Hnointersect : forall t, tc_getnode t tc_new -> tc_getnode t (Node ni chn) -> False)
  (Haclk_bounded : tc_rootaclk tc_new <= info_clk ni)
  (Haclk_ge : tc_rootaclk tc_new >= match chn with ch :: _ => tc_rootaclk ch | nil => 0 end) :
  tc_shape_inv (Node ni (tc_new :: chn)).
Proof.
  constructor.
  - repeat setoid_rewrite <- tc_getnode_subtc_iff in Hnointersect.
    eapply Permutation.Permutation_NoDup with 
      (l:=map tc_roottid ((tc_flatten tc_new) ++ (tc_flatten (Node ni chn)))).
    + simpl.
      rewrite -> ! map_app.
      simpl.
      symmetry.
      apply Permutation.Permutation_middle.
    + rewrite -> map_app.
      rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
      setoid_rewrite -> base.elem_of_list_In.
      now apply tid_nodup in Hshape, Hshape_new.
  - constructor.
    + apply aclk_upperbound, Foralltc_self in Hshape.
      simpl in Hshape |- *.
      destruct ni as (?, ?, ?).
      simpl in Haclk_bounded.
      constructor; auto.
    + apply aclk_upperbound in Hshape, Hshape_new.
      apply Foralltc_cons_iff in Hshape.
      now constructor.
  - constructor.
    + apply aclk_decsorted, Foralltc_self in Hshape.
      simpl in Hshape |- *.
      constructor.
      1: assumption.
      destruct chn as [ | ch chn ].
      * now simpl.
      * simpl.
        constructor.
        1: assumption.
        simpl in Hshape.
        apply StronglySorted_inv in Hshape.
        rewrite -> List.Forall_forall in Hshape |- *.
        intros x Hin.
        pose proof (proj2 Hshape _ Hin).
        lia.
    + apply aclk_decsorted in Hshape, Hshape_new.
      apply Foralltc_cons_iff in Hshape.
      now constructor.
Qed.

Lemma tc_get_updated_nodes_join_aux_result tc u' chn_u'
  (Haclk_impl_clk : forall tc', In tc' chn_u' -> 
    tc_rootaclk tc' <= (tc_getclk u' tc) -> 
    tc_rootclk tc' <= (tc_getclk (tc_roottid tc') tc)) 
  (Hsorted: StronglySorted ge (map tc_rootaclk chn_u')) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc u' chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => In tc' chn_u'' <-> 
      ((tc_getclk (tc_roottid tc') tc) < tc_rootclk tc' /\
        (tc_getclk u' tc) < tc_rootaclk tc')) chn_u').
Proof.
  induction chn_u' as [ | tc_v' chn_u' IH ].
  - exists nil.
    intuition.
  - simpl in Haclk_impl_clk, Hsorted.
    apply StronglySorted_inv in Hsorted.
    destruct Hsorted as (Hsorted & Hallle).
    destruct tc_v' as [(v', clk_v', aclk_v') chn_v'] eqn:Etc_v'.
    simpl in Hallle.
    rewrite <- Etc_v' in *.
    removehead IH.
    2:{
      intros tc' ?.
      specialize (Haclk_impl_clk tc').
      apply Haclk_impl_clk.
      intuition.
    }
    removehead IH.
    2: assumption.
    destruct IH as (chn_u'' & Hsub & Hres & Halllt).
    setoid_rewrite -> Forall_cons_iff.
    tc_get_updated_nodes_join_unfold.
    setoid_rewrite -> Etc_v' at 2.
    destruct (clk_v' <=? tc_getclk v' tc) eqn:Ecmp_clk_v'.
    + apply Nat.leb_le in Ecmp_clk_v'.
      destruct (aclk_v' <=? tc_getclk u' tc) eqn:Ecmp_aclk_v'.
      * (* chu_u'' is actually nil *)
        apply Nat.leb_le in Ecmp_aclk_v'.
        assert (chn_u'' = nil) as ->.
        {
          (* Oh, a long proof *)
          destruct chn_u'' as [ | tc_v'' chn_u'' ].
          1: auto. 
          apply sublist_cons_In in Hsub.
          rename Hsub into Hin'.
          rewrite -> Forall_map in Hallle.
          rewrite -> List.Forall_forall in Hallle, Halllt.
          specialize (Hallle _ Hin').
          specialize (Haclk_impl_clk _ (or_intror Hin')).
          removehead Haclk_impl_clk.
          2: lia.
          exfalso.
          revert Haclk_impl_clk.
          apply Nat.nle_gt, Halllt; simpl; intuition.
        }
        exists nil.
        rewrite -> Etc_v'.
        simpl.
        intuition (auto using list.sublist_nil_l).
        lia.
      * exists chn_u''.
        split.
        1: now constructor.
        split.
        1: assumption.
        split.
        2: assumption.
        transitivity False.
        2: rewrite -> Etc_v'; simpl; lia.
        split.
        2: intros [].
        intros Hin'.
        pose proof Hin' as Hin'_backup.
        eapply sublist_In in Hin'.
        2: apply Hsub.
        rewrite -> List.Forall_forall in Halllt.
        apply Halllt in Hin'.
        rewrite -> Hin', -> Etc_v' in Hin'_backup.
        simpl in Hin'_backup.
        lia.
    + pose proof Ecmp_clk_v' as Ecmp_clk_v'_lt.
      apply Nat.leb_gt in Ecmp_clk_v'_lt.
      specialize (Haclk_impl_clk _ (or_introl eq_refl)).
      rewrite <- ! Nat.nlt_ge, -> ! Etc_v' in Haclk_impl_clk.
      simpl in Haclk_impl_clk.
      exists (tc_v' :: chn_u'').
      split.
      1: now constructor.
      split; [ | split; [ split | ] ].
      * rewrite -> Etc_v'.
        tc_get_updated_nodes_join_unfold.
        now f_equal.
      * intros _.
        rewrite -> Etc_v'.
        simpl.
        intuition.
      * rewrite -> Etc_v'.
        now constructor.
      * simpl.
        eapply List.Forall_impl.
        2: apply Halllt.
        intros ch HH.
        rewrite <- HH.
        intuition.
        subst ch.
        rewrite -> Etc_v' in HH.
        simpl in HH.
        intuition.
Qed.

(* a weaker result; did not find a good way to combine with the statement above *)

Lemma tc_get_updated_nodes_join_aux_result_submap tc u chn :
  exists chn', list.sublist chn' chn /\
    (tc_get_updated_nodes_join_aux tc u chn) = map (tc_get_updated_nodes_join tc) chn'.
Proof.
  induction chn as [ | ch chn IH ]; intros.
  - now exists nil.
  - tc_get_updated_nodes_join_unfold.
    destruct ch as [(v, clk_v, aclk_v) chn_v] eqn:Ech.
    cbn.
    destruct IH as (chn' & Hsub & ->).
    rewrite <- Ech.
    destruct (clk_v <=? tc_getclk v tc) eqn:E.
    + destruct (aclk_v <=? tc_getclk u tc) eqn:E2.
      * exists nil.
        split; [ apply list.sublist_nil_l | reflexivity ].
      * exists chn'.
        split; [ now constructor | reflexivity ].
    + exists (ch :: chn').
      split; [ now constructor | ].
      simpl.
      now subst ch.
Qed.

Corollary tc_get_updated_nodes_join_is_prefix tc tc' :
  prefixtc (tc_get_updated_nodes_join tc tc') tc'.
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  tc_get_updated_nodes_join_unfold.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_submap tc u' chn')
    as (chn'' & Hsub & ->).
  econstructor.
  1: apply Hsub.
  revert chn' IH Hsub.
  induction chn'' as [ | ch chn'' IH' ]; intros.
  - now simpl.
  - simpl.
    constructor.
    + apply sublist_cons_In in Hsub.
      rewrite -> Forall_forall in IH.
      firstorder.
    + apply sublist_cons_remove in Hsub.
      firstorder.
Qed.

Fact imono_single_aclk_impl_clk tc u' clk_u' aclk_u' chn_u'
  (Himono : imono_single tc (Node (mkInfo u' clk_u' aclk_u') chn_u')) :
  forall tc', In tc' chn_u' -> 
    tc_rootaclk tc' <= (tc_getclk u' tc) -> 
    tc_rootclk tc' <= (tc_getclk (tc_roottid tc') tc).
Proof.
  intros tc_v' Hin' Hle.
  (* use imono *)
  simpl in Himono.
  rewrite -> List.Forall_forall in Himono.
  specialize (Himono _ Hin').
  destruct tc_v' as [(v', clk_v', aclk_v') chn_v'].
  simpl in Hle, Himono |- *.
  now apply Himono, Foralltc_self in Hle.
Qed.

Lemma tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn_u' 
  (Hshape_tc' : tc_shape_inv (Node (mkInfo u' clk_u' aclk_u') chn_u')) 
  (Hrespect : tc_respect (Node (mkInfo u' clk_u' aclk_u') chn_u') tc) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc u' chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => ~ In tc' chn_u'' <-> tc_ge tc tc') chn_u') /\
    (Forall (fun tc' => In tc' chn_u'' <-> (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc') chn_u') /\
    (Forall (fun tc' => (tc_getclk u' tc) < tc_rootaclk tc') chn_u'').
Proof.
  pose proof (tc_get_updated_nodes_join_aux_result tc u' chn_u') as H.
  (* get aclk_impl_clk *)
  pose proof (imono _ _ Hrespect) as Himono.
  apply Foralltc_cons_iff, proj1 in Himono.
  pose proof (imono_single_aclk_impl_clk _ _ _ _ _ Himono) as Haclk_impl_clk.
  pose proof (fun tc' H => contra_not (Haclk_impl_clk tc' H)) as Haclk_impl_clk'.
  repeat setoid_rewrite -> Nat.nle_gt in Haclk_impl_clk'.
  removehead H.
  2: assumption.
  removehead H.
  2: now apply aclk_decsorted, Foralltc_cons_iff in Hshape_tc'.
  destruct H as (chn_u'' & Hsub & Hres & Halllt).
  exists chn_u''.
  split.
  1: assumption.
  split.
  1: assumption.
  (* the subsumption part *)
  rewrite -> List.Forall_forall in Halllt.
  assert (forall x : treeclock, In x chn_u' ->
    ~ In x chn_u'' <-> tc_rootclk x <= tc_getclk (tc_roottid x) tc) as Halllt'.
  {
    intros ch Hin.
    rewrite -> Halllt, <- Nat.nlt_ge; auto.
    pose proof (Haclk_impl_clk' _ Hin).
    intuition.
  }
  rewrite -> ! List.Forall_forall.
  split; [ | split ].
  - intros ch Hin.
    specialize (Halllt' _ Hin).
    rewrite -> Halllt'.
    split; intros H.
    2: apply Foralltc_self in H; now destruct ch as [(?, ?, ?) ?].
    (* use dmono *)
    apply dmono, Foralltc_cons_iff in Hrespect.
    destruct Hrespect as (_ & Hdmono).
    rewrite -> List.Forall_forall in Hdmono.
    specialize (Hdmono _ Hin).
    apply Foralltc_self in Hdmono.
    destruct ch as [(?, ?, ?) ?].
    firstorder.
  - firstorder.
  - intros ch Hin.
    pose proof (sublist_In _ _ Hsub _ Hin).
    firstorder.
Qed.

(* make it over the whole tree; also soundness *)

Corollary tc_get_updated_nodes_join_shape tc' (Hshape: tc_shape_inv tc') : 
  forall tc (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc'),
  Foralltc (fun tc' => tc_getclk (tc_roottid tc') tc < tc_rootclk tc') 
    (tc_get_updated_nodes_join tc tc') /\
  Foralltc (fun tc' => let: Node ni chn := tc' in
    Forall (fun tc' => tc_getclk (info_tid ni) tc < tc_rootaclk tc') chn) 
    (tc_get_updated_nodes_join tc tc').
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  rewrite -> List.Forall_forall in IH.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & -> & _ & Halllt & Halllt').
  rewrite -> List.Forall_forall in Halllt, Halllt'.
  pose proof (sublist_In _ _ Hsub) as Hsub_in.
  pose proof (tc_shape_inv_chn _ _ Hshape) as Hshape_ch.
  pose proof (tc_respect_chn _ _ _ Hrespect) as Hrespect_ch.
  rewrite -> List.Forall_forall in Hshape_ch, Hrespect_ch.
  split.
  - constructor.
    + now simpl.
    + rewrite -> Forall_map, -> List.Forall_forall.
      intros ch Hin.
      apply IH; auto.
      firstorder.
  - constructor.
    + rewrite -> Forall_map, -> List.Forall_forall.
      simpl.
      intros ch Hin.
      specialize (Halllt' _ Hin).
      now destruct ch as [(?, ?, aclk) ?].
    + rewrite -> Forall_map, -> List.Forall_forall.
      intros ch Hin.
      apply IH; auto.
      firstorder.
Qed.

Corollary tc_get_updated_nodes_join_complete tc' (Hshape': tc_shape_inv tc') : 
  forall tc (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc')
  t (Hlt : tc_getclk t tc < tc_getclk t tc'),
    (* this equality can be from the prefix property; no need to repeat *)
    (* base.fmap tc_rootinfo (tc_getnode t (tc_get_updated_nodes_join tc tc')) = 
    base.fmap tc_rootinfo (tc_getnode t tc'). *)
    (tc_getnode t (tc_get_updated_nodes_join tc tc')).
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  unfold tc_getclk in Hlt at 2.
  cbn in Hlt |- *.
  destruct (thread_eqdec u' t) as [ <- | Htneq ] eqn:Etdec.
  1: intuition.
  (* get sub inv *)
  assert (NoDup (map tc_roottid (flat_map tc_flatten chn'))) as Hnodup_chn'
    by (now apply tid_nodup, NoDup_cons_iff in Hshape').
  (* get the result of tc_get_updated_nodes_join_aux *)
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & Hsubmap & Hgetjoinres & Halllt & Halllt').
  rewrite -> Hsubmap.
  rewrite -> List.Forall_forall in Hgetjoinres, Halllt.

  destruct (find (has_same_tid t) (flat_map tc_flatten chn')) as [ res | ] eqn:E.
  2: now destruct (tc_getnode t tc).
  simpl.
  apply find_some in E.
  destruct E as (Hin & Et).
  rewrite -> has_same_tid_true in Et.
  rewrite -> in_flat_map in Hin.
  destruct Hin as (ch & Hin_ch & Hin).

  (* tc_rootclk res --> getclk t ch *)
  pose proof (tid_nodup_find_self (tc_flatten ch)) as Hres_ch.
  removehead Hres_ch.
  2: apply tid_nodup in Hshape'; eapply tid_nodup_chn_ch; eauto.
  rewrite -> List.Forall_forall in Hres_ch.
  specialize (Hres_ch _ Hin).
  assert (tc_rootclk res = tc_getclk t ch) as Eclk_ch.
  1: subst t; unfold tc_getclk, tc_getnode; now rewrite -> Hres_ch.
  rewrite -> Eclk_ch in Hlt.
  pose proof (tc_shape_inv_chn _ _ Hshape') as Hshape_chn.
  pose proof (tc_respect_chn _ _ _ Hrespect) as Hrespect_chn.
  rewrite -> List.Forall_forall in IH, Hshape_chn, Hrespect_chn.
  (* now decide in or not? *)
  destruct (in_dec treeclock_eqdec ch chn_u'') as [ Hin_ch' | Hnotin ].
  + (* use IH *)
    pose proof Hin_ch' as Hlt_ch.
    rewrite -> Halllt in Hlt_ch.
    2: assumption.
    specialize (IH _ Hin_ch (Hshape_chn _ Hin_ch) _ (Hrespect_chn _ Hin_ch) Hlt_ch _ Hlt).
    destruct (tc_getnode t (tc_get_updated_nodes_join tc ch)) as [ res' | ] eqn:E.
    2: discriminate.
    apply find_some in E.
    destruct E as (Hres' & Et'').
    rewrite -> has_same_tid_true in Et''.
    destruct (find (has_same_tid t)
      (flat_map tc_flatten (map (tc_get_updated_nodes_join tc) chn_u''))) as [ res'' | ] eqn:Efind.
    * auto.
    * eapply find_none in Efind.
      2:{
        eapply in_flat_map_conv.
        2: apply Hres'.
        now apply in_map.
      }
      now rewrite -> has_same_tid_false in Efind.
  + (* make contradiction by tc_ge *)
    rewrite -> Hgetjoinres in Hnotin.
    2: assumption.
    eapply Foralltc_Forall_subtree, List.Forall_forall in Hnotin.
    2: apply Hin.
    subst t.
    destruct res as [(?, ?, ?) ?].
    simpl in *.
    lia.
Qed.

(* a node is in the gathered prefix iff it needs update; TODO not sure if should re-prove it with Foralltc
    ... or this is even not needed? *)
(*
Lemma tc_get_updated_nodes_join_result : forall tc' (Hshape_tc': tc_shape_inv tc') 
  tc (Hrespect: tc_respect tc' tc) 
  (* root clk le is NECESSARY for sound and completeness since root is always in the gathered prefix *)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') t,
  tc_getnode t (tc_get_updated_nodes_join tc tc') <-> 
  tc_getclk t tc < tc_getclk t tc'.
Proof.
  intros tc' Hshape_tc'.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  unfold tc_getclk at 2.
  cbn.
  destruct (thread_eqdec u' t) as [ <- | Htneq ] eqn:Etdec.
  1: intuition.
  (* get sub inv *)
  assert (NoDup (map tc_roottid (flat_map tc_flatten chn'))) as Hnodup_chn'
    by (now apply tid_nodup, NoDup_cons_iff in Hshape_tc').
  (* get the result of tc_get_updated_nodes_join_aux *)
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & -> & Hgetjoinres & Halllt & Halllt').
  rewrite -> List.Forall_forall in Hgetjoinres, Halllt.
  (* now check if t is in chn' *)
  (* rewrite -> ! find_first_some_correct. *)
  (* TODO ... should be some way to simplify the proof *)
  split.
  - (* know that t is in some gathered subtree *)
    destruct (find (has_same_tid t)
      (flat_map tc_flatten (map (tc_get_updated_nodes_join tc) chn_u''))) as [ res | ] eqn:E.
    2: unfold isSome; intuition.
    intros _.
    apply find_some in E.
    (* destruct res as [ res | ].
    2: unfold isSome in E; intuition. *)
    destruct E as (E & Et).
    rewrite -> has_same_tid_true in Et.
    subst t.
    (* rewrite -> map_map, in_map_iff in E. *)
    rewrite -> in_flat_map in E.
    setoid_rewrite -> in_map_iff in E.
    destruct E as (? & (ch & <- & Hin) & Hres).
    pose proof Hin as Hin_sublist.
    eapply sublist_In in Hin.
    2: apply Hsub.

    pose proof (in_map tc_rootinfo _ _ Hres) as Hres_ch.
    eapply sublist_In in Hres_ch.
    2: apply prefixtc_flatten_sublist, tc_get_updated_nodes_join_is_prefix.
    eapply map_flat_map_In_conv in Hres_ch.
    2: apply Hin.
    eapply find_tid_unique_result_full in Hres_ch.
    2: apply tc_rootinfo_tid_inj.
    2: auto.
    destruct Hres_ch as (res_ch & Hres_ch & Einfo).
    erewrite -> Hres_ch, -> tc_rootinfo_clk_inj.
    2: apply Einfo.
    replace (tc_rootclk res) with (tc_getclk (tc_roottid res) ch) by (unfold tc_getclk; now rewrite -> Hres_ch).
    eapply List.Forall_forall in IH.  
    apply IH.
    + eapply tc_shape_inv_chn, List.Forall_forall in Hshape_tc'; eauto.
    + eapply tc_respect_chn, List.Forall_forall in Hrespect; eauto.
    + now apply Halllt in Hin_sublist.
    + now rewrite -> Hres.


    apply tc_rootinfo_tid_inj in Einfo.



    pose proof (in_flat_map_conv) as Hres'.

    2: eapply tid_nodup_chn_ch; eauto.

    rewrite -> Hres_ch.

    destruct (find (has_same_tid (tc_roottid res)) (flat_map tc_flatten chn')) as [ res' | ] eqn:E.
    2:{
      rewrite -> in_map_iff in Hres_ch.

      eapply find_none in E.
      2: rewrite -> in_flat_map; rewrite -> in_map_iff in Hres_ch; firstorder.


    apply in_map with (f:=info_tid) in Hres_ch.
    rewrite -> map_map in Hres_ch.
    fold (tc_roottid res) tc_roottid in Hres_ch.
    unfold has_same_tid in Et.
    destruct (thread_eqdec (tc_roottid res) t) as [ <- | ]; try discriminate.
    

    eapply prefix_tc_getnode_impl in Hres_ch.
    2: apply tc_get_updated_nodes_join_is_prefix.
    destruct Hres_ch as (res_ch & Hres_ch).
    pose proof Hres_ch as Einfo.
    eapply prefix_tc_getnode_nodup_sameinfo in Einfo.
    2: apply tc_get_updated_nodes_join_is_prefix.
    2: now eapply tid_nodup_chn_ch with (chn:=chn').
    2: apply Hres.

    (* pose proof Hres_ch as Hin_flat.
    apply tc_getnode_some in Hin_flat.
    destruct Hin_flat as (Hin_flat & Et).
    eapply in_flat_map_conv in Hin_flat.
    2: apply Hin. *)
    (* now show that res must be the result of "find isSome (map (tc_getnode t) chn')" *)
    destruct (find (has_same_tid t) (flat_map tc_flatten chn')) as [ res' | ] eqn:E.
    + apply find_some in E.
      destruct E as (Hin' & Et').
      (* unify res' and res *)
      pose proof Hin' as Hin_flat'.
      apply tc_getnode_some_list in Hin_flat'.
      destruct Hin_flat' as (Hin_flat' & <-).
      rewrite -> in_map_iff in Hin'.
      destruct Hin' as (ch' & Hres' & Hin').
      pose proof Hres_ch as Htmp.
      eapply tc_getnode_complete_nodup_list with (sub:=res') in Htmp.
      2-5: eauto.
      subst res'.
      replace (tc_rootclk res_ch) with (tc_getclk (tc_roottid res_ch) ch) by (unfold tc_getclk; now rewrite -> Hres_ch).
      eapply List.Forall_forall in IH.
      2: apply Hin.
      apply IH.
      * eapply tc_shape_inv_chn, List.Forall_forall in Hshape_tc'; eauto.
      * eapply tc_respect_chn, List.Forall_forall in Hrespect; eauto.
      * now apply Halllt in Hin_sublist.
      * now rewrite -> Hres.
    + (* deriving contradiction *)
      eapply find_none in E.
      2: apply in_map, Hin.
      now destruct (tc_getnode t ch).



  
    pose proof Hres as Hres_ch.
    eapply prefix_tc_getnode_impl in Hres_ch.
    2: apply tc_get_updated_nodes_join_is_prefix.
    destruct Hres_ch as (res_ch & Hres_ch).
    pose proof Hres_ch as Einfo.
    eapply prefix_tc_getnode_nodup_sameinfo in Einfo.
    2: apply tc_get_updated_nodes_join_is_prefix.
    2: now eapply tid_nodup_chn_ch with (chn:=chn').
    2: apply Hres.

    pose proof Hres_ch as Hin_flat.
    apply tc_getnode_some in Hin_flat.
    destruct Hin_flat as (Hin_flat & Et).
    eapply in_flat_map_conv in Hin_flat.
    2: apply Hin.
    (* now show that res must be the result of "find isSome (map (tc_getnode t) chn')" *)
    destruct (find isSome (map (tc_getnode t) chn')) as [ res' | ] eqn:E.
    + apply find_some in E.
      destruct E as (Hin' & E), res' as [ res' | ].
      2: discriminate.
      (* unify res' and res *)
      pose proof Hin' as Hin_flat'.
      apply tc_getnode_some_list in Hin_flat'.
      destruct Hin_flat' as (Hin_flat' & <-).
      rewrite -> in_map_iff in Hin'.
      destruct Hin' as (ch' & Hres' & Hin').
      pose proof Hres_ch as Htmp.
      eapply tc_getnode_complete_nodup_list with (sub:=res') in Htmp.
      2-5: eauto.
      subst res'.
      replace (tc_rootclk res_ch) with (tc_getclk (tc_roottid res_ch) ch) by (unfold tc_getclk; now rewrite -> Hres_ch).
      eapply List.Forall_forall in IH.
      2: apply Hin.
      apply IH.
      * eapply tc_shape_inv_chn, List.Forall_forall in Hshape_tc'; eauto.
      * eapply tc_respect_chn, List.Forall_forall in Hrespect; eauto.
      * now apply Halllt in Hin_sublist.
      * now rewrite -> Hres.
    + (* deriving contradiction *)
      eapply find_none in E.
      2: apply in_map, Hin.
      now destruct (tc_getnode t ch).
  - destruct (find isSome (map (tc_getnode t) chn')) as [ res | ] eqn:E.
    2: lia.
    intros Hlt.

    apply find_some in E.
    destruct res as [ res | ].
    2: intuition.
    destruct E as (Hin & _).

    pose proof Hin as Hin_flat.
    apply tc_getnode_some_list in Hin_flat.
    destruct Hin_flat as (Hin_flat & <-).
    rewrite -> in_map_iff in Hin.
    destruct Hin as (ch & Hres & Hin).

    (* now decide in or not? *)
    destruct (in_dec treeclock_eqdec ch chn_u'') as [ Hin_ch | Hnotin ].
    + (* in the selected tree; use IH *)
      assert (tc_getnode (tc_roottid res) (tc_get_updated_nodes_join tc ch)) as Htmp.
      { 
        rewrite -> List.Forall_forall in IH.
        eapply IH.
        all: auto.
        - eapply tc_shape_inv_chn, List.Forall_forall in Hshape_tc'; eauto.
        - eapply tc_respect_chn, List.Forall_forall in Hrespect; eauto.
        - now apply Halllt in Hin_ch.
        - unfold tc_getclk at 2.
          now rewrite -> Hres.
      }
      destruct (tc_getnode (tc_roottid res) (tc_get_updated_nodes_join tc ch)) as [ res' | ] eqn:E.
      2: discriminate.
      assert (In (Some res') (map (tc_getnode (tc_roottid res)) (map (tc_get_updated_nodes_join tc) chn_u''))) as Hin'.
      {
        rewrite -> map_map, -> in_map_iff.
        eauto.
      }
      destruct (find isSome (map (tc_getnode (tc_roottid res)) (map (tc_get_updated_nodes_join tc) chn_u''))) eqn:Efind.
      * apply find_some in Efind.
        destruct o; intuition.
      * eapply find_none in Efind.
        2: apply Hin'.
        discriminate.
    + (* make contradiction *)
      rewrite -> Hgetjoinres in Hnotin.
      2: assumption.
      apply tc_getnode_some in Hres.
      destruct Hres as (Hres & _).
      eapply Foralltc_Forall_subtree, List.Forall_forall in Hnotin.
      2: apply Hres.
      destruct res as [(?, ?, ?) ?].
      simpl in *.
      lia.
Qed.
*)
(* turn the properties of forest in snd to those on fst *)

Lemma tc_detach_nodes_snd2fst subtree_tc' tc :
  Forall (fun tc' => exists sub, In sub (tc_flatten tc) /\ 
    tc' = fst (tc_detach_nodes subtree_tc' sub))
  (snd (tc_detach_nodes subtree_tc' tc)).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  simpl.
  (* TODO much repetition. make these domain-specific tactic? *)
  destruct (List.split (map (tc_detach_nodes subtree_tc') chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => tc_getnode (tc_roottid tc') subtree_tc') new_chn)
    as (res', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
  simpl.
  rewrite -> List.Forall_app, ! List.Forall_forall.
  split.
  - subst res.
    setoid_rewrite -> in_concat.
    setoid_rewrite -> in_map_iff.
    intros res_ch (? & (ch & <- & Hin_ch) & Hin).
    specialize (IH _ Hin_ch _ Hin).
    destruct IH as (sub & Hin_sub & ->).
    exists sub.
    split; [ right; eapply in_flat_map_conv in Hin_sub; eauto | reflexivity ].
  - subst res' new_chn.
    setoid_rewrite -> filter_In.
    setoid_rewrite -> in_map_iff.
    intros ? ((ch & <- & Hin_ch) & _).
    exists ch.
    split. 
    2: reflexivity.
    right. 
    eapply in_flat_map_conv in Hin_ch; eauto.
    destruct ch as [(?, ?, ?) ?].
    simpl.
    intuition.
Qed.

Lemma tc_detach_nodes_dom_incl subtree_tc' tc :
  Forall (fun tc' => tc_getnode (tc_roottid tc') subtree_tc')
  (snd (tc_detach_nodes subtree_tc' tc)).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  simpl.
  destruct (List.split (map (tc_detach_nodes subtree_tc') chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => tc_getnode (tc_roottid tc') subtree_tc') new_chn)
    as (res', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
  simpl.
  rewrite -> List.Forall_app, ! List.Forall_forall.
  split.
  - subst res.
    setoid_rewrite -> in_concat.
    setoid_rewrite -> in_map_iff.
    intros res_ch (? & (ch & <- & Hin_ch) & Hin).
    eapply IH; eauto.
  - subst res' new_chn.
    setoid_rewrite -> filter_In.
    setoid_rewrite -> in_map_iff.
    intros ? ((ch & <- & Hin_ch) & ?).
    intuition.
Qed.

Lemma tc_detach_nodes_fst_is_prefix subtree_tc' tc :
  prefixtc (fst (tc_detach_nodes subtree_tc' tc)) tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  destruct (List.split (map (tc_detach_nodes subtree_tc') chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => tc_getnode (tc_roottid tc') subtree_tc') new_chn)
    as (res', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
  simpl.
  subst new_chn.
  rewrite -> map_filter_comm in Enew_chn'.
  match type of Enew_chn' with map _ (filter ?ff ?ll) = _ => 
    remember (filter ff ll) as chn_sub;
    remember ff as fb
  end.
  econstructor.
  1: apply filter_sublist with (f:=fb).
  subst new_chn'.
  apply Forall_filter with (f:=fb) in IH.
  rewrite <- Heqchn_sub in IH |- *.
  clear -IH.
  induction chn_sub as [ | ch chn ].
  - reflexivity.
  - simpl.
    rewrite -> List.Forall_cons_iff in IH. 
    constructor; firstorder.
Qed.

Corollary tc_detach_nodes_snd_is_subprefix subtree_tc' tc :
  Forall (fun tc' => exists sub, In sub (tc_flatten tc) /\
    prefixtc tc' sub) (snd (tc_detach_nodes subtree_tc' tc)).
Proof.
  pose proof (tc_detach_nodes_snd2fst subtree_tc' tc) as Hto.
  rewrite -> List.Forall_forall in Hto |- *.
  intros sub' Hin'.
  specialize (Hto sub' Hin').
  destruct Hto as (sub & Hin & ->).
  pose proof (tc_detach_nodes_fst_is_prefix subtree_tc' sub).
  eauto.
Qed.

(* permutation is much more clear than mutual In here *)

Lemma tc_detach_nodes_dom_partition subtree_tc' tc :
  Permutation.Permutation (map tc_rootinfo (tc_flatten tc))
    (map tc_rootinfo (tc_flatten (fst (tc_detach_nodes subtree_tc' tc)) ++ 
      (flat_map tc_flatten (snd (tc_detach_nodes subtree_tc' tc))))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl.
  destruct (List.split (map (tc_detach_nodes subtree_tc') chn))
    as (new_chn, forest) eqn:Esplit, 
    (partition (fun tc' : treeclock => tc_getnode (tc_roottid tc') subtree_tc') new_chn)
    as (forest', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  apply pair_equal_split in Esplit.
  destruct Esplit as (Enew_chn & Eres).
  simpl.
  constructor.
  rewrite -> flat_map_app, -> ! map_app.
  etransitivity.
  2:{
    rewrite -> Permutation.Permutation_app_comm, <- app_assoc, <- map_app, <- flat_map_app.
    apply Permutation.Permutation_app_head, Permutation.Permutation_map, Permutation.Permutation_flat_map.
    match type of Epar with partition ?f ?l = (?a, ?b) => 
      replace a with (fst (partition f l)) by (rewrite -> Epar; now simpl);
      replace b with (snd (partition f l)) by (rewrite -> Epar; now simpl)
    end.
    apply Permutation_partition.
  }
  (* seems a local induction is needed *)
  clear -chn IH Enew_chn Eres.
  revert new_chn forest IH Enew_chn Eres.
  induction chn as [ | ch chn IH2 ]; intros.
  all: simpl in Enew_chn, Eres |- *; subst.
  - reflexivity.
  - apply Forall_cons_iff in IH.
    destruct IH as (HH & IH).
    specialize (IH2 _ _ IH eq_refl eq_refl).
    simpl.
    (* TODO this seems to be quite straightforward, but hard to deal with in Coq! *)
    rewrite -> flat_map_app.
    rewrite -> ! map_app.
    match goal with |- Permutation.Permutation _ ((?a ++ ?b) ++ (?c ++ ?d)) => 
      transitivity ((c ++ a) ++ (b ++ d)) end.
    2:{
      match goal with |- Permutation.Permutation _ ((?a ++ ?b) ++ (?c ++ ?d)) => 
        remember a as la; remember b as lb; remember c as lc; remember d as ld end.
      rewrite -> ! app_assoc with (n:=ld).
      apply Permutation.Permutation_app_tail.
      rewrite <- 2 app_assoc.
      apply Permutation.Permutation_app_rot.
    }
    apply Permutation.Permutation_app.
    + now rewrite <- map_app.
    + assumption.
Qed.

Corollary tc_detach_nodes_tid_nodup subtree_tc' tc 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  NoDup (map tc_roottid (flat_map tc_flatten (snd (tc_detach_nodes subtree_tc' tc)))) /\
  NoDup (map tc_roottid (tc_flatten (fst (tc_detach_nodes subtree_tc' tc)))).
Proof.
  pose proof (tc_detach_nodes_dom_partition subtree_tc' tc) as Hperm.
  eapply Permutation.Permutation_map with (f:=info_tid) in Hperm.
  rewrite -> ! map_map in Hperm.
  fold tc_roottid in Hperm.
  pose proof (Permutation.Permutation_NoDup Hperm Hnodup) as Htmp.
  now rewrite -> map_app, <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Htmp.
Qed.

(* there will not be any tid in subtree_tc' that is also inside the pivot tree *)

Lemma tc_detach_nodes_dom_excl subtree_tc' tc :
  forall t (Htarg : tc_getnode t subtree_tc')
  (* res (Hres : tc_getnode t (fst (tc_detach_nodes subtree_tc' tc)) = Some res), *)
  res (Hin : In res (tc_flatten (fst (tc_detach_nodes subtree_tc' tc)))) (Et : tc_roottid res = t),
  res = (fst (tc_detach_nodes subtree_tc' tc)).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  rewrite -> List.Forall_forall in IH.
  simpl in Hin |- *.
  destruct (List.split (map (tc_detach_nodes subtree_tc') chn))
    as (new_chn, forest) eqn:Esplit, 
    (partition (fun tc' : treeclock => tc_getnode (tc_roottid tc') subtree_tc') new_chn)
    as (forest', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
  simpl in Hin |- *.
  destruct Hin as [ | Hin ].
  1: congruence.
  (* now contradiction part *)
  apply in_flat_map in Hin.
  destruct Hin as (new_ch & Hin_ch & Hin).
  subst new_chn' new_chn.
  apply filter_In in Hin_ch.
  destruct Hin_ch as (Hin_ch & Htidnotin).
  apply in_map_iff in Hin_ch.
  destruct Hin_ch as (ch & <- & Hin_ch).
  subst t.
  eapply IH in Hin; eauto.
  subst res.
  now destruct (tc_getnode (tc_roottid (fst (tc_detach_nodes subtree_tc' ch)))
    subtree_tc').
Qed.

Corollary tc_shape_inv_tc_detach_nodes_fst subtree_tc' tc 
  (Hshape : tc_shape_inv tc) :
  tc_shape_inv (fst (tc_detach_nodes subtree_tc' tc)).
Proof.
  pose proof (tc_detach_nodes_fst_is_prefix subtree_tc' tc) as Hprefix.
  eapply tc_shape_inv_prefix_preserve; eauto.
Qed.

Corollary tc_shape_inv_tc_detach_nodes_snd subtree_tc' tc 
  (Hshape : tc_shape_inv tc) :
  Forall tc_shape_inv (snd (tc_detach_nodes subtree_tc' tc)).
Proof.
  pose proof (tc_detach_nodes_snd2fst subtree_tc' tc) as Hto.
  pose proof (tc_shape_inv_sub _ Hshape) as Hshape_sub.
  rewrite -> List.Forall_forall in Hto, Hshape_sub |- *.
  intros sub' Hin'.
  specialize (Hto sub' Hin').
  destruct Hto as (sub & Hin & ->).
  specialize (Hshape_sub _ Hin).
  now apply tc_shape_inv_tc_detach_nodes_fst.
Qed.

Lemma tc_detach_nodes_forest_recombine_pre subtree_tc' tc 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  (Hnodup' : NoDup (map tc_roottid (tc_flatten subtree_tc'))) :
  Permutation.Permutation
    (map Some (snd (tc_detach_nodes subtree_tc' tc)))
    (filter isSome (map
      (fun t => find (has_same_tid t) (snd (tc_detach_nodes subtree_tc' tc))) 
        (map tc_roottid (tc_flatten subtree_tc')))).
Proof.
  pose proof (tc_detach_nodes_tid_nodup subtree_tc' tc Hnodup) as Hnodup_forest.
  apply proj1, tid_nodup_root_chn_split, proj1 in Hnodup_forest.
  apply Permutation.NoDup_Permutation.
  - apply FinFun.Injective_map_NoDup.
    1: congruence.
    now apply NoDup_map_inv with (f:=tc_roottid).
  - (* no much good way ... induction? *)
    remember (map tc_roottid (tc_flatten subtree_tc')) as l.
    remember (snd (tc_detach_nodes subtree_tc' tc)) as tcs.
    clear -Hnodup' Hnodup_forest thread_eqdec.
    revert tcs Hnodup_forest.
    induction l as [ | t l IH ]; intros.
    1: constructor.
    apply NoDup_cons_iff in Hnodup'.
    destruct Hnodup' as (Hnotin & Hnodup').
    simpl.
    destruct (find (has_same_tid t) tcs) as [ res | ] eqn:E; simpl.
    + constructor.
      2: now apply IH.
      intros HH.
      apply filter_In, proj1, in_map_iff in HH.
      destruct HH as (u & E' & Hin').
      apply find_some, proj2, has_same_tid_true in E, E'.
      congruence.
    + now apply IH.
  - intros ot.
    split; intros Hin.
    + rewrite -> in_map_iff in Hin.
      destruct Hin as (sub & <- & Hin).
      apply filter_In.
      split; [ | auto ].
      apply in_map_iff.
      (* use dom incl *)
      pose proof (tc_detach_nodes_dom_incl subtree_tc' tc) as Hdomincl.
      pose proof (tid_nodup_find_self _ Hnodup_forest) as Hself.
      rewrite -> List.Forall_forall in Hdomincl, Hself.
      specialize (Hdomincl _ Hin).
      specialize (Hself _ Hin).
      rewrite <- tc_getnode_subtc_iff in Hdomincl.
      eauto.
    + apply filter_In in Hin.
      destruct ot as [ res | ]; [ | intuition discriminate ].
      apply proj1, in_map_iff in Hin.
      destruct Hin as (t & Hin & _).
      apply find_some in Hin.
      now apply in_map.
Qed.

(* simulation *)

Corollary tc_detach_nodes_forest_recombine subtree_tc' tc 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  (Hnodup' : NoDup (map tc_roottid (tc_flatten subtree_tc'))) :
  Permutation.Permutation
    (flat_map tc_rootchn (snd (tc_detach_nodes subtree_tc' tc)))
    (flat_map
      (fun t : thread =>
      match find (has_same_tid t) (snd (tc_detach_nodes subtree_tc' tc)) with
      | Some res => tc_rootchn res
      | None => nil
      end) (map tc_roottid (tc_flatten subtree_tc'))).
Proof.
  pose (f:=fun ot => match ot with Some tc => tc_rootchn tc | None => nil end).
  pose proof (tc_detach_nodes_forest_recombine_pre _ _ Hnodup Hnodup') as Hperm.
  apply Permutation.Permutation_flat_map with (g:=f) in Hperm.
  match type of Hperm with Permutation.Permutation ?a _ => transitivity a end.
  1:{
    remember (snd (tc_detach_nodes subtree_tc' tc)) as l.
    clear -thread_eqdec l.
    induction l as [ | x l IH ].
    1: reflexivity.
    simpl.
    now apply Permutation.Permutation_app_head.
  }
  match type of Hperm with Permutation.Permutation _ ?a => transitivity a end.
  2:{
    remember (map tc_roottid (tc_flatten subtree_tc')) as l.
    clear -thread_eqdec l.
    induction l as [ | x l IH ].
    1: reflexivity.
    simpl.
    destruct (find (has_same_tid x) (snd (tc_detach_nodes subtree_tc' tc))) eqn:E; simpl.
    - now apply Permutation.Permutation_app_head.
    - assumption.
  }
  assumption.
Qed.

(* a very special case for the overlay tree *)

Inductive simple_overlaytc (P : thread -> list treeclock) : treeclock -> treeclock -> Prop :=
  simple_overlaytc_intro : forall ni chn chn' chn'',
    chn'' = P (info_tid ni) ->
    Forall2 (simple_overlaytc P) chn chn' ->
    simple_overlaytc P (Node ni chn) (Node ni (chn' ++ chn'')).

Fact simple_overlaytc_inv (P : thread -> list treeclock) ni1 ni2 chn1 chn2 
  (Hso: simple_overlaytc P (Node ni1 chn1) (Node ni2 chn2)) :
  exists prefix_chn suffix_chn, ni1 = ni2 /\ chn2 = prefix_chn ++ suffix_chn /\
    suffix_chn = P (info_tid ni1) /\ Forall2 (simple_overlaytc P) chn1 prefix_chn /\
    map tc_rootinfo chn1 = map tc_rootinfo prefix_chn.
Proof. 
  inversion Hso; subst. 
  eexists. eexists. 
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ | split ]; auto.
  match goal with HH : Forall2 (simple_overlaytc P) _ _ |- _ => 
    clear -HH; induction HH as [ | [? ?] [? ?] chn1 chn2 H H' IH ] end.
  - auto.
  - inversion H.
    simpl.
    congruence.
Qed.

Lemma tc_attach_nodes_result forest tc :
  simple_overlaytc (fun t =>
    (* match List.find (fun tc => thread_eqdec (tc_roottid tc) t) forest with *)
    match List.find (has_same_tid t) forest with
    | Some res => tc_rootchn res
    | None => nil
    end) tc (tc_attach_nodes forest tc).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl.
  constructor.
  - auto.
  - clear -IH.
    induction chn as [ | ch chn ].
    1: constructor.
    apply List.Forall_cons_iff in IH.
    destruct IH as (H & IH).
    constructor; firstorder.
Qed.

Lemma simple_overlaytc_dom_info (P : thread -> list treeclock) tc : forall tc'
  (Hoverlay : simple_overlaytc P tc tc'),
  Permutation.Permutation (map tc_rootinfo (tc_flatten tc'))
  ((map tc_rootinfo (tc_flatten tc)) ++
    (map tc_rootinfo (flat_map tc_flatten (flat_map P (map tc_roottid (tc_flatten tc)))))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  simpl.
  constructor.
  rewrite -> ! flat_map_app, -> ! map_app.
  etransitivity.
  1: apply Permutation.Permutation_app_comm.
  etransitivity.
  2: apply Permutation.Permutation_app_comm.
  rewrite <- app_assoc.
  apply Permutation.Permutation_app_head.
  clear u clk aclk.
  induction Hcorr as [ | ch new_ch chn new_chn Hso Hcorr IH' ].
  - now simpl.
  - simpl in Hinfosame |- *.
    apply Forall_cons_iff in IH.
    destruct IH as (HH & IH).
    specialize (IH' IH).
    removehead IH'.
    2: congruence.
    repeat rewrite -> ? map_app, -> ? flat_map_app.
    match goal with |- Permutation.Permutation _ ((?a ++ ?b) ++ (?c ++ ?d)) => 
      remember a as la; remember b as lb; remember c as lc; remember d as ld;
      transitivity ((lc ++ la) ++ (lb ++ ld)) end.
    2:{
      rewrite -> ! app_assoc with (n:=ld).
      apply Permutation.Permutation_app_tail.
      rewrite <- 2 app_assoc.
      apply Permutation.Permutation_app_rot.
    }
    apply HH in Hso.
    now apply Permutation.Permutation_app.
Qed.
(*
Lemma simple_overlaytc_dom_info (P : thread -> list treeclock) tc : forall tc'
  (Hoverlay : simple_overlaytc P tc tc') ni,
  In ni (map tc_rootinfo (tc_flatten tc')) <->
  In ni (map tc_rootinfo (tc_flatten tc)) \/ 
    (exists t, tc_getnode t tc /\ In ni (map tc_rootinfo (flat_map tc_flatten (P t)))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  simpl.
  rewrite -> flat_map_app, -> map_app, -> in_app_iff, -> or_assoc.
  apply or_iff_compat_l.
  rewrite -> List.Forall_forall in IH.
  pose proof (Forall2_forall_exists_l _ _ _ Hcorr) as Hcorr_inl.
  pose proof (Forall2_forall_exists_r _ _ _ Hcorr) as Hcorr_inr.
  repeat setoid_rewrite -> map_flat_map_In.
  setoid_rewrite -> map_flat_map_In in IH.
  (* TODO temporarily cannot find a good way to do this. simply discuss first *)
  split.
  - intros [ (new_ch & Hin_newch & Hin) | (sub & Hin_sub & Hin) ].
    + specialize (Hcorr_inr _ Hin_newch).
      destruct Hcorr_inr as (ch & Hin_ch & Hso).
      specialize (IH _ Hin_ch _ Hso ni).
      rewrite -> IH in Hin.
      destruct Hin as [ | (t & Hres & (sub & Hin_sub & Hin)) ].
      1: left; eauto.
      right.
      exists t.
      split.
      2: eauto.
      destruct (thread_eqdec t u); auto.
      eapply find_first_some_correct', some_In_findsome_iff, tc_getnode_ch_in_chn; eauto.
    + right.
      exists u.
      destruct (thread_eqdec u u); intuition eauto.
  - intros [ (ch & Hin_ch & Hin) | (t & E & (sub & Hin_sub & Hin)) ].
    + specialize (Hcorr_inl _ Hin_ch).
      destruct Hcorr_inl as (new_ch & Hin_newch & Hso).
      specialize (IH _ Hin_ch _ Hso ni).
      apply (fun a => proj2 IH (or_introl a)) in Hin.
      eauto.
    + destruct (thread_eqdec t u) as [ <- | Hneq ].
      * eauto.
      * rewrite -> find_first_some_correct', some_In_findsome_iff in E.
        destruct E as (res & Hres).
        apply tc_getnode_some_list in Hres.
        rewrite -> in_flat_map in Hres.
        destruct Hres as ((ch & Hin_ch & Hres) & <-).
        pose proof (tc_getnode_complete _ _ _ Hres eq_refl) as (res' & E).
        specialize (Hcorr_inl _ Hin_ch).
        destruct Hcorr_inl as (new_ch & Hin_newch & Hso).
        left.
        exists new_ch. 
        split; auto.
        specialize (IH _ Hin_ch _ Hso ni).
        apply (fun a => proj2 IH (or_intror a)).
        exists (tc_roottid res).
        rewrite -> E.
        firstorder.
Qed.

Corollary simple_overlaytc_dom_tid (P : thread -> list treeclock) tc tc'
  (Hoverlay : simple_overlaytc P tc tc') t :
  In t (map tc_roottid (tc_flatten tc')) <->
  In t (map tc_roottid (tc_flatten tc)) \/ 
    (exists t', tc_getnode t' tc /\ In t (map tc_roottid (flat_map tc_flatten (P t')))).
Proof.
  setoid_rewrite -> map_flat_map_In.
  unfold tc_roottid.
  setoid_rewrite <- map_map.
  setoid_rewrite -> in_map_iff.
  pose proof (simple_overlaytc_dom_info _ _ _ Hoverlay).
  setoid_rewrite -> H.
  setoid_rewrite -> map_flat_map_In.
  firstorder.
Qed.
*)

(* not sure if this still works or not *)
(*
Section Perfect_Partition.

  (* a primitive attempt for perfect partitioning *)

  Lemma tc_getnode_list_nodup_perm (l : list treeclock)
    (Hnodup : List.NoDup (map tc_roottid (flat_map tc_flatten l))) 
    l' (Hperm : Permutation.Permutation l l') t :
    find_first_some (map (tc_getnode t) l) = find_first_some (map (tc_getnode t) l').
  Proof.
    rewrite -> ! find_first_some_correct.
    assert (forall res, In res (map (tc_getnode t) l) <-> In res (map (tc_getnode t) l')) as H.
    {
      intros res.
      apply Permutation.Permutation_in'.
      1: reflexivity.
      now apply Permutation.Permutation_map.
    }
    destruct (find isSome (map (tc_getnode t) l)) as [ res | ] eqn:E, 
      (find isSome (map (tc_getnode t) l')) as [ res' | ] eqn:E'.
    - apply find_some in E, E'.
      destruct E as (Hin & E), E' as (Hin' & E'), res as [ res | ], res' as [ res' | ].
      all: try discriminate.
      f_equal.
      rewrite <- H in Hin'.
      pose proof (tc_getnode_some_list _ _ _ Hin) as (Hin_flat & <-).
      pose proof (tc_getnode_some_list _ _ _ Hin') as (Hin_flat' & Et).
      symmetry.
      eapply NoDup_map_inj; eauto.
    - apply find_some in E.
      destruct E as (Hin & E).
      eapply find_none in E'.
      2: rewrite <- H; apply Hin.
      intuition.
    - (* TODO bad symmetry *)
      apply find_some in E'.
      destruct E' as (Hin & E').
      eapply find_none in E.
      2: rewrite -> H; apply Hin.
      intuition.
    - reflexivity.
  Qed.

  (* can only talk about rootinfo *)

  Fact fmap_rootinfo_someiff (x y : option treeclock) (H : base.fmap tc_rootinfo x = base.fmap tc_rootinfo y) :
    x <-> y.
  Proof. now destruct x, y. Qed.

  Fact tc_getnode_prepend_child_partition ni ch chn 
    (Hnodup : List.NoDup (map tc_roottid (tc_flatten (Node ni (ch :: chn))))) t : 
    base.fmap tc_rootinfo (tc_getnode t (Node ni (ch :: chn))) =
    base.fmap tc_rootinfo (find_first_some ((tc_getnode t (Node ni chn)) :: (tc_getnode t ch) :: nil)).
  Proof.
    cbn.
    destruct (thread_eqdec t (info_tid ni)) as [ -> | Hneq ].
    - reflexivity.
    - destruct (tc_getnode t ch) as [ res | ] eqn:E, 
        (find_first_some (map (tc_getnode t) chn)) as [ res' | ] eqn:E'.
      all: auto.
      simpl.
      f_equal.
      (* TODO should we extract this out? and also, why this seems very weird ... *)
      simpl in Hnodup.
      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as (_ & Hnodup).
      unfold tc_roottid in Hnodup.
      rewrite <- map_map in Hnodup.

      rewrite -> find_first_some_correct in E'.
      destruct (find isSome (map (tc_getnode t) chn)) as [ res'' | ] eqn:E2; [ | discriminate ].
      destruct res'' as [ ? | ]; [ injection E' as -> | discriminate ].
      apply find_some in E2.
      destruct E2 as (E' & _).
      apply tc_getnode_some_list in E'.
      destruct E' as (Hin' & <-).

      apply tc_getnode_some in E.
      destruct E as (Hin & Et).
      apply in_map with (f:=tc_rootinfo) in Hin, Hin'.

      eapply NoDup_map_inj.
      1: apply Hnodup.
      1: now unfold tc_roottid in Et.
      all: rewrite -> map_app, in_app_iff; intuition.
  Qed.

  Corollary tc_getnode_prepend_child_partition' ni ch chn 
    (Hnodup : List.NoDup (map tc_roottid (tc_flatten (Node ni (ch :: chn))))) t : 
    base.fmap tc_rootinfo (tc_getnode t (Node ni (ch :: chn))) =
    base.fmap tc_rootinfo (find_first_some ((tc_getnode t ch) :: (tc_getnode t (Node ni chn)) :: nil)).
  Proof.
    rewrite -> tc_getnode_prepend_child_partition; auto.
    f_equal.
    change (tc_getnode t ?a :: tc_getnode t ?b :: nil) with (map (tc_getnode t) (a :: b :: nil)).
    apply tc_getnode_list_nodup_perm.
    - simpl in Hnodup |- *.
      rewrite -> app_nil_r.
      eapply Permutation.Permutation_NoDup.
      2: apply Hnodup.
      constructor.
      apply Permutation.Permutation_map, Permutation.Permutation_app_comm.
    - apply Permutation.perm_swap.
  Qed.

End Perfect_Partition.
*)
(* this is actually much more complicated than I thought ... *)

Lemma simple_overlaytc_nodup (P : thread -> list treeclock) 
  (Hnodup_small : forall t, List.NoDup (map tc_roottid (flat_map tc_flatten (P t))))
  (* (Hnoits_forest : forall t t', t <> t' -> forall t'', 
    find (has_same_tid t'') (flat_map tc_flatten (P t)) -> 
    find (has_same_tid t'') (flat_map tc_flatten (P t')) -> False) *)
  tc tc'
  (Hoverlay : simple_overlaytc P tc tc')
  (Hnodup_forest : NoDup (map tc_roottid (flat_map tc_flatten (flat_map P (map tc_roottid (tc_flatten tc))))))
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc)))
  (* a neat choice to write None or neg here ... *)
  (Hdomexcl : forall t, tc_getnode t tc -> 
    forall t', ~ find (has_same_tid t) (flat_map tc_flatten (P t'))) :
  List.NoDup (map tc_roottid (tc_flatten tc')).
Proof.
  eapply Permutation.Permutation_NoDup.
  1:{
    symmetry.
    unfold tc_roottid.
    rewrite <- map_map.
    apply Permutation.Permutation_map.
    eapply simple_overlaytc_dom_info.
    apply Hoverlay.
  }
  rewrite -> map_app.
  rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
  split; [ | split ].
  - now rewrite -> map_map.
  - repeat setoid_rewrite -> base.elem_of_list_In.
    rewrite -> ! map_map.
    fold tc_roottid.
    setoid_rewrite -> map_flat_map_In.
    setoid_rewrite -> in_flat_map.
    intros t Hin (ch & (u & Hin' & Hin_ch) & Hin_sub').
    rewrite -> tc_getnode_subtc_iff in Hin.
    pose proof (map_flat_map_In_conv _ _ _ _ _ Hin_ch Hin_sub').
    rewrite -> tc_getnode_in_iff in H.
    apply (Hdomexcl _ Hin _ H).
  - now rewrite -> map_map.
Qed.
(*
Lemma simple_overlaytc_nodup (P : thread -> list treeclock) 
  (Hnodup_forest : forall t, List.NoDup (map tc_roottid (flat_map tc_flatten (P t))))
  (Hnoits_forest : forall t t', t <> t' -> forall t'', 
    find_first_some (map (tc_getnode t'') (P t)) -> 
    find_first_some (map (tc_getnode t'') (P t')) -> False)
  tc : forall tc'
  (Hoverlay : simple_overlaytc P tc tc')
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc)))
  (* a neat choice to write None or neg here ... *)
  (Hdomexcl : forall t, tc_getnode t tc -> forall t', ~ find_first_some (map (tc_getnode t) (P t'))),
  List.NoDup (map tc_roottid (tc_flatten tc')).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & _).
  injection Htmp as <-.
  subst clk' aclk'.
  rewrite -> List.Forall_forall in IH.
  pose proof (Forall2_forall_exists_l _ _ _ Hcorr) as Hcorr_inl.
  pose proof (Forall2_forall_exists_r _ _ _ Hcorr) as Hcorr_inr.
  simpl in Hnodup |- *.
  rewrite -> NoDup_cons_iff in Hnodup |- *.
  destruct Hnodup as (Hnotin & Hnodup).
  split.
  - rewrite -> flat_map_app, -> map_app, -> in_app_iff, -> ! map_flat_map_In.
    intros [ (new_ch & Hin_newch & Hin) | (sub & Hin_sub & Hin) ].
    + specialize (Hcorr_inr _ Hin_newch).
      destruct Hcorr_inr as (ch & Hin_ch & Hso).
      eapply simple_overlaytc_dom_tid with (t:=u) in Hso.
      rewrite -> Hso in Hin.
      destruct Hin as [ Hin | (t & _ & Hin) ].
      * rewrite -> map_flat_map_In in Hnotin.
        firstorder.
      * (* TODO some repetition here (from above + below) *)
        rewrite -> map_flat_map_In in Hin.
        setoid_rewrite -> tc_getnode_subtc_iff in Hin.
        destruct Hin as (sub & Hin_sub & Hin).
        (* use domain exclusion *)
        eapply Hdomexcl.
        2:{
          rewrite -> find_first_some_correct', -> some_In_findsome_iff.
          eapply tc_getnode_ch_in_chn; eauto.
        }
        simpl.
        now destruct (thread_eqdec u u).
    + (* use domain exclusion *)
      eapply Hdomexcl.
      2:{
        rewrite -> find_first_some_correct', -> some_In_findsome_iff.
        rewrite -> tc_getnode_subtc_iff in Hin.
        eapply tc_getnode_ch_in_chn; eauto.
      }
      simpl.
      now destruct (thread_eqdec u u).
  - rewrite -> flat_map_app, -> map_app.
    rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
    split; [ | split ].
    + (* for this case, maybe a local induction will be helpful ... *)
      clear Hcorr_inl Hcorr_inr.
      revert Hdomexcl.
      induction Hcorr as [ | ch new_ch chn new_chn Hso Hcorr IH' ]; intros.
      1: auto.
      (* simplify *)
      pose proof Hnodup as Hnodup_backup.
      simpl in IH, Hnotin, Hnodup |- *.
      rewrite -> map_app in Hnotin, Hnodup |- *. 
      rewrite -> in_app_iff in Hnotin.
      apply Decidable.not_or in Hnotin.
      rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hnodup |- *.
      repeat setoid_rewrite -> base.elem_of_list_In in Hnodup.
      repeat setoid_rewrite -> base.elem_of_list_In.
      destruct Hnotin as (Hnotin_ch & Hnotin_chn), Hnodup as (Hnodup_ch & Hnoits_ch_chn & Hnodup_chn).
      removehead IH'.
      2: firstorder.
      do 2 (removehead IH'; [ | intuition ]).
      removehead IH'.
      2:{
        (* TODO still, some repetition here *)
        intros t Hres.
        eapply Hdomexcl, fmap_rootinfo_someiff.
        - apply tc_getnode_prepend_child_partition.
          simpl in Hnodup_backup |- *.
          apply NoDup_cons_iff.
          split; [ | assumption ].
          rewrite -> map_app, -> in_app_iff.
          now intros [ ? | ? ].
        - simpl in Hres |- *.
          match type of Hres with (is_true (isSome ?t)) => now destruct t end.
      }
      split; [ | split ]; auto.
      * eapply IH; eauto.
      (* TODO still, some repetition here *)
        intros t Hres.
        eapply Hdomexcl, fmap_rootinfo_someiff.
        --apply tc_getnode_prepend_child_partition'.
          simpl in Hnodup_backup |- *.
          apply NoDup_cons_iff.
          split; [ | assumption ].
          rewrite -> map_app, -> in_app_iff.
          now intros [ ? | ? ].
        --simpl in Hres |- *.
          match type of Hres with (is_true (isSome ?t)) => now destruct t end.
      * intros t Hin Hin'.
        rewrite -> map_flat_map_In in Hin'.
        destruct Hin' as (new_ch' & Hin_newch' & Hin').
        (* relate to old tree; would yield 2*2 discussion *)
        pose proof (Forall2_forall_exists_r _ _ _ Hcorr _ Hin_newch') as (ch' & Hin_ch' & Hso').
        eapply simple_overlaytc_dom_tid with (t:=t) in Hso, Hso'.
        rewrite -> Hso in Hin.
        rewrite -> Hso' in Hin'.
        setoid_rewrite -> map_flat_map_In in Hin.
        setoid_rewrite -> map_flat_map_In in Hin'.
        destruct Hin as [ Hin | (t' & Hres' & (sub & Hin_sub & Hin)) ], 
          Hin' as [ Hin' | (t'' & Hres'' & (sub' & Hin_sub' & Hin')) ].
        --eapply Hnoits_ch_chn.
          1: apply Hin.
          eapply map_flat_map_In; eauto.
        --(* TODO some repetition here (from above) *)
          assert (t <> u) as Hneq by intuition.
          rewrite -> tc_getnode_subtc_iff in Hin, Hin'.
          (* use domain exclusion *)
          eapply Hdomexcl.
          2:{
            rewrite -> find_first_some_correct', -> some_In_findsome_iff.
            (* TODO maybe it is not very proper to use eauto here ... *)
            eapply tc_getnode_ch_in_chn; eauto.
          }
          simpl.
          destruct (thread_eqdec t u); try congruence.
          now destruct (tc_getnode t ch).
        --(* TODO some repetition here (from above) *)
          assert (t <> u) as Hneq.
          {
            intros ->.
            rewrite -> map_flat_map_In in Hnotin_chn.
            apply Hnotin_chn.
            eauto.
          }
          rewrite -> tc_getnode_subtc_iff in Hin, Hin'.
          (* use domain exclusion *)
          eapply Hdomexcl.
          2:{
            rewrite -> find_first_some_correct', -> some_In_findsome_iff.
            eapply tc_getnode_ch_in_chn.
            2: apply Hin_sub.
            apply Hin.
          }
          simpl.
          destruct (thread_eqdec t u); try congruence.
          destruct (tc_getnode t ch); auto.
          rewrite -> find_first_some_correct', -> some_In_findsome_iff.
          eapply tc_getnode_ch_in_chn; eauto.
        --rewrite <- tc_getnode_subtc_iff in Hres', Hres''.
          assert (t' <> t'') as Hneq.
          {
            intros <-.
            eapply Hnoits_ch_chn.
            1: apply Hres'.
            eapply map_flat_map_In; eauto.
          }
          rewrite -> tc_getnode_subtc_iff in Hin, Hin'.
          apply Hnoits_forest with (t:=t') (t':=t'') (t'':=t); auto.
          ++rewrite -> find_first_some_correct', -> some_In_findsome_iff.
            apply tc_getnode_ch_in_chn with (ch:=sub).
            all: auto.
          ++rewrite -> find_first_some_correct', -> some_In_findsome_iff.
            apply tc_getnode_ch_in_chn with (ch:=sub').
            all: auto.
    + setoid_rewrite -> base.elem_of_list_In.
      setoid_rewrite -> map_flat_map_In.
      intros t (new_ch & Hin_newch & Hin) (sub & Hin_sub & Hin').
      (* TODO repetition *)
      pose proof (Forall2_forall_exists_r _ _ _ Hcorr _ Hin_newch) as (ch & Hin_ch & Hso).
      eapply simple_overlaytc_dom_tid with (t:=t) in Hso.
      rewrite -> Hso in Hin.
      setoid_rewrite -> map_flat_map_In in Hin.
      destruct Hin as [ Hin | (t' & Hres' & (sub'' & Hin_sub'' & Hin)) ].
      * assert (t <> u) as Hneq.
        {
          intros ->.
          rewrite -> map_flat_map_In in Hnotin.
          apply Hnotin.
          eauto.
        }
        rewrite -> tc_getnode_subtc_iff in Hin, Hin'.
        (* use domain exclusion *)
        eapply Hdomexcl.
        2:{
          rewrite -> find_first_some_correct', -> some_In_findsome_iff.
          eapply tc_getnode_ch_in_chn.
          - apply Hin'.
          - apply Hin_sub.
        }
        simpl.
        destruct (thread_eqdec t u); try congruence.
        rewrite -> find_first_some_correct', -> some_In_findsome_iff.
        eapply tc_getnode_ch_in_chn; eauto.
      * rewrite <- tc_getnode_subtc_iff in Hres'.
        assert (t' <> u) as Hneq.
        {
          intros ->.
          eapply Hnotin.
          eapply map_flat_map_In.
          eauto.
        }
        rewrite -> tc_getnode_subtc_iff in Hin, Hin'.
        apply Hnoits_forest with (t:=t') (t':=u) (t'':=t); auto.
        ++rewrite -> find_first_some_correct', -> some_In_findsome_iff.
          apply tc_getnode_ch_in_chn with (ch:=sub'').
          all: auto.
        ++rewrite -> find_first_some_correct', -> some_In_findsome_iff.
          apply tc_getnode_ch_in_chn with (ch:=sub).
          all: auto.
    + firstorder.
Qed.
*)
Lemma tc_shape_inv_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat)
  (Hcomple : forall t, exists aclk, tc_shape_inv (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hshape : tc_shape_inv tc)
  (* needed for aclk upperbound *)
  (Hclk_lt : Foralltc (fun tc' => Q (tc_roottid tc') < tc_rootclk tc') tc)
  (* needed for aclk sorted *)
  (Haclk_lt : Foralltc (fun tc' => let: Node ni chn := tc' in
    Forall (fun tc' => Q (info_tid ni) < tc_rootaclk tc') chn) tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  Foralltc tc_chn_aclk_ub tc' /\ Foralltc tc_chn_aclk_decsorted tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  rewrite -> List.Forall_forall in IH.
  pose proof (Forall2_forall_exists_r _ _ _ Hcorr) as Hcorr_inr.
  (* prepare *)
  pose proof (Hcomple u) as (aclk' & Hshape_sub).
  pose proof (tc_shape_inv_chn _ _ Hshape) as Hshape_chn.
  rewrite -> tc_shape_inv_conj_iff, -> ! Foralltc_cons_iff in Hshape_sub, Hshape.
  rewrite -> Foralltc_cons_iff in Haclk_lt, Hclk_lt.
  destruct Hshape_sub as (_ & (Ha & Ha') & (Hb & Hb')), 
    Hshape as (_ & (Ha'' & _) & (Hb'' & _)), 
    Haclk_lt as (Eaclk_lt & Haclk_lt), Hclk_lt as (Eclk_lt & Hclk_lt).
  simpl in Ha, Hb, Eaclk_lt, Eclk_lt, Ha'', Hb''.

  rewrite -> List.Forall_forall in Hshape_chn, Hclk_lt, Haclk_lt.

  (* TODO repetition elimination *)
  split.
  all: rewrite -> Foralltc_cons_iff, -> List.Forall_app.
  - split; [ | split ].
    + simpl.
      apply List.Forall_app.
      split.
      * unfold tc_rootaclk.
        change (fun tc' => _) with (fun tc' => (fun ni => info_aclk ni <= clk) (tc_rootinfo tc')) in Ha'' |- *.
        rewrite <- Forall_map in Ha'' |- *.
        now rewrite <- Hinfosame.
      * eapply List.Forall_impl.
        2: apply Ha.
        simpl.
        lia.
    + rewrite -> List.Forall_forall.
      intros new_ch Hin_newch.
      pose proof (Hcorr_inr _ Hin_newch) as (ch & Hin_ch & Hso).
      (* now specialize (IH _ Hin_ch (Hshape_chn _ Hin_ch) (Haclk_bounded _ Hin_ch) _ Hso). *)
      eapply IH; eauto.
    + assumption.
  - split; [ | split ].
    + simpl.
      unfold tc_rootaclk.
      rewrite <- map_map, -> map_app, <- Hinfosame, <- map_app, -> map_map.
      fold tc_rootaclk.
      rewrite -> map_app.
      apply StronglySorted_app.
      * assumption.
      * assumption.
      * change (fun tc' => _) with (fun tc' => (fun a => a <= clk) (tc_rootaclk tc')) in Ha''.
        change (fun tc' => _) with (fun tc' => (fun a => a <= Q u) (tc_rootaclk tc')) in Ha.
        change (fun tc' => _) with (fun tc' => (fun a => Q u < a) (tc_rootaclk tc')) in Eaclk_lt.
        rewrite <- Forall_map, -> List.Forall_forall in Ha, Ha'', Eaclk_lt.
        firstorder lia.
    + rewrite -> List.Forall_forall.
      intros new_ch Hin_newch.
      pose proof (Hcorr_inr _ Hin_newch) as (ch & Hin_ch & Hso).
      eapply IH; eauto.
    + assumption.
Qed.

(* now, put everything together *)

Lemma tc_attach_nodes_tc_shape_inv tc tc' 
  (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc') 
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc')
  (Hrespect : tc_respect tc' tc) :
  tc_shape_inv (tc_attach_nodes 
    (snd (tc_detach_nodes (tc_get_updated_nodes_join tc tc') tc)) 
    (tc_get_updated_nodes_join tc tc')).
Proof.
  pose proof (tc_attach_nodes_result 
    (snd (tc_detach_nodes (tc_get_updated_nodes_join tc tc') tc))
    (tc_get_updated_nodes_join tc tc')) as Hso.
  remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
  destruct (tc_detach_nodes prefix_tc' tc) as (pivot, forest) eqn:Edetach.
  simpl in Hso |- *.
  pose proof Hso as Hnodup.
  pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
  rewrite <- Eprefix in Hprefix.
  pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix Hshape') as Hshape_pf.
  assert (forest = snd (tc_detach_nodes prefix_tc' tc)) as Eforest by now rewrite -> Edetach.

  (* first, get nodup *)
  eapply simple_overlaytc_nodup in Hnodup.
  2:{
    intros t.
    destruct (find (has_same_tid t) forest) as [ res | ] eqn:E.
    2: simpl; constructor.
    apply find_some in E.
    destruct E as (E & _).
    pose proof (tc_shape_inv_tc_detach_nodes_snd prefix_tc' tc Hshape) as H.
    rewrite -> Edetach, -> List.Forall_forall in H.
    specialize (H _ E).
    destruct res.
    now apply tid_nodup, NoDup_cons_iff in H.
  }
  2:{
    pose proof (tc_detach_nodes_tid_nodup prefix_tc' tc (tid_nodup _ Hshape)) as Hnodup_forest.
    pose proof (tc_detach_nodes_forest_recombine _ _ (tid_nodup _ Hshape) (tid_nodup _ Hshape_pf)) as Hperm.
    rewrite <- Eforest in Hperm.
    eapply Permutation.Permutation_NoDup.
    1: apply Permutation.Permutation_map, Permutation.Permutation_flat_map, Hperm.
    apply tid_nodup_root_chn_split.
    rewrite -> Eforest.
    now apply tc_detach_nodes_tid_nodup, tid_nodup.
  }
  2:{
    apply tid_nodup in Hshape'.
    pose proof (tid_nodup_prefix_preserve _ _ (tc_get_updated_nodes_join_is_prefix tc tc') Hshape').
    congruence.
  }
  2:{
    intros t H t' Hres.
    destruct (find (has_same_tid t') forest) as [ [ni chn] | ] eqn:E.
    2: auto.
    simpl in Hres.
    (* cannot find in children *)
    apply find_some in E.
    destruct E as (Hin & E).
    rewrite -> has_same_tid_true in E.
    subst forest.
    (* pose proof Hin as Hsnd. *)
    pose proof (tc_detach_nodes_snd2fst prefix_tc' tc) as Hsnd2fst.
    rewrite -> List.Forall_forall in Hsnd2fst.
    apply Hsnd2fst in Hin.
    destruct Hin as (sub & Hin & Hsnd).
    rewrite <- tc_getnode_in_iff, -> in_map_iff in Hres.
    destruct Hres as (sub' & <- & Hin').
    pose proof (tc_detach_nodes_dom_excl _ sub _ H sub') as Htmp.
    rewrite <- Hsnd in Htmp.
    simpl in Htmp.
    specialize (Htmp (or_intror Hin') eq_refl).
    subst sub'.
    now apply self_not_in_tc_flatten_chn in Hin'.
  }

  (* next, get all the others *)
  pose proof Hso as Hother.
  eapply tc_shape_inv_simple_overlaytc_pre with (Q:=fun t => tc_getclk t tc) in Hother.
  2:{
    intros t.
    destruct (find (has_same_tid t) forest) as [ [(t', clk, aclk) chn] | ] eqn:E.
    2:{
      exists 0.
      constructor.
      all: simpl.
      2-3: rewrite -> Foralltc_cons_iff.
      2-3: split; [ | constructor ].
      2-3: simpl.
      2-3: constructor.
      now repeat constructor.
    }
    simpl.
    apply find_some in E.
    rewrite -> has_same_tid_true in E.
    simpl in E.
    destruct E as (Hin & <-).
    (* unify getclk t tc and clk ... slightly troublesome *)
    pose proof (tc_detach_nodes_snd_is_subprefix prefix_tc' tc) as Hsnd2pf.
    pose proof (tc_shape_inv_tc_detach_nodes_snd prefix_tc' tc Hshape) as Hshape_forest.
    rewrite <- Eforest, -> List.Forall_forall in Hsnd2pf, Hshape_forest.
    specialize (Hsnd2pf _ Hin).
    specialize (Hshape_forest _ Hin).
    destruct Hsnd2pf as (sub & Hin_sub & E).
    pose proof (prefixtc_rootinfo_same _ _ E) as Einfo.
    pose proof (tid_nodup_find_self_sub _ (tid_nodup _ Hshape) _ Hin_sub) as Hres.
    apply option.fmap_Some in Hres.
    destruct Hres as (res & Hres & Einfo').
    unfold tc_roottid in Hres.
    rewrite <- Einfo in Hres.
    simpl in Hres.
    assert (tc_getclk t tc = clk) as <-.
    {
      unfold tc_getclk, tc_rootclk.
      now rewrite -> Hres, <- Einfo', <- Einfo.
    }
    eauto.
  }
  2:{
    pose proof (tc_shape_inv_prefix_preserve _ _ (tc_get_updated_nodes_join_is_prefix tc tc') Hshape').
    congruence.
  }
  2:{
    pose proof (tc_get_updated_nodes_join_shape _ Hshape' _ Hrespect Hroot_clk_le).
    intuition congruence.
  }
  2:{
    pose proof (tc_get_updated_nodes_join_shape _ Hshape' _ Hrespect Hroot_clk_le).
    intuition congruence.
  }

  now apply tc_shape_inv_conj_iff.
Qed.

(* 
  finally needed:
  - join implements pointwise-max
  - join preserves shape inv
  - join preserves respect in both directions
*)

End TreeClock.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant is_left => "(fun x -> x)".
Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ].
Extract Constant PeanoNat.Nat.leb => "( <= )".

(* FIXME: simply Import stdpp will result in mysterious extracted code. 
    Currently do not know why and there is no related report in Iris/stdpp/issues ...
    will investigate it later. For now, ignore this
*)
Extraction "extraction/lib/tcimpl.ml" tc_join tc_flatten tc_rootinfo.
