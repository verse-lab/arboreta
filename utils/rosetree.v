From Coq Require Import List Bool Lia PeanoNat Sorting RelationClasses Permutation.
From arboreta Require Import util util_perm.

From stdpp Require list.

(* Use some typeclasses to insert default arguments. *)
(* According to the Coq manual, singleton typeclasses have some benefits, so use them? *)

Class EqDec (A : Type) :=
  eqdec : forall (x y : A), {x = y} + {x <> y}.

Class IdGetter (A B : Type) := 
  info_id : A -> B.

Global Arguments info_id {_ _ _} !_ /.

Section RoseTree.

Local Ltac intuition_solver ::= auto. (* follow the modification in stdpp *)

Local Tactic Notation "eqsolve" := 
  intuition congruence; intuition discriminate.

Context {A : Type}.

(* A rosetree is a node with some information of type A, and some rosetrees as children. *)

Inductive tree : Type := Node (ni : A) (chn : list tree).

Definition tr_rootinfo tr := let 'Node ni _ := tr in ni.

Definition tr_rootchn tr := let 'Node _ chn := tr in chn.

Section Tree_Basics.

  Fact tree_recons tr : tr = Node (tr_rootinfo tr) (tr_rootchn tr).
  Proof. now destruct tr. Qed.

End Tree_Basics. 

Section Tree_Height.

  Fixpoint tr_height tr : nat := S (List.list_max (map tr_height (tr_rootchn tr))).

  Fact tr_height_le [n chn ch] (Hin : In ch chn) (Hle : List.list_max (map tr_height chn) <= n) :
    tr_height ch <= n.
  Proof.
    eapply list_max_le, Forall_map, List.Forall_forall in Hle.
    2: apply Hin.
    assumption.
  Qed.

  Fact tr_height_map_nil chn : List.list_max (map tr_height chn) <= 0 <-> chn = nil.
  Proof. 
    split; intros H.
    - destruct chn as [| [? ?] ?].
      all: simpl in *; try lia; auto.
    - subst chn. simpl. lia.
  Qed.

  (* One can prove an enhanced induction principle using a step-indexing like argument. *)

  Lemma tr_ind_bounded_height (P : tree -> Prop)
    (Hind : forall (ni : A) (chn : list tree), Forall P chn -> P (Node ni chn)) n : 
    forall (tr : tree) (Hh : tr_height tr <= n), P tr.
  Proof.
    induction n as [ n IH ] using Wf_nat.lt_wf_ind; intros.
    destruct tr as (ni & chn). 
    simpl in Hh.
    destruct n; [ inversion Hh | ].
    apply le_S_n, list_max_le, Forall_map in Hh. 
    eapply Hind, List.Forall_impl.
    2: apply Hh.
    intros.
    apply IH with (m:=n).
    - constructor.
    - assumption.
  Qed.

  Lemma tree_ind_2 (P : tree -> Prop)
    (Hind : forall (ni : A) (chn : list tree), Forall P chn -> P (Node ni chn)) : 
    forall (tr : tree), P tr.
  Proof.
    intros tr.
    apply tr_ind_bounded_height with (n:=tr_height tr). 
    - assumption.
    - constructor.
  Qed.

  (* sometimes can avoid the pervasive usage of Forall_forall *)
  Corollary tree_ind_2' (P : tree -> Prop)
    (Hind : forall (ni : A) (chn : list tree), (forall ch, In ch chn -> P ch) -> P (Node ni chn)) : 
    forall (tr : tree), P tr.
  Proof. apply tree_ind_2. intros. apply Hind. now rewrite Forall_forall in H. Qed.

End Tree_Height.

Section Tree_Equality.

  (* Rosetree has decidable equality as long as A has decidable equality.  *)

  Context `{A_eqdec : EqDec A}.

  Fixpoint tr_eqb tr tr' :=
    let 'Node ni chn := tr in
    let 'Node ni' chn' := tr' in
    if eqdec ni ni'
    then 
      (if Nat.eq_dec (length chn) (length chn')
        then 
          List.forallb (fun pp => (fst pp) (snd pp))
            (List.combine (map tr_eqb chn) chn')
        else false)
    else false.

  Lemma tr_eqP tr : forall tr', tr_eqb tr tr' = true <-> tr = tr'.
  Proof.
    induction tr as [ni chn IH] using tree_ind_2; intros [ni' chn']; simpl.
    destruct (eqdec ni ni') as [ <- | Hnineq ], (Nat.eq_dec (length chn) (length chn')) as [ El | Hlneq ].
    all: try eqsolve.
    rewrite -> forallb_forall, <- Forall_forall.
    revert chn' El.
    induction chn as [ | ch chn IH' ]; intros.
    all: destruct chn' as [ | ch' chn' ]; try discriminate.
    - intuition constructor.
    - injection El as El.
      simpl.
      rewrite -> Forall_cons_iff in IH |- *.
      simpl.
      specialize (IH' (proj2 IH) _ El).
      rewrite -> (proj1 IH), IH'.
      intuition congruence.
  Qed.

  Definition tr_eqdec (tr tr' : tree) : {tr = tr'} + {tr <> tr'}.
  Proof.
    destruct (tr_eqb tr tr') eqn:E.
    - apply tr_eqP in E.
      now left.
    - right.
      intros EE.
      apply tr_eqP in EE.
      congruence.
  Qed.

End Tree_Equality.

Section Core_Auxiliary_Functions.

  (* flat_map f l = concat (map f l) *)
  Fixpoint tr_flatten tr := tr :: (flat_map tr_flatten (tr_rootchn tr)).

  Fact tr_flatten_self_in tr : In tr (tr_flatten tr).
  Proof. destruct tr as [? ?]. simpl. now left. Qed.

  Fact trs_flatten_self_in [tr trs] (Hin : In tr trs) : In tr (flat_map tr_flatten trs).
  Proof. eapply in_flat_map_conv; eauto. apply tr_flatten_self_in. Qed.

  Fact tr_flatten_proper_subtr [sub tr] : 
    In sub (flat_map tr_flatten (tr_rootchn tr)) -> In sub (tr_flatten tr).
  Proof. intros H. rewrite (tree_recons tr). simpl. tauto. Qed.
(*
  Fact tr_flatten_direct_result tr : tr_flatten tr = tr :: (flat_map tr_flatten (tr_rootchn tr)).
  Proof. now destruct tr as [? ?]. Qed.
*)
  Fact tr_flatten_root_chn_split trs :
    Permutation (flat_map tr_flatten trs) (trs ++ (flat_map tr_flatten (flat_map tr_rootchn trs))).
  Proof.
    induction trs as [ | [ni chn] trs IH ].
    1: constructor.
    simpl.
    constructor.
    now rewrite -> flat_map_app, -> IH, -> Permutation_app_swap_app.
  Qed.

  (* One can prove that a tree is not a subtree of any of the subtree of its children by comparing height. *)

  Fact tr_height_else_lt tr :
    Forall (fun tr' => tr_height tr' < tr_height tr) (flat_map tr_flatten (tr_rootchn tr)).
  Proof.
    induction tr as [ni chn IH] using tree_ind_2; intros.
    rewrite -> List.Forall_forall in IH |- *.
    simpl.
    intros sub ([ni_ch chn_ch] & Hin_ch & Hin)%in_flat_map.
    simpl in Hin.
    specialize (IH _ Hin_ch).
    rewrite -> List.Forall_forall in IH.
    simpl in IH.
    unfold lt in IH |- *.
    assert (tr_height (Node ni_ch chn_ch) <= list_max (map tr_height chn)) as H
      by (eapply tr_height_le; eauto).
    destruct Hin as [ <- | Hin ].
    - lia.
    - transitivity (S (list_max (map tr_height chn_ch))).
      1: now apply IH.
      simpl in H.
      lia.
  Qed.

  Fact self_not_in_tr_flatten_chn tr : ~ In tr (flat_map tr_flatten (tr_rootchn tr)).
  Proof.
    pose proof (tr_height_else_lt tr) as Hlt.
    rewrite -> List.Forall_forall in Hlt.
    intros Hin%Hlt.
    lia.
  Qed.

  Fixpoint tr_locate (tr : tree) (pos : list nat) : option tree :=
    match pos with
    | nil => Some tr
    | x :: pos' => 
      match nth_error (tr_rootchn tr) x with
      | Some ch => tr_locate ch pos'
      | None => None
      end
    end.

  Fact tr_locate_pos_app [pos1] : forall [tr sub] (H : tr_locate tr pos1 = Some sub) pos2,
    tr_locate tr (pos1 ++ pos2) = tr_locate sub pos2.
  Proof.
    induction pos1 as [ | x pos1 IH ]; intros; simpl in *.
    - injection H as <-.
      reflexivity.
    - destruct tr as [ni chn].
      simpl in *.
      destruct (nth_error chn x) eqn:E; try discriminate.
      now apply IH.
  Qed.

  Fixpoint tr_locate_update (tr : tree) (pos : list nat) (sub : tree) : tree :=
    match pos with
    | nil => sub
    | x :: pos' => 
      match nth_error (tr_rootchn tr) x with
      | Some ch => Node (tr_rootinfo tr) (upd_nth x (tr_rootchn tr) (tr_locate_update ch pos' sub))
      | None => tr
      end
    end.

  (* TODO update related things? or put them below? *)

End Core_Auxiliary_Functions.

Section Tree_Size.

  Definition tr_size tr := length (tr_flatten tr).

  Global Arguments tr_size ! _ /.

  Fact tr_size_chn_lt_full tr : length (tr_rootchn tr) < tr_size tr.
  Proof.
    destruct tr; simpl.
    erewrite -> Permutation_length with (l:=(flat_map _ _)).
    2: apply tr_flatten_root_chn_split.
    rewrite app_length.
    lia.
  Qed.

  Fact trs_size_le_full trs : length trs <= length (flat_map tr_flatten trs).
  Proof.
    induction trs as [ | tr trs IH ]; simpl.
    - apply le_n.
    - rewrite app_length.
      destruct tr.
      simpl.
      lia.
  Qed.

  Fact tr_size_ch_lt_full [ch tr] (H : In ch (tr_rootchn tr)) : 
    tr_size ch < tr_size tr.
  Proof.
    destruct tr; simpl in H |- *.
    pose proof (in_split _ _ H) as (pre & suf & ->).
    rewrite -> flat_map_app.
    simpl.
    erewrite -> Permutation_length.
    2: apply Permutation_app_swap_app.
    rewrite ! app_length.
    unfold tr_size. 
    lia.
  Qed.

  Fact tr_size_subtr_le_full [tr] : forall [sub] (H : In sub (tr_flatten tr)), 
    tr_size sub <= tr_size tr.
  Proof.
    induction tr as [ni chn IH] using tree_ind_2'; intros; simpl in H |- *.
    destruct H as [ <- | (ch & Hin_ch & H)%in_flat_map ]; simpl.
    1: constructor.
    transitivity (tr_size ch).
    2: pose proof (tr_size_ch_lt_full (tr:=Node ni chn) Hin_ch) as Htmp; simpl in Htmp; lia.
    firstorder.
  Qed.

End Tree_Size.

Section Subtree_Theory.

  (* tr1 is a subtree of tr2 *)
  Definition subtr tr1 tr2 : Prop := In tr1 (tr_flatten tr2).

  Global Arguments subtr _ _/.

  Fact subtr_chn [tr ch] : In ch (tr_rootchn tr) -> subtr ch tr.
  Proof.
    intros H.
    hnf.
    rewrite (tree_recons tr).
    simpl; right.
    apply in_flat_map.
    exists ch.
    split; [ assumption | apply tr_flatten_self_in ].
  Qed.

  Lemma subtr_trans [tr tr' tr''] : subtr tr'' tr' -> subtr tr' tr -> subtr tr'' tr.
  Proof.
    revert tr'' tr'.
    induction tr as [ni chn IH] using tree_ind_2'; intros.
    simpl in H, H0. 
    destruct H0 as [ <- | (ch & Hin_ch & H0)%in_flat_map ]; auto.
    simpl; right; apply in_flat_map; exists ch.
    firstorder.
  Qed.

  Corollary subtr_flatten_incl [tr tr'] (H : subtr tr tr') : incl (tr_flatten tr) (tr_flatten tr').
  Proof. hnf. intros sub' H'. revert H' H. apply subtr_trans. Qed.

  (* proof-relevant witness of subtree *)
  Definition subtr_witness (l : list nat) sub tr := tr_locate tr l = Some sub.

  Lemma subtr_witness_subtr [l] :
    forall [sub tr], subtr_witness l sub tr -> subtr sub tr.
  Proof.
    induction l as [ | x l IH ]; intros; hnf in H; simpl in H.
    - injection H as <-. 
      apply tr_flatten_self_in.
    - destruct (nth_error (tr_rootchn tr) x) as [ res | ] eqn:E; try eqsolve.
      apply IH in H.
      apply nth_error_In in E.
      eapply subtr_trans; [ apply H | ].
      now apply subtr_chn.
  Qed.

  Lemma subtr_subtr_witness [tr] :
    forall [sub], subtr sub tr -> exists l, subtr_witness l sub tr.
  Proof.
    induction tr as [ni chn IH] using tree_ind_2'; intros.
    simpl in H. 
    destruct H as [ <- | (ch & Hin_ch & Hin)%in_flat_map ].
    - now exists nil.
    - specialize (IH _ Hin_ch _ Hin).
      destruct IH as (l & H).
      apply In_nth_error in Hin_ch. 
      destruct Hin_ch as (n & E).
      exists (n :: l); hnf; simpl; now rewrite E.
  Qed. 

  Corollary subtr_witness_iff sub tr :
    subtr sub tr <-> exists l, subtr_witness l sub tr.
  Proof.
    split; intros.
    - now apply subtr_subtr_witness in H.
    - destruct H as (l & H). now apply subtr_witness_subtr in H.
  Qed.

  (* if sub has a parent and its parent is a subtree of tr, then sub must be a subtree of a child of tr *)
  Fact subtr_has_par [sub_par sub tr] (Hsub : subtr sub_par tr) (Hin : In sub (tr_rootchn sub_par)) :
    exists ch, In ch (tr_rootchn tr) /\ subtr sub ch.
  Proof.
    destruct tr as [ni chn]; simpl.
    simpl in Hsub.
    destruct Hsub as [ <- | (ch & Hin_ch & Hsub)%in_flat_map ].
    - exists sub.
      auto using tr_flatten_self_in.
    - exists ch.
      split; auto.
      eapply subtr_trans.
      + apply subtr_chn, Hin.
      + assumption.
  Qed.

  Lemma subtr_flatten_sublist [tr tr'] (H : subtr tr tr') : list.sublist (tr_flatten tr) (tr_flatten tr').
  Proof.
    apply subtr_subtr_witness in H.
    destruct H as (l & H).
    unfold subtr_witness in H.
    revert tr tr' H.
    induction l as [ | x l IH ]; intros.
    - now injection H as ->.
    - destruct tr' as [ a' chn' ].
      simpl in H.
      destruct (nth_error chn' x) as [ ch' | ] eqn:E; try discriminate.
      simpl.
      apply list.sublist_cons.
      etransitivity.
      1: eapply IH; eauto.
      apply nth_error_split in E.
      destruct E as (pre & suf & -> & _).
      rewrite flat_map_app.
      simpl.
      now apply list.sublist_inserts_l, list.sublist_inserts_r.
  Qed.

End Subtree_Theory.

Section Forall_Tree_Theory.

  (* Sometimes it is convenient to have a structurally recursive predicate telling that every 
      subtree inside the tree satisfies some predicate. *)

  Inductive Foralltr (P : tree -> Prop) : tree -> Prop :=
    Foralltr_intro : forall ni chn, 
      P (Node ni chn) -> Forall (Foralltr P) chn -> Foralltr P (Node ni chn). 

  Fact Foralltr_cons_iff P ni chn :
    Foralltr P (Node ni chn) <-> (P (Node ni chn) /\ Forall (Foralltr P) chn).
  Proof.
    split; intros.
    - now inversion H.
    - now apply Foralltr_intro.
  Qed.

  Fact Foralltr_cons_iff' P tr : Foralltr P tr <-> (P tr /\ Forall (Foralltr P) (tr_rootchn tr)).
  Proof. destruct tr. now apply Foralltr_cons_iff. Qed.

  Fact Foralltr_self [P tr] (H : Foralltr P tr) : P tr.
  Proof. destruct tr. now apply Foralltr_cons_iff in H. Qed.

  Fact Foralltr_chn [P tr] (H : Foralltr P tr) : Forall (Foralltr P) (tr_rootchn tr).
  Proof. destruct tr. now apply Foralltr_cons_iff in H. Qed.

  Fact Foralltr_chn_selves [P tr] (H : Foralltr P tr) : Forall P (tr_rootchn tr).
  Proof. eapply List.Forall_impl. 1: apply Foralltr_self. now apply Foralltr_chn. Qed.

  Lemma Foralltr_Forall_subtree (P : tree -> Prop) tr :
    Foralltr P tr <-> Forall P (tr_flatten tr).
  Proof.
    induction tr as [ni chn IH] using tree_ind_2; intros.
    simpl.
    rewrite -> ! Foralltr_cons_iff, List.Forall_cons_iff, -> ! List.Forall_forall.
    setoid_rewrite in_flat_map.
    repeat setoid_rewrite -> List.Forall_forall in IH.
    firstorder. 
    apply IH; firstorder. 
  Qed.

  Corollary Foralltr_trivial (P : tree -> Prop) (H : forall tr, P tr) tr : Foralltr P tr.
  Proof. now apply Foralltr_Forall_subtree, List.Forall_forall. Qed.

  Lemma Foralltr_impl_pre (P Q : tree -> Prop) [tr] 
    (Hf : Foralltr (fun tr' => P tr' -> Q tr') tr) (H : Foralltr P tr) : Foralltr Q tr.
  Proof.
    induction tr as [ni chn IH] using tree_ind_2; intros.
    rewrite -> Foralltr_cons_iff in Hf, H |- *.
    destruct H as (H & H0), Hf as (Hf & Hf0).
    rewrite -> Forall_forall in *. 
    split; try firstorder.
  Qed.

  Corollary Foralltr_impl (P Q : tree -> Prop) (Hpq : forall tr, P tr -> Q tr) [tr] 
    (H : Foralltr P tr) : Foralltr Q tr.
  Proof. eapply Foralltr_impl_pre. 2: apply H. now apply Foralltr_trivial. Qed.

  Lemma Foralltr_Forall_chn_comm P tr :
    Foralltr (fun tr' => Forall P (tr_rootchn tr')) tr <-> Forall (Foralltr P) (tr_rootchn tr).
  Proof.
    induction tr as [ni chn IH] using tree_ind_2; intros.
    rewrite -> Foralltr_cons_iff at 1. simpl.
    rewrite <- list.Forall_and. 
    repeat rewrite -> List.Forall_forall in *.
    setoid_rewrite -> Foralltr_cons_iff' at 2.
    firstorder.
  Qed.

  Lemma Foralltr_Forall_flat_map_In P trs :
    Forall (Foralltr P) trs <-> (forall tr, In tr (flat_map tr_flatten trs) -> P tr).
  Proof.
    rewrite Forall_forall.
    setoid_rewrite Foralltr_Forall_subtree.
    setoid_rewrite Forall_forall.
    setoid_rewrite in_flat_map.
    firstorder.
  Qed.

  Lemma Foralltr_and (P Q : tree -> Prop) tr :
    Foralltr (fun tr => P tr /\ Q tr) tr <-> Foralltr P tr /\ Foralltr Q tr.
  Proof.
    induction tr as [ni chn IH] using tree_ind_2; intros.
    rewrite -> ! Foralltr_cons_iff, -> ! List.Forall_forall.
    rewrite -> List.Forall_forall in IH.
    firstorder.
  Qed.

  Lemma Foralltr_idempotent (P : tree -> Prop) tr :
    Foralltr (Foralltr P) tr <-> Foralltr P tr.
  Proof.
    induction tr as [ni chn IH] using tree_ind_2; intros.
    rewrite -> ! Foralltr_cons_iff, -> ! List.Forall_forall.
    rewrite -> List.Forall_forall in IH.
    firstorder.
  Qed.

  Corollary Foralltr_Foralltr_subtree (P : tree -> Prop) tr :
    Foralltr P tr <-> Forall (Foralltr P) (tr_flatten tr).
  Proof. now rewrite <- Foralltr_idempotent, -> Foralltr_Forall_subtree. Qed.

  Fact Foralltr_subtr P [tr sub] (Hsub : subtr sub tr) (H : Foralltr P tr) : P sub.
  Proof. rewrite -> Foralltr_Forall_subtree, -> Forall_forall in H. auto. Qed. 

  Fact Foralltr_ch P [tr ch] (Hin_ch : In ch (tr_rootchn tr)) (H : Foralltr P tr) : P ch.
  Proof. eapply Foralltr_subtr; eauto. now apply subtr_chn. Qed. 

End Forall_Tree_Theory.

Section Tree_Prefix_Theory.

  Inductive prefixtr : tree -> tree -> Prop :=
    prefixtr_intro : forall ni chn chn_sub prefix_chn, 
      list.sublist chn_sub chn ->
      Forall2 prefixtr prefix_chn chn_sub ->
      prefixtr (Node ni prefix_chn) (Node ni chn).

  Fact prefixtr_inv [ni1 ni2 chn1 chn2] (Hprefix: prefixtr (Node ni1 chn1) (Node ni2 chn2)) :
    ni1 = ni2 /\ exists chn2_sub, list.sublist chn2_sub chn2 /\ Forall2 prefixtr chn1 chn2_sub.
  Proof. inversion Hprefix; subst. firstorder. Qed.

  Lemma prefixtr_ind_2 (P : tree -> tree -> Prop)
    (Hind : forall (ni : A) (chn1 chn2_sub chn2 : list tree), 
      list.sublist chn2_sub chn2 ->
      Forall2 prefixtr chn1 chn2_sub -> 
      Forall2 P chn1 chn2_sub -> P (Node ni chn1) (Node ni chn2))
    (tr1 tr2 : tree) (H : prefixtr tr1 tr2) : P tr1 tr2.
  Proof.
    revert tr2 H.
    induction tr1 as [ni chn1 IH] using tree_ind_2; intros.
    destruct tr2 as [ni2 chn2].
    apply prefixtr_inv in H.
    destruct H as (<- & (chn2_sub & Hsub & H)).
    eapply Hind; eauto.
    clear -H IH.
    induction H.
    1: constructor.
    rewrite Forall_cons_iff in IH.
    constructor; firstorder.
  Qed.

  Fact prefixtr_rootinfo_same [tr tr'] (Hprefix : prefixtr tr tr') :
    tr_rootinfo tr = tr_rootinfo tr'.
  Proof. 
    destruct tr, tr'.
    apply prefixtr_inv in Hprefix.
    intuition congruence.
  Qed.

  Corollary prefixtr_rootinfo_same_map [trs trs'] (Hprefix : Forall2 prefixtr trs trs') :
    map tr_rootinfo trs = map tr_rootinfo trs'.
  Proof. eapply map_ext_Forall2, list.Forall2_impl; eauto. exact prefixtr_rootinfo_same. Qed.

  #[export] Instance prefixtr_refl : Reflexive prefixtr.
  Proof.
    hnf.
    intros tr.
    induction tr as [ni chn IH] using tree_ind_2; intros.
    econstructor.
    1: reflexivity.
    now apply list.Forall_Forall2_diag.
  Qed.

  #[export] Instance prefixtr_trans : Transitive prefixtr.
  Proof.
    hnf.
    intros tr1 tr2 tr3 H.
    revert tr3.
    induction H as [ni chn1 chn2_sub chn2 Hsub H IH] using prefixtr_ind_2; intros.
    destruct tr3 as [ ni' chn3 ].
    apply prefixtr_inv in H0.
    destruct H0 as (<- & (chn3_sub & Hsub3 & H0)).
    pose proof (sublist_Forall2 _ Hsub H0) as (chn3_sub' & Hgoal1 & H1).
    econstructor.
    1: etransitivity; eauto.
    pose proof (conj H IH) as HH%Forall2_and.
    eapply list.Forall2_transitive; eauto.
    firstorder.
  Qed.

  (* if a tree is generated in a specific way, then it must be a prefix *)

  Lemma prefixtr_by_sublist_map [a chn' chn] (f : tree -> tree)
    (H : Forall (fun tr => prefixtr (f tr) tr) chn) 
    (H' : list.sublist chn' (map f chn)) : 
    prefixtr (Node a chn') (Node a chn).
  Proof.
    apply sublist_map_l_recover in H'.
    destruct H' as (chn'' & -> & Hsub).
    econstructor; eauto.
    eapply Forall2_mapself_l, sublist_Forall; eauto.
  Qed.

  Fact prefixtr_nil_l ni chn : prefixtr (Node ni nil) (Node ni chn).
  Proof.
    econstructor.
    2: reflexivity.
    apply list.sublist_nil_l.
  Qed.

  Lemma prefixtr_flatten_sublist [tr1 tr2] (Hprefix : prefixtr tr1 tr2) :
    list.sublist (map tr_rootinfo (tr_flatten tr1)) (map tr_rootinfo (tr_flatten tr2)).
  Proof.
    induction Hprefix as [ni chn1 chn2_sub chn2 Hsub Hprefix IH] using prefixtr_ind_2.
    simpl.
    apply list.sublist_skip.
    transitivity (map tr_rootinfo (flat_map tr_flatten chn2_sub)).
    - clear -IH.
      induction IH.
      1: auto.
      simpl.
      rewrite ! map_app.
      now apply list.sublist_app.
    - apply sublist_map.
      clear -Hsub.
      induction Hsub; simpl; auto.
      + now apply list.sublist_app.
      + now apply list.sublist_inserts_l.
  Qed.

  Corollary prefixtr_size_le [tr1 tr2] (Hprefix : prefixtr tr1 tr2) :
    length (tr_flatten tr1) <= length (tr_flatten tr2).
  Proof. rewrite <- ! map_length with (f:=tr_rootinfo). now apply list.sublist_length, prefixtr_flatten_sublist. Qed.

  Corollary prefixtr_flatten_info_incl [tr1 tr2] (Hprefix : prefixtr tr1 tr2) :
    incl (map tr_rootinfo (tr_flatten tr1)) (map tr_rootinfo (tr_flatten tr2)).
  Proof.
    intros ni Hin.
    eapply sublist_In.
    1: eapply prefixtr_flatten_sublist; eauto.
    assumption.
  Qed.

  (* A interesting property of prefix is that if the size of a prefix is equal to 
    the original tree, then the prefix is exactly the original tree. *)

  Lemma prefixtr_size_eq_tr_eq [tr1 tr2] (Hprefix : prefixtr tr1 tr2) 
    (H : length (tr_flatten tr1) = length (tr_flatten tr2)) : tr1 = tr2.
  Proof.
    induction Hprefix as [ni chn1 chn2_sub chn2 Hsub Hprefix IH] using prefixtr_ind_2.
    injection H as H.
    f_equal; clear ni.
    pose proof Hprefix as Hple.
    eapply list.Forall2_impl in Hple.
    2: apply prefixtr_size_le.
    pose proof Hple as Hple'%Forall2_map.
    pose proof Hple' as Hle1%pointwise_le_sum_le.
    pose proof Hsub as H2.
    apply sublist_map with (f:=fun t => length (tr_flatten t)), sublist_sum_le in H2.
    rewrite -> 2 flat_map_concat_map, -> 2 length_concat_sum, -> 2 map_map in H.
    assert (chn2_sub = chn2) as ->.
    {
      apply sublist_map_sum_eq_ with (f:=fun t => length (tr_flatten t)); auto.
      - intros [? ?]; simpl; lia.
      - lia.
    }
    eapply pointwise_le_sum_le_; eauto.
  Qed.

End Tree_Prefix_Theory.

(* Now we start to consider trees with (decidable) indices. *)

Context {B : Type} `{B_getter : IdGetter A B}.

Definition tr_rootid tr := info_id (tr_rootinfo tr).

Global Arguments tr_rootid !_ /.

Fact tr_rootinfo_id_inj : forall [x y], tr_rootinfo x = tr_rootinfo y -> tr_rootid x = tr_rootid y.
Proof. intros [ni ?] [ni' ?]. unfold tr_rootid. now intros ->. Qed.

Fact prefixtr_rootid_same [tr tr'] (Hprefix : prefixtr tr tr') :
  tr_rootid tr = tr_rootid tr'.
Proof. unfold tr_rootid. erewrite prefixtr_rootinfo_same; eauto. Qed.

Fact Permutation_rootinfo2rootid_pre [B' : Type] (g : tree -> B') (h : B' -> B) 
  (Hh : forall tr, h (g tr) = tr_rootid tr) [trs1 trs2]
  (Hperm : Permutation (map g trs1) (map g trs2)) :
  Permutation (map tr_rootid trs1) (map tr_rootid trs2).
Proof.
  pose proof Hperm as Hperm'%(Permutation_map h).
  rewrite -> 2 map_map, -> 2 (map_ext (fun x : tree => h (g x)) tr_rootid) in Hperm'; auto.
Qed.

Fact Permutation_rootinfo2rootid [trs1 trs2]
  (H : Permutation (map tr_rootinfo trs1) (map tr_rootinfo trs2)) :
  Permutation (map tr_rootid trs1) (map tr_rootid trs2).
Proof. eapply Permutation_rootinfo2rootid_pre with (h:=info_id); eauto. Qed.

Section NoDup_Indices_Theory.

  Definition trs_roots_NoDupId trs := List.NoDup (map tr_rootid trs).
  Definition trs_NoDupId trs := Eval unfold trs_roots_NoDupId in trs_roots_NoDupId (flat_map tr_flatten trs).
  Definition tr_NoDupId tr := Eval unfold trs_roots_NoDupId in trs_roots_NoDupId (tr_flatten tr).

  Fact id_nodup_rootinfo_nodup [trs] (H : trs_roots_NoDupId trs) : NoDup (map tr_rootinfo trs).
  Proof.
    unfold trs_roots_NoDupId, tr_rootid in H.
    rewrite <- map_map in H.
    eapply NoDup_map_inv; eauto.
  Qed.

  Lemma id_nodup_trs_each [trs] (H : trs_NoDupId trs)
    [tr] (Hin : In tr trs) : tr_NoDupId tr.
  Proof.
    unfold trs_NoDupId in H. 
    rewrite -> flat_map_concat_map, -> concat_map, -> map_map in H.
    apply NoDup_concat in H.
    rewrite -> List.Forall_map, List.Forall_forall in H.
    now apply H.
  Qed.

  Corollary id_nodup_ch [ch tr] (H : In ch (tr_rootchn tr)) 
    (Hnodup : tr_NoDupId tr) : tr_NoDupId ch.
  Proof.
    unfold tr_NoDupId in Hnodup.
    rewrite -> (tree_recons tr) in Hnodup.
    simpl in Hnodup.
    apply NoDup_cons_iff, proj2 in Hnodup.
    eapply id_nodup_trs_each; eauto.
  Qed.

  Lemma id_nodup_Foralltr_id tr : tr_NoDupId tr <-> Foralltr tr_NoDupId tr.
  Proof.
    induction tr as [ni chn IH] using tree_ind_2; intros.
    rewrite -> Foralltr_cons_iff.
    split; [ | intuition ].
    intros H.
    split; [ assumption | ].
    rewrite -> List.Forall_forall in IH |- *.
    intros tr Hin.
    rewrite <- IH.
    2: assumption.
    now apply (id_nodup_ch (tr:=(Node ni chn))) in Hin.
  Qed.

  Corollary id_nodup_subtr [sub tr] (H : subtr sub tr) 
    (Hnodup : tr_NoDupId tr) : tr_NoDupId sub.
  Proof. rewrite -> id_nodup_Foralltr_id in Hnodup; eapply Foralltr_subtr in H; [ | apply Hnodup ]; auto. Qed. 

  Fact id_nodup_rootid_sublist_preserve [trs1 trs2]
    (Hsub : list.sublist (map tr_rootid trs1) (map tr_rootid trs2))
    (Hnodup : trs_roots_NoDupId trs2) : trs_roots_NoDupId trs1.
  Proof. eapply sublist_NoDup; eauto. Qed.

  Corollary id_nodup_rootinfo_sublist_preserve [trs1 trs2]
    (Hsub : list.sublist (map tr_rootinfo trs1) (map tr_rootinfo trs2))
    (Hnodup : trs_roots_NoDupId trs2) : trs_roots_NoDupId trs1.
  Proof. 
    eapply id_nodup_rootid_sublist_preserve. 
    2: apply Hnodup.
    unfold tr_rootid.
    rewrite <- 2 (map_map tr_rootinfo).
    now apply sublist_map.
  Qed.

  Corollary id_nodup_prefix_preserve [tr tr'] (Hprefix : prefixtr tr tr') 
    (Hnodup : tr_NoDupId tr') : tr_NoDupId tr.
  Proof.
    eapply id_nodup_rootinfo_sublist_preserve.
    2: apply Hnodup.
    now apply prefixtr_flatten_sublist.
  Qed.

  Lemma id_nodup_root_chn_split [trs] (Hnodup : trs_NoDupId trs) : 
    trs_roots_NoDupId trs /\ trs_NoDupId (flat_map tr_rootchn trs).
  Proof.
    pose proof (tr_flatten_root_chn_split trs) as Hperm.
    apply Permutation_map with (f:=tr_rootid) in Hperm.
    rewrite -> map_app in Hperm.
    apply Permutation_NoDup in Hperm.
    2: assumption.
    now apply NoDup_app_ in Hperm.
  Qed.

  Lemma id_nodup_rootid_neq [tr] (Hnodup : tr_NoDupId tr) :
    Forall (Foralltr (fun tr' => tr_rootid tr <> tr_rootid tr')) (tr_rootchn tr).
  Proof.
    destruct tr as [ a chn ].
    hnf in Hnodup.
    simpl in Hnodup.
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as (Hnotin & Hnodup).
    simpl.
    apply Foralltr_Forall_flat_map_In.
    intros ? H%(in_map tr_rootid).
    congruence.
  Qed.

End NoDup_Indices_Theory.

Section Tree_Find.

  Context `{B_eqdec : EqDec B}.

  Definition has_same_id t tr := if (eqdec (tr_rootid tr) t) then true else false.

  Global Arguments has_same_id _ !_ /.

  Fact has_same_id_refl tr : has_same_id (tr_rootid tr) tr = true.
  Proof. unfold has_same_id. now rewrite eqdec_must_left. Qed.

  Fact has_same_id_true t tr : has_same_id t tr = true <-> t = tr_rootid tr.
  Proof. unfold has_same_id. destruct (eqdec (tr_rootid tr) t) as [ <- | ]; simpl; intuition congruence. Qed.

  Fact has_same_id_false t tr : has_same_id t tr = false <-> t <> tr_rootid tr.
  Proof. unfold has_same_id. destruct (eqdec (tr_rootid tr) t) as [ <- | ]; simpl; intuition congruence. Qed.

  Fact tr_rootinfo_has_same_id_congr : forall [x y], tr_rootinfo x = tr_rootinfo y -> 
    forall t, has_same_id t x = has_same_id t y.
  Proof. intros. unfold has_same_id. now rewrite tr_rootinfo_id_inj with (x:=x) (y:=y). Qed.

  Definition trs_find_node t trs := find (has_same_id t) trs.

  Definition tr_getnode t tr := Eval unfold trs_find_node in trs_find_node t (tr_flatten tr).

  Global Arguments tr_getnode _ !_ /.

  Fact trs_find_node_isSome_app t trs1 trs2 :
    isSome (trs_find_node t (trs1 ++ trs2)) = 
    if isSome (trs_find_node t trs1) then true else isSome (trs_find_node t trs2).
  Proof.
    unfold trs_find_node.
    rewrite find_app.
    now destruct (find _ trs1), (find _ trs2).
  Qed.

  Fact tr_getnode_self tr : tr_getnode (tr_rootid tr) tr = Some tr.
  Proof.
    destruct tr as [ni ?].
    simpl.
    now rewrite eqdec_must_left.
  Qed.

  Fact trs_find_has_id [t trs res]
    (Hres : trs_find_node t trs = Some res) : In res trs /\ tr_rootid res = t.
  Proof. 
    apply find_some in Hres.
    now rewrite -> has_same_id_true in Hres.
  Qed.

  Fact trs_find_in_iff t trs : 
    In t (map tr_rootid trs) <-> isSome (trs_find_node t trs) = true.
  Proof.
    rewrite -> in_map_iff.
    split.
    - intros (sub & <- & Hin).
      destruct (trs_find_node (tr_rootid sub) trs) eqn:E; simpl.
      1: auto.
      eapply find_none in E.
      2: apply Hin.
      now rewrite -> has_same_id_false in E.
    - destruct (trs_find_node t trs) as [ res | ] eqn:E.
      2: intros; discriminate.
      intros _.
      apply trs_find_has_id in E.
      destruct E.
      eauto.
  Qed.

  Fact tr_getnode_in_iff t tr : 
    In t (map tr_rootid (tr_flatten tr)) <-> isSome (tr_getnode t tr) = true.
  Proof. apply trs_find_in_iff. Qed.

  Fact tr_getnode_res_Foralltr (P : tree -> Prop) [t tr res]
    (Hp : Foralltr P tr) (Hres : tr_getnode t tr = Some res) : 
    P res /\ tr_rootid res = t.
  Proof.
    apply trs_find_has_id in Hres.
    destruct Hres as (Hin & ->).
    rewrite -> Foralltr_Forall_subtree, -> Forall_forall in Hp.
    firstorder. 
  Qed.

  Lemma id_nodup_find_self [trs] (Hnodup : trs_roots_NoDupId trs) :
    Forall (fun tr => trs_find_node (tr_rootid tr) trs = Some tr) trs.
  Proof.
    induction trs as [ | tr trs IH ].
    1: constructor.
    unfold trs_roots_NoDupId in *.
    simpl in Hnodup |- *.
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as (Hnotin & Hnodup).
    specialize (IH Hnodup).
    constructor.
    - now rewrite has_same_id_refl.
    - eapply Forall_impl.
      2: apply IH.
      simpl.
      intros tr' Hin.
      destruct (has_same_id (tr_rootid tr') tr) eqn:E; try assumption.
      rewrite -> has_same_id_true in E.
      apply trs_find_has_id, proj1, in_map with (f:=tr_rootid) in Hin.
      congruence.
  Qed.

  Corollary id_nodup_find_self' [tr] (Hnodup : tr_NoDupId tr) :
    Foralltr (fun tr0 => tr_getnode (tr_rootid tr0) tr = Some tr0) tr.
  Proof. now apply Foralltr_Forall_subtree, id_nodup_find_self. Qed.

  (* fully parameterized; B' can be regarded as the type of a portion of information *)
  (* FIXME: is this related with fmap, or something else about category theory? *)
  Corollary id_nodup_find_congr_fmap [B' : Type] (g : tree -> B') (h : B' -> B)
    (Hh : forall tr, h (g tr) = tr_rootid tr)
    [trs trs'] (Hnodup : trs_roots_NoDupId trs) (Hperm : Permutation (map g trs) (map g trs')) :
    forall t, base.fmap g (trs_find_node t trs) = base.fmap g (trs_find_node t trs').
  Proof.
    unfold trs_roots_NoDupId in Hnodup.
    pose proof (Permutation_rootinfo2rootid_pre _ _ Hh Hperm) as Hperm'.
    pose proof Hnodup as Hnodup2.
    eapply Permutation_NoDup in Hnodup2; eauto.

    intros t.
    pose proof (Permutation_in_mutual Hperm' t) as Hin.
    rewrite -> ! trs_find_in_iff in Hin.
    destruct (trs_find_node t trs) as [ res | ] eqn:Eres.
    all: destruct (trs_find_node t trs') as [ res' | ] eqn:Eres';
      try solve [ simpl in Hin; eqsolve ].
    simpl.
    f_equal.
    (* use NoDup_map_inj *)
    apply trs_find_has_id in Eres, Eres'.
    destruct Eres as (Hsub%(in_map g) & Et), Eres' as (Hsub'%(in_map g) & Et').
    eapply Permutation_in in Hsub.
    2: apply Hperm.
    eapply NoDup_map_inj with (l:=(map g trs')) (f:=h); auto.
    - rewrite -> map_map, -> (map_ext _ tr_rootid); auto.
    - rewrite ! Hh.
      congruence.
  Qed.

  Corollary id_nodup_find_self_fmap [C B' : Type] (f : B' -> C) (g : tree -> B') (h : B' -> B)
    (Hh : forall tr, h (g tr) = tr_rootid tr)
    [trs] (Hnodup : trs_roots_NoDupId trs) 
    [el] (Hin : In el (map g trs)) :
    base.fmap (fun tr0 => f (g tr0)) (trs_find_node (h el) trs) = Some (f el).
  Proof.
    apply in_map_iff in Hin.
    destruct Hin as (sub & <- & Hin_sub).
    pose proof (id_nodup_find_self Hnodup) as H.
    rewrite -> List.Forall_forall in H.
    specialize (H _ Hin_sub).
    now rewrite -> Hh, -> H.
  Qed.

  Corollary id_nodup_find_self_subtr [C : Type] (f : tree -> C) [tr sub]
    (Hnodup : tr_NoDupId tr) (Hin_sub : In sub (tr_flatten tr)) :
    base.fmap f (tr_getnode (tr_rootid sub) tr) = Some (f sub).
  Proof.
    eapply id_nodup_find_self_fmap in Hnodup.
    3: rewrite map_id_eq; apply Hin_sub.
    2: reflexivity.
    apply Hnodup.
  Qed.

  (* unification *)

  Lemma id_nodup_find_sublist [trs1 trs2] 
    (Hsub : list.sublist (map tr_rootinfo trs1) (map tr_rootinfo trs2))
    (Hnodup : trs_roots_NoDupId trs2)
    [t res] (E : base.fmap tr_rootinfo (trs_find_node t trs1) = Some res) :
    base.fmap tr_rootinfo (trs_find_node t trs2) = Some res.
  Proof.
    pose proof (id_nodup_rootinfo_sublist_preserve Hsub Hnodup) as Hnodup1.
    destruct (trs_find_node t trs1) as [ res1 | ] eqn:E1; try discriminate.
    injection E as <-.
    apply trs_find_has_id in E1.
    destruct E1 as (Hin%(in_map tr_rootinfo) & <-).
    pose proof (sublist_In Hsub Hin) as (res2 & E2 & Hin2)%in_map_iff.
    pose proof E2 as Et%tr_rootinfo_id_inj.
    eapply id_nodup_find_self, Forall_forall in Hnodup; eauto.
    now rewrite <- Et, -> Hnodup, <- E2.
  Qed.

  Corollary id_nodup_find_sublist' [trs1 trs2] 
    (Hsub : list.sublist (map tr_rootinfo trs1) (map tr_rootinfo trs2))
    (Hnodup : trs_roots_NoDupId trs2)
    [sub] (E : In sub trs1) :
    base.fmap tr_rootinfo (trs_find_node (tr_rootid sub) trs2) = Some (tr_rootinfo sub).
  Proof.
    erewrite id_nodup_find_sublist; try eassumption.
    1: reflexivity.
    erewrite id_nodup_find_self_fmap; eauto.
    1: eapply id_nodup_rootinfo_sublist_preserve; eauto.
    now rewrite map_id_eq.
  Qed.

  Corollary id_nodup_find_prefix [tr1 tr2] (Hprefix : prefixtr tr1 tr2)
    (Hnodup : tr_NoDupId tr2)
    [t res] (E : base.fmap tr_rootinfo (tr_getnode t tr1) = Some res) :
    base.fmap tr_rootinfo (tr_getnode t tr2) = Some res.
  Proof. eapply id_nodup_find_sublist. 1: apply prefixtr_flatten_sublist, Hprefix. all: auto. Qed.

  Corollary id_nodup_find_prefix' [tr1 tr2] (Hprefix : prefixtr tr1 tr2)
    (Hnodup : tr_NoDupId tr2) [sub] (E : subtr sub tr1) :
    base.fmap tr_rootinfo (tr_getnode (tr_rootid sub) tr2) = Some (tr_rootinfo sub).
  Proof. eapply id_nodup_find_sublist'. 1: apply prefixtr_flatten_sublist, Hprefix. all: auto. Qed.

End Tree_Find.

Section Tree_Locate_Update.

(* TODO *)

End Tree_Locate_Update.

Section Reversed_Preorder_Traversal_Theory.

(* TODO *)

End Reversed_Preorder_Traversal_Theory.

End RoseTree.

Global Arguments tree : clear implicits.

(* need some tweak, otherwise will need to put @ before when doing induction, or
    face the "Not the right number of induction arguments" error *)
Global Arguments prefixtr_ind_2 [_].
