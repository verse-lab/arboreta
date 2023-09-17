From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses Permutation.
From Coq Require ssreflect.
From distributedclocks.utils Require Export util libtac.
Import ssreflect.SsrSyntax.

From stdpp Require list.

Class EqDec (A : Type) := {
  eqdec : forall (x y : A), {x = y} + {x <> y}
}.

Section RoseTree.

Set Implicit Arguments.

Variable A : Type.

(* A rosetree is a node with some information of type A, and some rosetrees as children. *)

Inductive rosetree : Type := Node (ni : A) (chn : list rosetree).

Definition tr_rootinfo tr := let: Node ni _ := tr in ni.

Definition tr_rootchn tr := let: Node _ chn := tr in chn.

Section Tree_Height.

  Fixpoint tr_height tr : nat := S (List.list_max (map tr_height (tr_rootchn tr))).

  Fact tr_height_le n chn ch (Hin : In ch chn) (Hle : List.list_max (map tr_height chn) <= n) :
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

  Lemma tr_ind_bounded_height (P : rosetree -> Prop)
    (Hind : forall (ni : A) (chn : list rosetree), Forall P chn -> P (Node ni chn)) n : 
    forall (tr : rosetree) (Hh : tr_height tr <= n), P tr.
  Proof.
    induction n as [ | n IH ] using nat_ind_2; intros.
    all: destruct tr as (ni & chn); simpl in Hh.
    - lia.
    - apply le_S_n, list_max_le, Forall_map in Hh. 
      apply Hind, List.Forall_impl with (P:=fun x => tr_height x <= n).
      2: assumption.
      intros.
      apply IH with (m:=n).
      + lia.
      + assumption.
  Qed.

  Lemma tr_ind_2 (P : rosetree -> Prop)
    (Hind : forall (ni : A) (chn : list rosetree), Forall P chn -> P (Node ni chn)) : 
    forall (tr : rosetree), P tr.
  Proof.
    intros tr.
    apply tr_ind_bounded_height with (n:=tr_height tr). 
    - assumption.
    - lia.
  Qed.

End Tree_Height.

Section Tree_Equality.

  Context `{A_eqdec : EqDec A}.

  Fixpoint tr_eqb tr tr' :=
    let: Node ni chn := tr in
    let: Node ni' chn' := tr' in
    if eqdec ni ni'
    then 
      (if Nat.eq_dec (length chn) (length chn')
        then 
          List.forallb (fun pp => (fst pp) (snd pp))
            (List.combine (map tr_eqb chn) chn')
        else false)
    else false.

  Lemma tr_eqP tr : forall tr', tr_eqb tr tr' <-> tr = tr'.
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros [ni' chn'].
    simpl.
    destruct (eqdec ni ni') as [ <- | Hnineq ], (Nat.eq_dec (length chn) (length chn')) as [ El | Hlneq ].
    all: try eqsolve.
    unfold is_true.
    rewrite -> forallb_forall, <- Forall_forall.
    revert chn' El.
    induction chn as [ | ch chn IH' ]; intros.
    - destruct chn'; try discriminate.
      intuition constructor.
    - destruct chn' as [ | ch' chn' ]; try discriminate.
      simpl in El.
      injection El as El.
      simpl.
      rewrite -> Forall_cons_iff in IH |- *.
      simpl.
      specialize (IH' (proj2 IH) _ El).
      rewrite -> (proj1 IH ch'), IH'.
      intuition congruence.
  Qed.

  Definition tr_eqdec (tr tr' : rosetree) : {tr = tr'} + {tr <> tr'}.
  Proof.
    destruct (tr_eqb tr tr') eqn:E.
    - apply tr_eqP in E.
      now left.
    - right.
      intros EE.
      apply tr_eqP in EE.
      intuition congruence.
  Qed.

End Tree_Equality.

Section Core_Auxiliary_Functions.

  (* flat_map f l = concat (map f l) *)
  Fixpoint tr_flatten tr :=
    let: Node ni chn := tr in tr :: (List.flat_map tr_flatten chn).

  Fact tr_flatten_self_in tr : In tr (tr_flatten tr).
  Proof. destruct tr as [? ?]. simpl. now left. Qed.

  Fact tr_flatten_direct_result tr : tr_flatten tr = tr :: (flat_map tr_flatten (tr_rootchn tr)).
  Proof. now destruct tr as [? ?]. Qed.

  Fact tr_flatten_root_chn_split trs :
    Permutation (flat_map tr_flatten trs) (trs ++ (flat_map tr_flatten (flat_map tr_rootchn trs))).
  Proof.
    induction trs as [ | [ni chn] trs IH ].
    1: constructor.
    simpl.
    constructor.
    rewrite -> flat_map_app.
    etransitivity.
    2: apply Permutation_app_swap_app.
    now apply Permutation_app_head.
  Qed.

  (* One can prove that a tree is not a subtree of any of the subtree of its children by comparing height. *)

  Fact tr_height_else_lt tr :
    Forall (fun tr' => tr_height tr' < tr_height tr) (flat_map tr_flatten (tr_rootchn tr)).
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    rewrite -> List.Forall_forall in IH |- *.
    simpl.
    setoid_rewrite -> in_flat_map.
    intros sub ([ni_ch chn_ch] & Hin_ch & Hin).
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

  Fact self_not_in_tr_flatten_chn ni chn : ~ In (Node ni chn) (flat_map tr_flatten chn).
  Proof.
    pose proof (tr_height_else_lt (Node ni chn)) as Hlt.
    simpl in Hlt.
    rewrite -> List.Forall_forall in Hlt.
    intros Hin.
    apply Hlt in Hin.
    simpl in Hin.
    lia.
  Qed.

  Fixpoint tr_locate (tr : rosetree) (pos : list nat) : option rosetree :=
    match pos with
    | nil => Some tr
    | x :: pos' => 
      match nth_error (tr_rootchn tr) x with
      | Some ch => tr_locate ch pos'
      | None => None
      end
    end.

  Fact tr_locate_pos_app pos1 : forall tr pos2 sub (H : tr_locate tr pos1 = Some sub),
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

End Core_Auxiliary_Functions.

Section Tree_Size.

  Definition tr_size tr := length (tr_flatten tr).

  Global Arguments tr_size ! _ /.

  Fact tr_size_chn_lt_full tr : length (tr_rootchn tr) < tr_size tr.
  Proof.
    destruct tr; simpl.
    erewrite -> Permutation_length with (l:=(flat_map tr_flatten chn)).
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

  Fact tr_size_ch_lt_full ch tr (H : In ch (tr_rootchn tr)) : 
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

  Fact tr_size_subtr_le_full tr : forall sub (H : In sub (tr_flatten tr)), 
    tr_size sub <= tr_size tr.
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros; simpl in H |- *.
    destruct H as [ <- | (ch & Hin_ch & H)%in_flat_map ]; simpl.
    1: apply le_n.
    transitivity (tr_size ch).
    2: pose proof (tr_size_ch_lt_full ch (Node ni chn) Hin_ch) as Htmp; simpl in Htmp; lia.
    rewrite Forall_forall in IH.
    now specialize (IH _ Hin_ch _ H).
  Qed.

End Tree_Size.

Section Subtree_Theory.

  (* tr1 is a subtree of tr2 *)
  Definition subtr tr1 tr2 : Prop := In tr1 (tr_flatten tr2).

  Global Arguments subtr _ _/.

  Fact subtr_chn tr ch : In ch (tr_rootchn tr) -> subtr ch tr.
  Proof.
    intros H.
    hnf.
    rewrite tr_flatten_direct_result.
    right.
    apply in_flat_map.
    exists ch.
    split; [ assumption | apply tr_flatten_self_in ].
  Qed.

  Lemma subtr_trans tr tr' tr'' : subtr tr'' tr' -> subtr tr' tr -> subtr tr'' tr.
  Proof.
    revert tr'' tr'.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    simpl in H, H0. 
    destruct H0 as [ <- | H0 ]; auto.
    rewrite -> in_flat_map in H0.
    destruct H0 as (ch & Hin_ch & H0).
    rewrite -> Forall_forall in IH. 
    specialize (IH _ Hin_ch _ _ H H0).
    hnf. right. apply in_flat_map. now exists ch.
  Qed.

  Corollary subtr_flatten_incl tr tr' (H : subtr tr tr') : incl (tr_flatten tr) (tr_flatten tr').
  Proof. hnf. intros sub' H'. revert H' H. apply subtr_trans. Qed.

  (* proof-relevant witness of subtree *)
  Definition subtr_witness (l : list nat) sub tr := tr_locate tr l = Some sub.

  Lemma subtr_witness_subtr l :
    forall sub tr, subtr_witness l sub tr -> subtr sub tr.
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

  Lemma subtr_subtr_witness tr :
    forall sub, subtr sub tr -> exists l, subtr_witness l sub tr.
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    hnf in H. 
    destruct H as [ <- | ].
    - now exists nil.
    - apply in_flat_map in H.
      destruct H as (ch & Hin_ch & Hin).
      rewrite -> Forall_forall in IH. 
      specialize (IH _ Hin_ch).
      apply IH in Hin. 
      destruct Hin as (l & H).
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

End Subtree_Theory.

Section Forall_Tree_Theory.

  Inductive Foralltr (P : rosetree -> Prop) : rosetree -> Prop :=
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

  Fact Foralltr_self P tr (H : Foralltr P tr) : P tr.
  Proof. destruct tr. now apply Foralltr_cons_iff in H. Qed.

  Fact Foralltr_chn P tr (H : Foralltr P tr) : Forall (Foralltr P) (tr_rootchn tr).
  Proof. destruct tr. now apply Foralltr_cons_iff in H. Qed.

  Fact Foralltr_chn_selves P tr (H : Foralltr P tr) : Forall P (tr_rootchn tr).
  Proof. eapply List.Forall_impl. 1: apply Foralltr_self. now apply Foralltr_chn. Qed.

  Lemma Foralltr_Forall_subtree (P : rosetree -> Prop) tr :
    Foralltr P tr <-> Forall P (tr_flatten tr).
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    simpl.
    rewrite -> ! Foralltr_cons_iff, List.Forall_cons_iff, -> ! List.Forall_forall.
    setoid_rewrite in_flat_map.
    rewrite -> List.Forall_forall in IH.
    setoid_rewrite -> List.Forall_forall in IH.
    firstorder. 
    apply IH; firstorder. 
  Qed.

  Corollary Foralltr_trivial (P : rosetree -> Prop) (H : forall tr, P tr) tr : Foralltr P tr.
  Proof. now apply Foralltr_Forall_subtree, List.Forall_forall. Qed.

  Lemma Foralltr_impl_pre (P Q : rosetree -> Prop) tr 
    (Hf : Foralltr (fun tr' => P tr' -> Q tr') tr) (H : Foralltr P tr) : Foralltr Q tr.
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    rewrite -> Foralltr_cons_iff in Hf, H |- *.
    destruct H as (H & H0), Hf as (Hf & Hf0).
    rewrite -> Forall_forall in *. 
    split; try firstorder.
  Qed.

  Corollary Foralltr_impl (P Q : rosetree -> Prop) (Hpq : forall tr, P tr -> Q tr) tr 
    (H : Foralltr P tr) : Foralltr Q tr.
  Proof. eapply Foralltr_impl_pre. 2: apply H. now apply Foralltr_trivial. Qed.

  Lemma Foralltr_Forall_chn_comm P tr : 
    Foralltr (fun tr' => Forall P (tr_rootchn tr')) tr <-> Forall (Foralltr P) (tr_rootchn tr).
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    rewrite -> Foralltr_cons_iff at 1. simpl.
    rewrite <- list.Forall_and. 
    repeat rewrite -> List.Forall_forall in *.
    setoid_rewrite -> Foralltr_cons_iff' at 2.
    firstorder.
  Qed.

  Lemma Foralltr_and (P Q : rosetree -> Prop) tr :
    Foralltr (fun tr => P tr /\ Q tr) tr <-> Foralltr P tr /\ Foralltr Q tr.
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    rewrite -> ! Foralltr_cons_iff, -> ! List.Forall_forall.
    rewrite -> List.Forall_forall in IH.
    firstorder.
  Qed.

  Lemma Foralltr_idempotent (P : rosetree -> Prop) tr :
    Foralltr (Foralltr P) tr <-> Foralltr P tr.
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    rewrite -> ! Foralltr_cons_iff, -> ! List.Forall_forall.
    rewrite -> List.Forall_forall in IH.
    firstorder.
  Qed.

  Corollary Foralltr_Foralltr_subtree (P : rosetree -> Prop) tr :
    Foralltr P tr <-> Forall (Foralltr P) (tr_flatten tr).
  Proof. now rewrite <- Foralltr_idempotent, -> Foralltr_Forall_subtree. Qed.

  Fact Foralltr_subtr P tr sub (Hsub : subtr sub tr) (H : Foralltr P tr) : P sub.
  Proof. rewrite -> Foralltr_Forall_subtree, -> Forall_forall in H. auto. Qed. 

End Forall_Tree_Theory.

Section Tree_Prefix_Theory.

  Inductive prefixtr : rosetree -> rosetree -> Prop :=
    prefixtr_intro : forall ni chn chn_sub prefix_chn, 
      list.sublist chn_sub chn ->
      Forall2 prefixtr prefix_chn chn_sub ->
      prefixtr (Node ni prefix_chn) (Node ni chn).

  Fact prefixtr_inv ni1 ni2 chn1 chn2 (Hprefix: prefixtr (Node ni1 chn1) (Node ni2 chn2)) :
    ni1 = ni2 /\ exists chn2_sub, list.sublist chn2_sub chn2 /\ Forall2 prefixtr chn1 chn2_sub.
  Proof. inversion Hprefix; subst. firstorder. Qed.

  Lemma prefixtr_ind_2 (P : rosetree -> rosetree -> Prop)
    (Hind : forall (ni : A) (chn1 chn2_sub chn2 : list rosetree), 
      list.sublist chn2_sub chn2 ->
      Forall2 prefixtr chn1 chn2_sub -> 
      Forall2 P chn1 chn2_sub -> P (Node ni chn1) (Node ni chn2)) : 
    forall (tr1 tr2 : rosetree), prefixtr tr1 tr2 -> P tr1 tr2.
  Proof.
    intros.
    revert tr2 H.
    induction tr1 as [ni chn1 IH] using tr_ind_2; intros.
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

  Fact prefixtr_rootinfo_same tr tr' (Hprefix : prefixtr tr tr') :
    tr_rootinfo tr = tr_rootinfo tr'.
  Proof. 
    destruct tr, tr'.
    apply prefixtr_inv in Hprefix.
    intuition congruence.
  Qed.

  #[export] Instance prefixtr_refl : Reflexive prefixtr.
  Proof.
    hnf.
    intros tr.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    econstructor.
    1: reflexivity.
    now apply list.Forall_Forall2_diag.
  Qed.

  Fact prefixtr_nil_l ni chn : prefixtr (Node ni nil) (Node ni chn).
  Proof.
    econstructor.
    2: reflexivity.
    apply list.sublist_nil_l.
  Qed.

  Lemma prefixtr_flatten_sublist tr1 tr2 (Hprefix : prefixtr tr1 tr2) :
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

  Corollary prefixtr_size_le tr1 tr2 (Hprefix : prefixtr tr1 tr2) :
    length (tr_flatten tr1) <= length (tr_flatten tr2).
  Proof. rewrite <- ! map_length with (f:=tr_rootinfo). now apply list.sublist_length, prefixtr_flatten_sublist. Qed.

  Corollary prefixtr_flatten_info_incl tr1 tr2 (Hprefix : prefixtr tr1 tr2) :
    incl (map tr_rootinfo (tr_flatten tr1)) (map tr_rootinfo (tr_flatten tr2)).
  Proof.
    intros ni Hin.
    eapply sublist_In.
    1: eapply prefixtr_flatten_sublist; eauto.
    assumption.
  Qed.

  Lemma prefixtr_size_eq_tr_eq tr1 tr2 (Hprefix : prefixtr tr1 tr2) 
    (H : length (tr_flatten tr1) = length (tr_flatten tr2)) : tr1 = tr2.
  Proof.
    induction Hprefix as [ni chn1 chn2_sub chn2 Hsub Hprefix IH] using prefixtr_ind_2.
    simpl in H.
    injection H as H.
    f_equal; clear ni.
    pose proof Hprefix as Hple.
    eapply list.Forall2_impl in Hple.
    2: apply prefixtr_size_le.
    assert (length (flat_map tr_flatten chn1) <= length (flat_map tr_flatten chn2_sub)) as H1.
    {
      rewrite -> ! flat_map_concat_map.
      eapply length_concat_le, list.Forall2_fmap_2.
      assumption.
    }
    pose proof (length_concat_sum (map tr_flatten chn2_sub)) as E'.
    pose proof (length_concat_sum (map tr_flatten chn2)) as E.
    rewrite <- ! flat_map_concat_map in E, E'.
    pose proof Hsub as H2.
    apply sublist_map with (f:=fun t => length (tr_flatten t)), sublist_sum_le in H2.
    assert (chn2_sub = chn2) as ->.
    {
      apply sublist_map_sum_eq_ with (f:=fun t => length (tr_flatten t)); auto.
      - intros [? ?]; simpl; lia.
      - rewrite -> map_map in E, E'; lia.
    }
    clear -H Hprefix Hple IH.
    induction Hprefix as [ | ch1 ch2 chn1 chn2 Hp Hprefix ]; try reflexivity.
    simpl in H.
    rewrite -> ! app_length in H.
    rewrite -> list.Forall2_cons in IH, Hple.
    destruct Hple as (Hp1 & Hp2).
    assert (length (flat_map tr_flatten chn1) <= length (flat_map tr_flatten chn2)) as H1.
    {
      rewrite -> ! flat_map_concat_map.
      eapply length_concat_le, list.Forall2_fmap_2.
      assumption.
    }
    destruct (Nat.leb (length (tr_flatten ch2)) (length (tr_flatten ch1))) eqn:E.
    - apply Nat.leb_le in E.
      f_equal.
      + apply IH.
        lia.
      + apply IHHprefix; intuition; lia.
    - apply Nat.leb_gt in E.
      lia.
  Qed.

  Global Arguments prefixtr_rootinfo_same [_ _] _.
  Global Arguments prefixtr_flatten_sublist [_ _] _.
  Global Arguments prefixtr_size_le [_ _] _.
  Global Arguments prefixtr_flatten_info_incl [_ _] _.
  Global Arguments prefixtr_size_eq_tr_eq [_ _] _.

End Tree_Prefix_Theory.

(* Now we start to consider trees with (decidable) indices. *)

Variables (B : Type) (info_id : A -> B).

Definition tr_rootid tr := info_id (tr_rootinfo tr).

Global Arguments tr_rootid !_ /.

Fact tr_rootinfo_id_inj : forall x y, tr_rootinfo x = tr_rootinfo y -> tr_rootid x = tr_rootid y.
Proof. intros [ni ?] [ni' ?]. unfold tr_rootid. now intros ->. Qed.

Global Arguments tr_rootinfo_id_inj [_ _] _.

Section NoDup_Indices_Theory.

  Lemma id_nodup_trs_each trs
    (H : List.NoDup (map tr_rootid (flat_map tr_flatten trs)))
    tr (Hin : In tr trs) : List.NoDup (map tr_rootid (tr_flatten tr)).
  Proof.
    rewrite -> flat_map_concat_map, -> concat_map, -> map_map in H.
    apply NoDup_concat in H.
    rewrite -> List.Forall_map, List.Forall_forall in H.
    now apply H.
  Qed.

  Lemma id_nodup_Foralltr_id tr : 
    List.NoDup (map tr_rootid (tr_flatten tr)) <->
    Foralltr (fun tr' => List.NoDup (map tr_rootid (tr_flatten tr'))) tr.
  Proof.
    induction tr as [ni chn IH] using tr_ind_2; intros.
    simpl.
    rewrite -> Foralltr_cons_iff.
    simpl.
    split; [ | intuition ].
    intros H.
    split; [ assumption | ].
    rewrite -> List.Forall_forall in IH |- *.
    intros tr Hin.
    rewrite <- IH.
    2: assumption.
    apply NoDup_cons_iff in H.
    destruct H as (_ & H).
    now eapply id_nodup_trs_each; eauto.
  Qed.

  Corollary id_nodup_subtr sub tr (H : subtr sub tr) 
    (Hnodup : List.NoDup (map tr_rootid (tr_flatten tr))) :
    List.NoDup (map tr_rootid (tr_flatten sub)).
  Proof. rewrite -> id_nodup_Foralltr_id in Hnodup; eapply Foralltr_subtr in H; [ | apply Hnodup ]; auto. Qed. 

  Lemma id_nodup_prefix_preserve tr tr' (Hprefix : prefixtr tr tr') 
    (Hnodup : List.NoDup (map tr_rootid (tr_flatten tr'))) : 
    List.NoDup (map tr_rootid (tr_flatten tr)).
  Proof.
    pose proof (prefixtr_flatten_sublist Hprefix) as Hdomsub.
    apply sublist_map with (f:=info_id) in Hdomsub.
    simpl in Hdomsub.
    rewrite -> ! map_map in Hdomsub.
    fold tr_rootid in Hdomsub.
    eapply sublist_NoDup; eauto.
  Qed.

  Lemma id_nodup_root_chn_split trs
    (Hnodup : List.NoDup (map tr_rootid (flat_map tr_flatten trs))) : 
    List.NoDup (map tr_rootid trs) /\ List.NoDup (map tr_rootid (flat_map tr_flatten (flat_map tr_rootchn trs))).
  Proof.
    pose proof (tr_flatten_root_chn_split trs) as Hperm.
    apply Permutation_map with (f:=tr_rootid) in Hperm.
    rewrite -> map_app in Hperm.
    apply Permutation_NoDup in Hperm.
    2: assumption.
    now apply NoDup_app_ in Hperm.
  Qed.

  Global Arguments id_nodup_subtr [_ _] _ _.
  Global Arguments id_nodup_prefix_preserve [_ _] _ _.

End NoDup_Indices_Theory.

Section Tree_Find.

  Context `{B_eqdec : EqDec B}.

  Definition has_same_id t tr := is_left (eqdec (tr_rootid tr) t).

  Global Arguments has_same_id _ !_ /.

  Fact has_same_id_refl tr : has_same_id (tr_rootid tr) tr = true.
  Proof. unfold has_same_id. destruct (eqdec (tr_rootid tr) (tr_rootid tr)) as [ <- | ]; auto; try contradiction. Qed.

  Fact has_same_id_true t tr : has_same_id t tr = true <-> t = tr_rootid tr.
  Proof. unfold has_same_id. destruct (eqdec (tr_rootid tr) t) as [ <- | ]; simpl; intuition congruence. Qed.

  Fact has_same_id_false t tr : has_same_id t tr = false <-> t <> tr_rootid tr.
  Proof. unfold has_same_id. destruct (eqdec (tr_rootid tr) t) as [ <- | ]; simpl; intuition congruence. Qed.

  Fact tr_rootinfo_has_same_id_congr : forall x y, tr_rootinfo x = tr_rootinfo y -> 
    forall t, has_same_id t x = has_same_id t y.
  Proof. intros. unfold has_same_id. now rewrite tr_rootinfo_id_inj with (x:=x) (y:=y). Qed.

  Definition tr_getnode t tr := find (has_same_id t) (tr_flatten tr).

  Global Arguments tr_getnode _ !_ /.

  Fact tr_getnode_self tr : tr_getnode (tr_rootid tr) tr = Some tr.
  Proof.
    destruct tr as [ni ?].
    simpl.
    now destruct (eqdec _ _).
  Qed.

  Fact trs_find_has_id t trs res
    (Hres : find (has_same_id t) trs = Some res) : In res trs /\ tr_rootid res = t.
  Proof. 
    apply find_some in Hres.
    now rewrite -> has_same_id_true in Hres.
  Qed.

  Fact trs_find_in_iff t trs : 
    In t (map tr_rootid trs) <-> find (has_same_id t) trs.
  Proof.
    rewrite -> in_map_iff.
    split.
    - intros (sub & <- & Hin).
      destruct (find (has_same_id (tr_rootid sub)) trs) eqn:E.
      1: auto.
      eapply find_none in E.
      2: apply Hin.
      now rewrite -> has_same_id_false in E.
    - destruct (find (has_same_id t) trs) as [ res | ] eqn:E.
      2: intros; discriminate.
      intros _.
      apply trs_find_has_id in E.
      destruct E.
      eauto.
  Qed.

  Fact tr_getnode_in_iff t tr : 
    In t (map tr_rootid (tr_flatten tr)) <-> tr_getnode t tr.
  Proof. apply trs_find_in_iff. Qed.

  Fact tr_getnode_res_Foralltr t tr res (P : rosetree -> Prop)
    (Hp : Foralltr P tr) (Hres : tr_getnode t tr = Some res) : 
    P res /\ tr_rootid res = t.
  Proof.
    apply find_some in Hres.
    rewrite -> has_same_id_true in Hres.
    destruct Hres as (Hin & ->).
    rewrite -> Foralltr_Forall_subtree, -> Forall_forall in Hp.
    firstorder. 
  Qed.

  Lemma id_nodup_find_self trs (Hnodup : List.NoDup (map tr_rootid trs)) :
    Forall (fun tr => find (has_same_id (tr_rootid tr)) trs = Some tr) trs.
  Proof.
    induction trs as [ | tr trs IH ].
    1: constructor.
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

  (* fully parameterized *)
  Corollary id_nodup_find_self' [C D : Type] (f : D -> C) (g : rosetree -> D) (h : D -> B)
    (Hh : forall tr, h (g tr) = tr_rootid tr)
    trs (Hnodup : List.NoDup (map tr_rootid trs)) 
    el (Hin : In el (map g trs)) :
    base.fmap (fun tr0 => f (g tr0)) (find (has_same_id (h el)) trs) = Some (f el).
  Proof.
    apply in_map_iff in Hin.
    destruct Hin as (sub & <- & Hin_sub).
    pose proof (id_nodup_find_self trs Hnodup) as H.
    rewrite -> List.Forall_forall in H.
    specialize (H _ Hin_sub).
    now rewrite -> Hh, -> H.
  Qed.

  Corollary id_nodup_find_self_subtr [C : Type] (f : rosetree -> C) tr (Hnodup : List.NoDup (map tr_rootid (tr_flatten tr))) 
    sub (Hin_sub : In sub (tr_flatten tr)) :
    base.fmap f (tr_getnode (tr_rootid sub) tr) = Some (f sub).
  Proof.
    eapply id_nodup_find_self' in Hnodup.
    3: rewrite map_id_eq; apply Hin_sub.
    2: reflexivity.
    apply Hnodup.
  Qed.

  (* FIXME: still need a counterpart of "tc_getclk_perm_congr_pre" *)

  Global Arguments trs_find_has_id [_ _ _] _.
  Global Arguments tr_getnode_res_Foralltr [_ _ _ _] _.

End Tree_Find.

Section Tree_Locate_Update.

(* TODO *)

End Tree_Locate_Update.

Section Reversed_Preorder_Traversal_Theory.

(* TODO *)

End Reversed_Preorder_Traversal_Theory.

Unset Implicit Arguments. (* ? *)

End RoseTree.
