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

Local Notation isSome := ssrbool.isSome.

Context {A : Type}.

(* A rosetree is a node with some information of type A, and some rosetrees as children. *)

Inductive tree : Type := Node (a : A) (chn : list tree).

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
    (Hind : forall (a : A) (chn : list tree), Forall P chn -> P (Node a chn)) n : 
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
    (Hind : forall (a : A) (chn : list tree), Forall P chn -> P (Node a chn)) : 
    forall (tr : tree), P tr.
  Proof.
    intros tr.
    apply tr_ind_bounded_height with (n:=tr_height tr). 
    - assumption.
    - constructor.
  Qed.

  (* sometimes can avoid the pervasive usage of Forall_forall *)
  Corollary tree_ind_2' (P : tree -> Prop)
    (Hind : forall (a : A) (chn : list tree), (forall ch, In ch chn -> P ch) -> P (Node a chn)) : 
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

  Fact tr_locate_pos_app tr pos1 pos2 :
    tr_locate tr (pos1 ++ pos2) = base.mbind (fun tr' => tr_locate tr' pos2) (tr_locate tr pos1).
  Proof.
    revert tr pos2.
    induction pos1 as [ | x pos1 IH ]; intros [a chn]; intros; simpl; try reflexivity.
    destruct (nth_error chn x) eqn:E; try reflexivity.
    now rewrite IH.
  Qed.

  Corollary tr_locate_pos_app' [tr pos1 sub] (H : tr_locate tr pos1 = Some sub) pos2 :
    tr_locate tr (pos1 ++ pos2) = tr_locate sub pos2.
  Proof. now rewrite tr_locate_pos_app, H. Qed.

  Corollary tr_locate_parent [tr pos ch] (H : tr_locate tr pos = Some ch) (Hnotnil : pos <> nil) :
    exists par, tr_locate tr (removelast pos) = Some par /\ In ch (tr_rootchn par).
  Proof.
    destruct (list_rev_destruct pos) as [ -> | (pos' & x & ->) ]; try contradiction.
    rewrite tr_locate_pos_app in H.
    simpl in H.
    rewrite removelast_last.
    destruct (tr_locate tr pos') as [ par | ]; try discriminate.
    simpl in H.
    destruct (nth_error _ _) eqn:E in H; try discriminate.
    injection H as ->.
    exists par.
    split; [ reflexivity | eapply nth_error_In; eauto ].
  Qed.

  Fixpoint tr_pos_valid_depth (tr : tree) (pos : list nat) : nat :=
    match pos with
    | nil => 0
    | x :: pos' => 
      match nth_error (tr_rootchn tr) x with
      | Some ch => S (tr_pos_valid_depth ch pos')
      | None => 0
      end
    end.

  Definition tr_pos_valid_part tr pos := firstn (tr_pos_valid_depth tr pos) pos.
  Global Arguments tr_pos_valid_part _ !_ /.

  Fact tr_pos_valid_depth_le tr pos : tr_pos_valid_depth tr pos <= length pos.
  Proof.
    revert tr.
    induction pos as [ | x pos IH ]; intros [ni chn]; simpl.
    - constructor.
    - destruct (nth_error chn x) as [ ch | ] eqn:E.
      + apply le_n_S, IH.
      + apply Nat.le_0_l.
  Qed.

  Fact tr_pos_valid_depth_maximal tr pos :
    exists chn, base.fmap tr_rootchn (tr_locate tr (tr_pos_valid_part tr pos)) = Some chn /\
      (tr_pos_valid_depth tr pos < length pos ->
        length chn <= nth (tr_pos_valid_depth tr pos) pos 0).
  Proof.
    revert tr.
    induction pos as [ | x pos IH ]; intros [ni chn]; simpl.
    - exists chn.
      split; [ reflexivity | intros H; inversion H ].
    - destruct (nth_error chn x) as [ ch | ] eqn:E.
      + simpl; rewrite E.
        specialize (IH ch).
        destruct IH as (chn' & E' & H).
        exists chn'.
        split; [ assumption | intros HH%le_S_n; now apply H ].
      + simpl.
        exists chn.
        split; [ reflexivity | intros _; now apply nth_error_None ].
  Qed.

  Corollary tr_pos_valid_depth_valid tr pos :
    isSome (tr_locate tr (tr_pos_valid_part tr pos)) = true.
  Proof. destruct (tr_pos_valid_depth_maximal tr pos) as (? & E & _). now destruct (tr_locate _ _). Qed.

  Fact tr_pos_valid_depth_lt tr pos : 
    tr_locate tr pos = None <-> tr_pos_valid_depth tr pos < length pos.
  Proof.
    revert tr.
    induction pos as [ | x pos IH ]; intros [ni chn]; simpl.
    - split; intros H; inversion H.
    - destruct (nth_error chn x) as [ ch | ] eqn:E.
      + now rewrite IH, <- Nat.succ_lt_mono.
      + split; intros; auto.
        apply le_n_S, Nat.le_0_l.
  Qed.

  Corollary tr_pos_valid_depth_eq tr pos :
    isSome (tr_locate tr pos) = true <-> tr_pos_valid_depth tr pos = length pos.
  Proof.
    pose proof (tr_pos_valid_depth_le tr pos) as Hle.
    rewrite isSome_true_not_None, tr_pos_valid_depth_lt.
    lia.
  Qed.

  Corollary tr_pos_valid_part_eq tr pos :
    isSome (tr_locate tr pos) = true <-> tr_pos_valid_part tr pos = pos.
  Proof.
    unfold tr_pos_valid_part.
    rewrite tr_pos_valid_depth_eq, <- firstn_all2_iff.
    pose proof (tr_pos_valid_depth_le tr pos) as Hle.
    lia.
  Qed.

  (* FIXME: generalize this property? *)
  Fact tr_pos_valid_part_removelast [tr pos] (H : tr_locate tr pos = None) :
    tr_pos_valid_part tr (removelast pos) = tr_pos_valid_part tr pos.
  Proof.
    revert tr H.
    induction pos as [ | x pos IH ]; intros [ni chn]; simpl.
    - intros; discriminate.
    - unfold tr_pos_valid_part in *.
      destruct (nth_error chn x) as [ ch | ] eqn:E.
      + simpl.
        intros.
        rewrite <- (IH _ H); auto.
        destruct pos; [ discriminate | simpl; now rewrite E ].
      + intros _.
        destruct pos; [ reflexivity | simpl; now rewrite E ].
  Qed.

  Fixpoint tr_locate_upd (tr : tree) (pos : list nat) (sub : tree) : tree :=
    match pos with
    | nil => sub
    | x :: pos' => 
      match nth_error (tr_rootchn tr) x with
      | Some ch => Node (tr_rootinfo tr) (upd_nth x (tr_rootchn tr) (tr_locate_upd ch pos' sub))
      | None => tr
      end
    end.

  Fact tr_locate_upd_pos_app [pos1] : forall [tr res] (H : tr_locate tr pos1 = Some res) pos2 sub,
    tr_locate_upd tr (pos1 ++ pos2) sub = tr_locate_upd tr pos1 (tr_locate_upd res pos2 sub).
  Proof.
    induction pos1 as [ | x pos1 IH ]; intros [ni chn]; intros; simpl in *.
    - congruence.
    - destruct (nth_error chn x) eqn:E; try discriminate.
      erewrite IH; eauto.
  Qed.

  Fact tr_locate_upd_locate_pos_app [pos1] : forall [tr res] (H : tr_locate tr pos1 = Some res) pos2 sub,
    tr_locate (tr_locate_upd tr pos1 sub) (pos1 ++ pos2) = tr_locate sub pos2.
  Proof.
    induction pos1 as [ | x pos1 IH ]; intros [ni chn]; intros; simpl in *.
    - reflexivity.
    - destruct (nth_error chn x) eqn:E; try discriminate.
      simpl.
      (* length trick *)
      pose proof E as (pre & suf & -> & <-)%nth_error_split.
      rewrite upd_nth_exact by reflexivity.
      rewrite nth_error_app2 by apply le_n.
      rewrite Nat.sub_diag.
      simpl.
      eapply IH; eauto.
  Qed.

End Core_Auxiliary_Functions.

Section Structure_Changing_Functions.

  (* some common derived definitions from "tr_locate_upd" *)

  (* this might be defined as a separate recursive functions, but that would incur 
      repetitive proof? *)
  Definition tr_locate_apply tr pos (f : tree -> tree) :=
    match tr_locate tr pos with
    | Some sub => tr_locate_upd tr pos (f sub)
    | None => tr
    end.

  (* this should be used whenever possible, instead of unfolding every time *)
  Fact tr_locate_apply_iota a chn x l f :
    tr_locate_apply (Node a chn) (x :: l) f = 
    Node a (match nth_error chn x with
            | Some ch => upd_nth x chn (tr_locate_apply ch l f)
            | None => chn
            end).
  Proof.
    unfold tr_locate_apply. 
    simpl.
    destruct (nth_error chn x) as [ ch | ] eqn:E; try reflexivity. 
    destruct (tr_locate ch l); [ reflexivity | now rewrite upd_nth_intact ].
  Qed.

  Definition tr_remove_node tr pos :=
    match list.last pos with
    | Some x => tr_locate_apply tr (removelast pos) 
      (fun '(Node a chn) => Node a (firstn x chn ++ skipn (S x) chn))
    | None => tr  (* do not return an empty tree *)
    end.

  Fact tr_remove_node_iota a l y [ch chn x] (E : nth_error chn x = Some ch) :
    tr_remove_node (Node a chn) (x :: l ++ y :: nil) = 
    Node a (upd_nth x chn (tr_remove_node ch (l ++ y :: nil))).
  Proof.
    unfold tr_remove_node.
    simpl.
    now rewrite list.last_cons, list.last_snoc, removelast_last, 
      list_snoc_notnil_match, tr_locate_apply_iota, E.
  Qed.

  Lemma tr_remove_node_dom_partition [tr] :
    forall [l sub] (Hsub : tr_locate tr l = Some sub) (Hnotnil : l <> nil),
    Permutation (map tr_rootinfo (tr_flatten tr))
      (map tr_rootinfo (tr_flatten (tr_remove_node tr l)) ++ map tr_rootinfo (tr_flatten sub)).
  Proof.
    induction tr as [a chn IH] using tree_ind_2'; intros.
    destruct l as [ | x l ]; try contradiction.
    simpl in Hsub.
    destruct (nth_error chn x) as [ res | ] eqn:E; try discriminate.
    pose proof E as (Hle & Elen & Echn & Esuf)%nth_error_mixin.
    destruct (list_rev_destruct l) as [ -> | (l' & y & ->) ].
    - unfold tr_remove_node.
      simpl in Hsub |- *.
      injection Hsub as <-.
      rewrite Echn at 1.
      rewrite ! flat_map_app, ! map_app.
      simpl.
      rewrite map_app.
      list.solve_Permutation.
    - erewrite tr_remove_node_iota; eauto.
      simpl.
      rewrite Echn at 1 2.
      rewrite upd_nth_exact by assumption.
      rewrite ! flat_map_app, ! map_app.
      simpl.
      rewrite map_app, IH; eauto.
      2: eapply nth_error_In; eauto.
      2: now destruct l'.
      rewrite map_app.
      list.solve_Permutation.
  Qed.

  Definition tr_prepend_nodes tr pos new :=
    tr_locate_apply tr pos (fun '(Node a chn) => Node a (new ++ chn)).

  Lemma tr_prepend_nodes_dom_addition [l] :
    forall [tr] (Hsub : isSome (tr_locate tr l) = true) new,
    Permutation (map tr_rootinfo (tr_flatten (tr_prepend_nodes tr l new)))
      (map tr_rootinfo (tr_flatten tr) ++ map tr_rootinfo (flat_map tr_flatten new)).
  Proof.
    unfold tr_prepend_nodes.
    induction l as [ | x l IH ]; intros [a chn]; intros; simpl in Hsub |- *.
    - rewrite flat_map_app, map_app.
      list.solve_Permutation.
    - destruct (nth_error chn x) as [ ch | ] eqn:E; try discriminate.
      rewrite tr_locate_apply_iota, E.
      simpl.
      pose proof E as (Hle & Elen & Echn & Esuf)%nth_error_mixin.
      rewrite Echn, upd_nth_exact by assumption.
      rewrite ! flat_map_app, ! map_app.
      simpl.
      rewrite ! map_app, IH by eauto.
      list.solve_Permutation.
  Qed.

End Structure_Changing_Functions.

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

  #[export] Instance subtr_refl : Reflexive subtr.
  Proof tr_flatten_self_in.

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

  #[export] Instance subtr_trans : Transitive subtr.
  Proof.
    hnf.
    intros tr'' tr' tr.
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
      etransitivity; [ apply H | ].
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
    Foralltr_intro : forall a chn, 
      P (Node a chn) -> Forall (Foralltr P) chn -> Foralltr P (Node a chn). 

  Fact Foralltr_cons_iff P a chn :
    Foralltr P (Node a chn) <-> (P (Node a chn) /\ Forall (Foralltr P) chn).
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

  (* in the future, we may use bit mask to achieve the most precise characterization of prefix? *)

  Inductive prefixtr : tree -> tree -> Prop :=
    prefixtr_intro : forall a chn chn_sub prefix_chn, 
      list.sublist chn_sub chn ->
      Forall2 prefixtr prefix_chn chn_sub ->
      prefixtr (Node a prefix_chn) (Node a chn).

  Fact prefixtr_inv [ni1 ni2 chn1 chn2] (Hprefix: prefixtr (Node ni1 chn1) (Node ni2 chn2)) :
    ni1 = ni2 /\ exists chn2_sub, list.sublist chn2_sub chn2 /\ Forall2 prefixtr chn1 chn2_sub.
  Proof. inversion Hprefix; subst. firstorder. Qed.

  Lemma prefixtr_ind_2 (P : tree -> tree -> Prop)
    (Hind : forall (a : A) (chn1 chn2_sub chn2 : list tree), 
      list.sublist chn2_sub chn2 ->
      Forall2 prefixtr chn1 chn2_sub -> 
      Forall2 P chn1 chn2_sub -> P (Node a chn1) (Node a chn2))
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

  Fact prefixtr_nil_l a chn : prefixtr (Node a nil) (Node a chn).
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

Corollary prefixtr_rootid_same_map [trs trs'] (Hprefix : Forall2 prefixtr trs trs') :
  map tr_rootid trs = map tr_rootid trs'.
Proof. unfold tr_rootid. rewrite <- ! map_map with (g:=info_id) (f:=tr_rootinfo). f_equal. now apply prefixtr_rootinfo_same_map. Qed.

Corollary prefixtr_flatten_id_incl [tr1 tr2] (Hprefix : prefixtr tr1 tr2) :
  incl (map tr_rootid (tr_flatten tr1)) (map tr_rootid (tr_flatten tr2)).
Proof. apply prefixtr_flatten_info_incl, (incl_map info_id) in Hprefix. now rewrite ! map_map in Hprefix. Qed.

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

Fact tr_self_id_in tr : In (tr_rootid tr) (map tr_rootid (tr_flatten tr)).
Proof. rewrite (tree_recons tr) at 2. simpl. now left. Qed.

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

  Lemma id_nodup_tr_chn [tr] (H : tr_NoDupId tr) : trs_NoDupId (tr_rootchn tr).
  Proof. rewrite tree_recons in H. hnf in H |- *. simpl in H. now inversion H. Qed.

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

  Corollary id_nodup_rootid_neq' [tr] (Hnodup : tr_NoDupId tr) :
    ~ In (tr_rootid tr) (map tr_rootid (flat_map tr_flatten (tr_rootchn tr))).
  Proof.
    pose proof (id_nodup_rootid_neq Hnodup) as H.
    rewrite Foralltr_Forall_flat_map_In in H.
    intros (sub & E & Hin)%in_map_iff.
    revert E.
    now apply not_eq_sym, H.
  Qed.

  Lemma id_nodup_diff_by_index [trs] (Hnodup : trs_NoDupId trs)
    [x y chx chy] (Hx : nth_error trs x = Some chx) (Hy : nth_error trs y = Some chy)
    (Hneq : x <> y) : forall t, In t (map tr_rootid (tr_flatten chx)) -> 
      In t (map tr_rootid (tr_flatten chy)) -> False.
  Proof.
    pose proof (two_nth_pick_Permutation Hx Hy Hneq) as (rest & Hperm).
    assert (trs_NoDupId (chx :: chy :: rest)) as Hnodup'
      by (eapply Permutation_NoDup; [ apply Permutation_map, Permutation_flat_map; eassumption | ]; assumption).
    hnf in Hnodup'.
    simpl in Hnodup'.
    rewrite ! map_app, ! NoDup_app_ in Hnodup'.
    setoid_rewrite in_app_iff in Hnodup'.
    apply proj2, proj1 in Hnodup'.
    firstorder.
  Qed.

  Lemma id_nodup_diff_by_pos : forall [tr] (Hnodup : tr_NoDupId tr) [pos1 pos2 sub1 sub2]
    (Hsub1 : tr_locate tr pos1 = Some sub1) (Hsub2 : tr_locate tr pos2 = Some sub2)
    (Hneq : pos1 <> pos2), tr_rootid sub1 <> tr_rootid sub2.
  Proof.
    (* avoid defining a separate pre lemma *)
    enough (forall tr : tree,
      tr_NoDupId tr -> forall pos1 pos2, length pos1 <= length pos2 -> 
      forall sub1 sub2,
      tr_locate tr pos1 = Some sub1 ->
      tr_locate tr pos2 = Some sub2 ->
      pos1 <> pos2 -> tr_rootid sub1 <> tr_rootid sub2) as Hgoal.
    1:{
      intros tr Hnodup pos1 pos2.
      destruct (Compare_dec.le_lt_dec (length pos1) (length pos2)) as [ Hle | Hlt%Nat.lt_le_incl ].
      - eapply Hgoal; eauto.
      - intros.
        apply not_eq_sym.
        eapply Hgoal; eauto.
    }
    intros tr Hnodup pos1 pos2 Hle sub1 sub2 Hsub1 Hsub2 Hneq.
    (* seems like induction is easy here *)
    revert tr Hnodup sub1 Hsub1 pos2 sub2 Hsub2 Hneq Hle.
    induction pos1 as [ | x pos1 IH ]; intros [a chn]; intros.
    - injection Hsub1 as <-.
      destruct pos2 as [ | y pos2 ]; try contradiction.
      simpl in Hsub2.
      destruct (nth_error chn y) as [ ch | ] eqn:E; try discriminate.
      eapply nth_error_In, Forall_forall in E.
      2: apply (id_nodup_rootid_neq (tr:=Node a chn)); try assumption.
      eapply subtr_witness_subtr, Foralltr_subtr in Hsub2; eauto.
      now cbn beta in Hsub2.
    - simpl in Hle.
      destruct pos2 as [ | y pos2 ]; [ inversion Hle | simpl in Hle ].
      apply le_S_n in Hle.
      simpl in Hsub1, Hsub2.
      destruct (nth_error chn x) as [ chx | ] eqn:Ex, 
        (nth_error chn y) as [ chy | ] eqn:Ey; try discriminate.
      destruct (Nat.eq_dec x y) as [ <- | Hneqxy ].
      + rewrite Ex in Ey.
        injection Ey as <-.
        eapply id_nodup_ch in Hnodup.
        2: simpl; eapply nth_error_In; eauto.
        eapply IH; eauto.
        congruence.
      + apply subtr_witness_subtr, (in_map tr_rootid) in Hsub1, Hsub2.
        intros EE.
        rewrite EE in Hsub1.
        revert Hsub1 Hsub2.
        eapply id_nodup_diff_by_index; eauto.
        apply (id_nodup_tr_chn Hnodup).
  Qed.

  Corollary id_nodup_unifypos_by_id [tr] (Hnodup : tr_NoDupId tr) [pos1 pos2 sub1 sub2]
    (Hsub1 : tr_locate tr pos1 = Some sub1) (Hsub2 : tr_locate tr pos2 = Some sub2)
    (E : tr_rootid sub1 = tr_rootid sub2) : pos1 = pos2.
  Proof.
    (* exploit the fact that list nat has decidable equality *)
    destruct (list_eq_dec Nat.eq_dec pos1 pos2) as [ | Hneq ]; auto.
    eapply id_nodup_diff_by_pos in Hneq; eauto.
    contradiction.
  Qed.

  Corollary id_nodup_unify_by_id [tr] (Hnodup : tr_NoDupId tr) [sub1 sub2]
    (Hin1 : subtr sub1 tr) (Hin2 : subtr sub2 tr)
    (E : tr_rootid sub1 = tr_rootid sub2) : sub1 = sub2.
  Proof.
    apply subtr_subtr_witness in Hin1, Hin2.
    destruct Hin1 as (? & H1), Hin2 as (? & H2).
    eapply id_nodup_unifypos_by_id in E; eauto.
    rewrite E in H1.
    hnf in H1, H2.
    rewrite H1 in H2.
    now inversion H2.
  Qed.

End NoDup_Indices_Theory.

(* a by-product *)
Lemma prefixtr_concatenate [tr tr'] (H : prefixtr tr tr')
  (Hnodup : tr_NoDupId tr') :
  forall [l sub'] (Hsub : tr_locate tr l = Some (Node (tr_rootinfo sub') nil))
  (Hsub' : subtr sub' tr'),
  forall sub_prefix' (Hpf : prefixtr sub_prefix' sub'),
    prefixtr (tr_prepend_nodes tr l (tr_rootchn sub_prefix')) tr'.
Proof.
  induction H as [ni chn1 chn2_sub chn2 Hsl H IH] using prefixtr_ind_2; intros.
  destruct l as [ | x l ].
  - injection Hsub as ->.
    subst chn1.
    unfold tr_prepend_nodes, tr_locate_apply.
    simpl.
    rewrite app_nil_r.
    hnf in Hsub'.
    (* unify *)
    destruct Hsub' as [ -> | Hin ].
    1: now rewrite <- (prefixtr_rootinfo_same Hpf), <- tree_recons.
    apply id_nodup_rootid_neq' in Hnodup.
    exfalso.
    apply (in_map tr_rootid) in Hin.
    now apply Hnodup.
  - pose proof (sublist_In Hsl) as Hsubin.
    unfold tr_prepend_nodes.
    rewrite tr_locate_apply_iota.
    simpl in Hsub |- *.
    destruct (nth_error chn1 x) as [ ch | ] eqn:E.
    2: econstructor; eauto.
    econstructor; eauto.
    pose proof E as (_ & Elen & Echn1 & _)%nth_error_mixin.
    pose proof E as Hlt%nth_error_some_inrange.
    rewrite Echn1, upd_nth_exact by assumption.
    eapply Forall2_pointwise in IH; eauto.
    destruct IH as (ch' & E' & HH).
    pose proof E' as (_ & Elen' & Echn2 & Esuf)%nth_error_mixin.
    pose proof E' as Hin%nth_error_In%Hsubin.
    rewrite Echn2, Echn1 in H.
    apply list.Forall2_app_inv in H; try congruence.
    destruct H as (Hq1 & (Hpf' & Hq2)%list.Forall2_cons_1).
    apply list.Forall2_app_l; rewrite Elen; try assumption.
    rewrite Esuf.
    constructor; try assumption.
    eapply HH; eauto.
    + eapply id_nodup_ch; eauto.
      simpl.
      assumption.
    + (* unify two children *)
      apply prefixtr_flatten_id_incl in Hpf'.
      apply subtr_witness_subtr, (in_map tr_rootid), Hpf' in Hsub.
      simpl in Hsub.
      fold (tr_rootid sub') in Hsub.
      pose proof Hsub as (sub'' & Eid & Hsub'')%in_map_iff.
      apply id_nodup_unify_by_id with (sub2:=sub'') in Hsub'; auto.
      2: transitivity ch'; [ assumption | now apply subtr_chn  ].
      subst sub''.
      apply Hsub''.
Qed.

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

  Fact trs_find_in_iff_neg t trs : 
    ~ In t (map tr_rootid trs) <-> trs_find_node t trs = None.
  Proof. rewrite trs_find_in_iff, not_true_iff_false, <- isSome_false_is_None. reflexivity. Qed.

  Fact tr_getnode_in_iff t tr : 
    In t (map tr_rootid (tr_flatten tr)) <-> isSome (tr_getnode t tr) = true.
  Proof. apply trs_find_in_iff. Qed.

  Fact tr_getnode_in_iff_neg t tr : 
    ~ In t (map tr_rootid (tr_flatten tr)) <-> tr_getnode t tr = None.
  Proof. apply trs_find_in_iff_neg. Qed.

  Fact trs_find_some [t trs res] (H : trs_find_node t trs = Some res) :
    In t (map tr_rootid trs).
  Proof. now apply (f_equal (@isSome _)), trs_find_in_iff in H. Qed.

  Fact tr_getnode_some [t tr res] (H : tr_getnode t tr = Some res) :
    In t (map tr_rootid (tr_flatten tr)).
  Proof. now apply trs_find_some in H. Qed.

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

  Fact id_nodup_filter_self [trs] (Hnodup : trs_roots_NoDupId trs) 
    [tr] (Hin : In tr trs) :
    filter (fun tr' => has_same_id (tr_rootid tr') tr) trs = tr :: nil.
  Proof.
    apply in_split in Hin.
    destruct Hin as (pre & suf & ->).
    rewrite filter_app.
    simpl.
    rewrite has_same_id_refl.
    eapply Permutation_NoDup in Hnodup.
    2: rewrite <- Permutation_middle; reflexivity.
    simpl in Hnodup.
    apply NoDup_cons_iff, proj1 in Hnodup.
    setoid_rewrite map_app in Hnodup.
    setoid_rewrite in_app_iff in Hnodup.
    rewrite ! filter_all_false; try reflexivity.
    all: intros ? Hin%(in_map tr_rootid); rewrite has_same_id_false.
    all: intros E; rewrite E in Hin.
    all: intuition.
  Qed.

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

  (* a lemma about rearrangement; using "map Some" and "filter isSome" since we have to skip the "None"s *)

  Lemma trs_find_rearrangement [trs l]
    (Hnodup : trs_roots_NoDupId trs) (Hnodup' : NoDup l) 
    (Hdomincl : incl (map tr_rootid trs) l) :
    Permutation (map Some trs) 
      (filter (@isSome _) (map (fun t => trs_find_node t trs) l)).
  Proof.
    revert l Hnodup' Hdomincl.
    induction trs as [ | tr trs IH ]; intros; simpl.
    - rewrite filter_all_false; auto.
      now intros ? (? & <- & ?)%in_map_iff.
    - hnf in Hnodup, Hdomincl.
      simpl in Hnodup, Hdomincl.
      apply NoDup_cons_iff in Hnodup.
      pose proof (Hdomincl _ (or_introl eq_refl)) as (pre & suf & ->)%in_split.
      rewrite map_app, filter_app.
      simpl.
      rewrite has_same_id_refl; simpl.
      apply Permutation_cons_app.
      erewrite <- filter_app, <- map_app, -> (map_ext_Forall _ _ (l:=pre ++ suf)).
      1: apply IH.
      + tauto.
      + now apply NoDup_remove_1 in Hnodup'.
      + hnf.
        setoid_rewrite in_app_iff in Hdomincl.
        setoid_rewrite in_app_iff.
        simpl in Hdomincl.
        intros b Hin.
        destruct (Hdomincl _ (or_intror Hin)) as [ ? | [ <- | ? ]]; tauto.
      + apply NoDup_remove_2 in Hnodup'.
        apply Forall_forall.
        intros.
        unfold has_same_id.
        rewrite eqdec_must_right; congruence.
  Qed.

  Corollary trs_find_rearrangement_flat_map [trs l] (h : tree -> list tree)
    (Hnodup : trs_roots_NoDupId trs) (Hnodup' : NoDup l) 
    (Hdomincl : incl (map tr_rootid trs) l) :
    Permutation (flat_map h trs)
      (flat_map (fun t => match trs_find_node t trs with
       | Some res => h res
       | None => nil
       end) l).
  Proof.
    pose proof (trs_find_rearrangement Hnodup Hnodup' Hdomincl) as Hperm.
    pose (f:=fun ot : option tree => match ot with Some tr => h tr | None => nil end).
    apply Permutation_flat_map with (g:=f) in Hperm.
    rewrite flat_map_concat_map, map_map, <- flat_map_concat_map in Hperm.
    simpl in Hperm.
    rewrite Hperm.
    subst f.
    clear Hperm Hnodup' Hdomincl.
    induction l as [ | x l IH ]; auto; simpl.
    destruct (trs_find_node x trs) eqn:E; simpl.
    + now rewrite IH.
    + assumption.
  Qed.

End Tree_Find.

Section Reversed_Preorder_Traversal_Theory.

  (* vertical split *)
  (* two modes: full or leaf *)
  Fixpoint tr_vsplitr (full : bool) tr (l : list nat) : tree :=
    match l with
    | nil => Node (tr_rootinfo tr) (if full then tr_rootchn tr else nil)
    | x :: l' =>
      match nth_error (tr_rootchn tr) x with
      | Some ch => Node (tr_rootinfo tr) (tr_vsplitr full ch l' :: skipn (S x) (tr_rootchn tr))
      | None => Node (tr_rootinfo tr) nil
      end
    end.

  (* compute both the positions and thread ids at the same time *)
  (* FIXME: the stack has its entry/exit point at the tail position, which brings some trouble. any way to fix it? *)
  Fixpoint tr_trav_waitlist tr (l : list nat) : (list (list nat)) * (list tree) :=
    match l with
    | nil => (nil, nil)
    | x :: l' =>
      match nth_error (tr_rootchn tr) x with
      | Some ch => 
        let (res1, res2) := (tr_trav_waitlist ch l') in
        ((map (fun i => i :: nil) (seq 0 x)) ++ (map (fun l0 => x :: l0) res1), (firstn x (tr_rootchn tr)) ++ res2)
      | None => 
        ((map (fun i => i :: nil) (seq 0 (length (tr_rootchn tr)))), (tr_rootchn tr))
      end
    end.

  Definition pos_succ (l : list nat) :=
    match rev l with
    | nil => nil
    | x :: l' => rev ((S x) :: l')
    end.

  Definition post_iter_visited_prefix tr pos : tree :=
    tr_vsplitr false tr pos.

  Definition pre_iter_visited_prefix tr pos : tree :=
    tr_vsplitr (isSome (tr_locate tr (pos_succ pos))) tr (pos_succ pos).

  Fact pos_succ_nil : pos_succ nil = nil. Proof eq_refl. 

  Fact pos_succ_last l x : 
    pos_succ (l ++ x :: nil) = l ++ (S x) :: nil.
  Proof. unfold pos_succ. rewrite ! rev_app_distr. simpl. now rewrite rev_involutive. Qed.

  Fact pos_succ_cons x y l : 
    pos_succ (x :: y :: l) = x :: pos_succ (y :: l).
  Proof. 
    assert (y :: l <> nil) as (l' & y' & E)%exists_last by auto.
    rewrite -> ! E, -> ! app_comm_cons, -> ! pos_succ_last, -> app_comm_cons.
    reflexivity.
  Qed.

  Fact pos_succ_cons' x [l] (Hnotnil : l <> nil) :
    pos_succ (x :: l) = x :: pos_succ l.
  Proof. destruct l; try contradiction. apply pos_succ_cons. Qed.

  Fact tr_trav_waitlist_align tr l : 
    length (fst (tr_trav_waitlist tr l)) = length (snd (tr_trav_waitlist tr l)).
  Proof.
    revert tr.
    induction l as [ | x l IH ]; intros; simpl; try reflexivity.
    destruct tr as [ni chn]; simpl. 
    destruct (nth_error chn x) as [ ch | ] eqn:E; simpl.
    - destruct (tr_trav_waitlist ch l) as (res1, res2) eqn:EE; simpl.
      specialize (IH ch).
      rewrite -> EE in IH.
      simpl in IH.
      autorewrite with list.
      rewrite -> firstn_length_le; try lia.
      now apply nth_error_some_inrange_le in E.
    - now autorewrite with list.
  Qed.

  Fact tr_trav_waitlist_length_lt_tr_size tr l : 
    length (snd (tr_trav_waitlist tr l)) < tr_size tr.
  Proof.
    revert tr.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl; try lia.
    destruct (nth_error chn x) as [ ch | ] eqn:E; simpl.
    - destruct (tr_trav_waitlist ch l) as (res1, res2) eqn:EE; simpl.
      specialize (IH ch).
      rewrite EE in IH.
      simpl in IH.
      rewrite <- firstn_skipn with (n:=x) (l:=chn) at 2.
      rewrite flat_map_app, ! app_length.
      match goal with |- (_ + ?a < S (_ + ?b))%nat => enough (a < S b)%nat end.
      + pose proof (trs_size_le_full (firstn x chn)).
        lia.
      + apply nth_error_mixin in E.
        destruct E as (_ & _ & _ & ->).
        simpl.
        rewrite app_length.
        unfold tr_size in IH.
        lia.
    - pose proof (trs_size_le_full chn).
      lia.
  Qed.

  Fact tr_trav_waitlist_pos_notnil tr l : 
    Forall (fun l' => l' <> nil) (fst (tr_trav_waitlist tr l)).
  Proof.
    destruct l as [ | x l ], tr as [ni chn]; simpl; auto.
    destruct (nth_error chn x) as [ ch | ] eqn:E; simpl.
    - destruct (tr_trav_waitlist ch l) as (res1, res2) eqn:EE; simpl.
      rewrite Forall_app, ! Forall_map.
      split; now apply list.Forall_true.
    - rewrite Forall_map.
      now apply list.Forall_true.
  Qed.

  (* "tr_trav_waitlist" enjoys a good property over list append *)
  Lemma tr_trav_waitlist_pos_app [pos1] : forall [tr sub] (H : tr_locate tr pos1 = Some sub) pos2,
    tr_trav_waitlist tr (pos1 ++ pos2) = 
      (fst (tr_trav_waitlist tr pos1) ++ (map (fun pos => pos1 ++ pos) (fst (tr_trav_waitlist sub pos2))), 
        snd (tr_trav_waitlist tr pos1) ++ snd (tr_trav_waitlist sub pos2)).
  Proof.
    induction pos1 as [ | x pos1 IH ]; intros [ni chn]; intros; simpl in *.
    - injection H as <-.
      rewrite -> map_id_eq.
      now destruct (tr_trav_waitlist _ _).
    - destruct (nth_error chn x) eqn:E; try discriminate.
      rewrite -> (IH _ _ H pos2).
      do 2 destruct (tr_trav_waitlist _ _).
      simpl.
      rewrite -> ! map_app, -> map_map, <- ! app_assoc.
      reflexivity.
  Qed.

  Lemma tr_vsplitr_full_all0pos [l] (H : Forall (fun x => x = 0) l) :
    forall tr, tr_vsplitr true tr l = tr.
  Proof.
    induction H as [ | x l -> H IH ]; intros [ni chn]; auto.
    simpl.
    destruct chn as [ | ch chn ]; auto.
    now rewrite IH.
  Qed.

  Lemma tr_vsplitr_all0pos_atleaf [l] : forall [tr] (H : Forall (fun x => x = 0) (tr_pos_valid_part tr l)) 
    (Hleaf : base.fmap tr_rootchn (tr_locate tr (tr_pos_valid_part tr l)) = Some nil) full,
    tr_vsplitr full tr l = tr.
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in *.
    - injection Hleaf as ->.
      now destruct full.
    - destruct (nth_error chn x) as [ ch | ] eqn:E; simpl in *.
      + rewrite E in Hleaf.
        apply Forall_cons_iff in H.
        destruct H as (-> & H).
        erewrite IH; eauto.
        destruct chn; try discriminate.
        now injection E as ->.
      + injection Hleaf as ->.
        now destruct full.
  Qed.

  (* give the most precise characterization *)
  Lemma tr_trav_waitlist_nil [l] : forall [tr] (Hnil : fst (tr_trav_waitlist tr l) = nil),
    Forall (fun x => x = 0) (tr_pos_valid_part tr l) /\
    (tr_locate tr l = None -> base.fmap tr_rootchn (tr_locate tr (tr_pos_valid_part tr l)) = Some nil).
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in Hnil |- *.
    - split; [ apply Forall_nil | intros [=] ].
    - destruct (nth_error chn x) as [ ch | ] eqn:E.
      + simpl.
        destruct (tr_trav_waitlist _ _) eqn:Ew in Hnil.
        simpl in Hnil.
        apply app_eq_nil in Hnil.
        destruct Hnil as (E1%map_eq_nil & ->%map_eq_nil).
        assert (x = 0%nat) as -> by (now destruct x).
        rewrite E.
        specialize (IH ch ltac:(rewrite Ew; reflexivity)).
        split; [ constructor; [ reflexivity | ] | ]; tauto.
      + simpl in Hnil |- *.
        destruct chn; try discriminate.
        auto.
  Qed.

  Corollary tr_vsplitr_full_trav_term [l tr] (Hnil : fst (tr_trav_waitlist tr l) = nil) :
    tr_vsplitr true tr l = tr.
  Proof.
    (* analytic ... though by induction might be easier? *)
    apply tr_trav_waitlist_nil in Hnil.
    destruct Hnil as (Hall0 & Hq).
    pose proof (tr_pos_valid_depth_maximal tr l) as (chn' & E & Hlt).
    rewrite E in Hq.
    destruct (tr_locate tr _) as [ [a chn] | ] eqn:Esub in E; try discriminate.
    injection E as <-.
    destruct (isSome (tr_locate tr l)) eqn:E.
    - pose proof E as E'%tr_pos_valid_depth_eq.
      rewrite tr_pos_valid_part_eq in E.
      rewrite E in *.
      eapply tr_vsplitr_full_all0pos; eauto.
    - apply isSome_false_is_None in E.
      specialize (Hq E).
      injection Hq as ->.
      apply tr_vsplitr_all0pos_atleaf; auto.
      now rewrite Esub.
  Qed.

  Lemma tr_vsplitr_leaf_validpart_congr l : forall tr,
    tr_vsplitr false tr l = tr_vsplitr false tr (tr_pos_valid_part tr l).
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl.
    - reflexivity.
    - destruct (nth_error chn x) as [ ch | ] eqn:E.
      + simpl.
        rewrite IH, E; auto.
      + reflexivity.
  Qed.

  Corollary tr_vsplitr_leaf_lastover [l tr] (H : tr_locate tr l = None) :
    tr_vsplitr false tr l = tr_vsplitr false tr (removelast l).
  Proof.
    apply tr_pos_valid_part_removelast in H.
    rewrite tr_vsplitr_leaf_validpart_congr.
    now rewrite tr_vsplitr_leaf_validpart_congr with (l:=removelast l), H.
  Qed.

  Lemma tr_vsplitr_leaf2full [l] : forall [tr] 
    (H : base.fmap tr_rootchn (tr_locate tr l) = Some nil \/ tr_locate tr l = None), 
    tr_vsplitr false tr l = tr_vsplitr true tr l.
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in H |- *.
    - now destruct H as [ [=->] | ]; try discriminate.
    - destruct (nth_error chn x) as [ ch | ] eqn:E0; simpl.
      + now erewrite -> IH; eauto.
      + reflexivity.
  Qed.

  Fact tr_vsplitr_full_by_locate_upd [l] : forall [tr sub] (H : tr_locate tr l = Some sub), 
    tr_vsplitr true tr l = tr_locate_upd (tr_vsplitr false tr l) (List.repeat 0%nat (length l)) sub.
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in *.
    - now injection H as <-.
    - destruct (nth_error chn x) as [ ch | ] eqn:Enth; try discriminate.
      simpl.
      specialize (IH _ _ H).
      congruence.
  Qed.

  Lemma tr_vsplitr_is_prefix full l : forall tr, 
    prefixtr (tr_vsplitr full tr l) tr.
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; simpl.
    - destruct full.
      + reflexivity.
      + apply prefixtr_nil_l.
    - destruct (nth_error chn x) as [ ch | ] eqn:E.
      2: apply prefixtr_nil_l.
      apply nth_error_mixin in E.
      apply prefixtr_intro with (chn_sub:=ch :: skipn (S x) chn).
      + rewrite <- (firstn_skipn x chn) at 2.
        destruct E as (_ & _ & _ & <-).
        now apply list.sublist_inserts_l.
      + constructor.
        * apply IH.
        * reflexivity.
  Qed.

  Corollary pre_iter_visited_is_prefix tr l : prefixtr (pre_iter_visited_prefix tr l) tr.
  Proof. apply tr_vsplitr_is_prefix. Qed.

  Corollary post_iter_visited_is_prefix tr l : prefixtr (post_iter_visited_prefix tr l) tr.
  Proof. apply tr_vsplitr_is_prefix. Qed.

  Fact tr_vsplitr_locate [l] :
    forall [tr sub] full (H : tr_locate tr l = Some sub),
      tr_locate (tr_vsplitr full tr l) (List.repeat 0%nat (length l)) = 
      Some (tr_vsplitr full sub nil).
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in H |- *.
    1: injection H as <-; reflexivity.
    destruct (nth_error chn x) as [ ch | ] eqn:E0; simpl.
    2: discriminate.
    erewrite IH; eauto.
  Qed.

  Lemma visited_prefix_pre2post [l] :
    forall [tr sub] (H : tr_locate tr l = Some sub) (Hnotnil : l <> nil),
      (* FIXME: maybe strengthen the following into arbitrary proper prefix in the future? *)
      base.fmap tr_rootinfo (tr_locate (pre_iter_visited_prefix tr l) (List.repeat 0%nat (length l - 1))) = 
        base.fmap tr_rootinfo (tr_locate tr (removelast l)) /\
      post_iter_visited_prefix tr l = tr_prepend_nodes (pre_iter_visited_prefix tr l)
        (List.repeat 0%nat (length l - 1)) (Node (tr_rootinfo sub) nil :: nil).
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in H |- *.
    1: contradiction.
    destruct (nth_error chn x) as [ ch | ] eqn:E; try discriminate.
    rewrite Nat.sub_0_r.
    clear Hnotnil.
    destruct (list_ifnil_destruct l) as [ -> | Hnotnil ].
    - injection H as <-.
      split; [ simpl; rewrite (prefixtr_rootinfo_same (pre_iter_visited_is_prefix _ _)); reflexivity | ].
      cbn delta -[nth_error] beta iota.
      rewrite E.
      destruct (nth_error chn (S x)) as [ ch' | ] eqn:E'.
      + simpl.
        pose proof E' as (_ & _ & _ & ->)%nth_error_mixin.
        now destruct ch'.
      + apply nth_error_None in E'.
        now rewrite skipn_all2 by assumption.
    - specialize (IH _ _ H Hnotnil).
      unfold pre_iter_visited_prefix in *.
      rewrite pos_succ_cons' by assumption.
      cbn delta -[nth_error] beta iota.
      rewrite E.
      destruct l eqn:El; try contradiction.
      simpl length in *.
      rewrite Nat.sub_succ, Nat.sub_0_r in *.
      rewrite <- El in *.
      cbn.
      rewrite E.
      split; try tauto.
      unfold tr_prepend_nodes, tr_locate_apply in *.
      cbn.
      fold (post_iter_visited_prefix ch l).
      rewrite (proj2 IH).
      now destruct (tr_locate _ _).
  Qed.

  Corollary visited_prefix_dom [l tr sub] 
    (H : tr_locate tr l = Some sub) (Hnotnil : l <> nil) :
    Permutation (map tr_rootinfo (tr_flatten (post_iter_visited_prefix tr l)))
      (tr_rootinfo sub :: map tr_rootinfo (tr_flatten (pre_iter_visited_prefix tr l))).
  Proof.
    pose proof (visited_prefix_pre2post H Hnotnil) as (H1 & H2).
    pose proof (tr_locate_parent H Hnotnil) as (par & Epar & _).
    rewrite Epar in H1.
    simpl in H1.
    rewrite H2, tr_prepend_nodes_dom_addition.
    2: now apply isSome_by_fmap in H1.
    simpl.
    list.solve_Permutation.
  Qed.

  Corollary stack_top_not_visited [l tr sub] 
    (H : tr_locate tr l = Some sub) (Hnotnil : l <> nil) (Hnodup : tr_NoDupId tr) :
    ~ In (tr_rootid sub) (map tr_rootid (tr_flatten (pre_iter_visited_prefix tr l))).
  Proof.
    pose proof (id_nodup_prefix_preserve (post_iter_visited_is_prefix tr l) Hnodup) as HH.
    eapply Permutation_NoDup with (l':=map tr_rootid (sub :: tr_flatten (pre_iter_visited_prefix tr l))) in HH.
    2: apply Permutation_rootinfo2rootid; simpl; rewrite visited_prefix_dom; eauto.
    simpl in HH.
    now inversion HH.
  Qed.

  Local Tactic Notation "injection_last_pair" "in_" hyp(E) "as_" ident(E1) ident(E2) :=
    match type of E with (?l1 ++ ?y1, ?l2 ++ ?y2) = (?l1' ++ ?y1', ?l2' ++ ?y2') =>
      assert (l1 ++ y1 = l1' ++ y1') as E1 by congruence;
      assert (l2 ++ y2 = l2' ++ y2') as E2 by congruence;
      rewrite -> app_inj_tail_iff in E1, E2 end.

  Local Tactic Notation "waitlist_align" hyp(E) "as_" ident(H) :=
    match type of E with 
    | tr_trav_waitlist ?tr ?l = _ => 
      pose proof (tr_trav_waitlist_align tr l) as H;
      rewrite -> E in H; simpl in H
    end.

  Local Tactic Notation "list_rev_codestruct" hyp(H) "as_" simple_intropattern(p1) simple_intropattern(p2) := 
    match type of H with 
    | length ?l1 = length ?l2 => 
      destruct (list_rev_destruct l1) as [ -> | p1 ]; 
      [ destruct l2 |
        destruct (list_rev_destruct l2) as [ -> | p2 ]; 
        [ subst; rewrite -> app_length, -> Nat.add_1_r in H | ] ]; 
      simpl in H; try discriminate
    end.

  (* the proofs about stack are tedious (requiring much manual manipulation), but maybe no much better way ... *)

  Local Fact tr_trav_waitlist_continue_pre [chn : list tree] [y res1 l' res2 sub']
    (Hle : y <= length chn)
    (E : (map (fun i => i :: nil) (seq 0 y), firstn y chn) = 
      (res1 ++ l' :: nil, res2 ++ sub' :: nil)) :
    exists y', y = S y' /\ l' = y' :: nil /\ res1 = map (fun i => i :: nil) (seq 0 y') /\
      nth_error chn y' = Some sub' /\ res2 = firstn y' chn.
  Proof.
    destruct y as [ | y ].
    1: simpl in E; inversion E; now destruct res1.
    rewrite seq_last, map_app in E.
    simpl in E.
    destruct (firstn_last Hle) as (? & EE & E2).
    rewrite EE in E.
    injection_last_pair in_ E as_ EE1 EE2.
    destruct EE1 as (<- & <-), EE2 as (<- & <-).
    now exists y.
  Qed.

  (* the stack top node gives the correct result of the rest of the stack *)
  Lemma tr_trav_waitlist_continue [tr] : forall [l] (H : isSome (tr_locate tr l) = true) 
    [res1 l' res2 sub'] (E : tr_trav_waitlist tr l = (res1 ++ l' :: nil, res2 ++ sub' :: nil)),
    tr_locate tr l' = Some sub' /\ tr_trav_waitlist tr l' = (res1, res2).
  Proof.
    induction tr as [ni chn IH] using tree_ind_2'; intros.
    destruct l as [ | x l ]; simpl in E.
    1: inversion E; now destruct res1.
    simpl in H.
    destruct (nth_error chn x) as [ ch | ] eqn:E0; try discriminate.
    destruct (tr_trav_waitlist ch l) as (res1', res2') eqn:EE; simpl.
    waitlist_align EE as_ Hlen.
    (* check if "tr_trav_waitlist ch l" gives nil or not *)
    list_rev_codestruct Hlen as_ (res1'' & l'' & ->) (res2'' & sub'' & ->).
    + simpl in E.
      rewrite ! app_nil_r in E.
      apply tr_trav_waitlist_continue_pre in E.
      2: now eapply nth_error_some_inrange_le; eassumption.
      destruct E as (y & -> & -> & -> & E0' & ->).
      simpl; now rewrite E0', ! app_nil_r.
    + rewrite -> map_app, -> ! app_assoc in E.
      simpl in E.
      specialize (IH _ (nth_error_In _ _ E0) _ H _ _ _ _ EE).
      destruct IH as (IH1 & IH2).
      injection_last_pair in_ E as_ EE1 EE2.
      destruct EE1 as (? & <-), EE2 as (? & <-).
      simpl.
      rewrite E0, IH1, IH2.
      split; congruence.
  Qed.

  Lemma tr_vsplitr_continue [l] : forall [tr]
    [res1 l' res2 sub'] (E : tr_trav_waitlist tr l = (res1 ++ l' :: nil, res2 ++ sub' :: nil)),
    tr_vsplitr true tr l = tr_vsplitr true tr (pos_succ l') /\
    (* proof goal merged, just for reducing repeating proof preparation; 
      and this is not quite compatible with tr_trav_waitlist_continue, so merge to here *)
    (base.fmap tr_rootchn (tr_locate tr l) = Some nil -> isSome (tr_locate tr (pos_succ l')) = true).
  Proof.
    induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in E |- *.
    1: inversion E; now destruct res1.
    destruct (nth_error chn x) as [ ch | ] eqn:E0; simpl.
    - destruct (tr_trav_waitlist ch l) as (res1', res2') eqn:EE; simpl.
      waitlist_align EE as_ Hlen.
      list_rev_codestruct Hlen as_ (res1'' & l'' & ->) (res2'' & sub'' & ->).
      + simpl in E.
        rewrite -> ! app_nil_r in E.
        apply tr_trav_waitlist_continue_pre in E.
        2: now eapply nth_error_some_inrange_le; eassumption.
        destruct E as (y & -> & -> & -> & E0' & ->).
        cbn delta -[nth_error] iota beta.
        rewrite E0, tr_vsplitr_full_trav_term by (rewrite EE; reflexivity).
        split; [ now destruct ch | auto ].
      + rewrite -> map_app, -> ! app_assoc in E.
        simpl in E.
        injection_last_pair in_ E as_ EE1 EE2.
        destruct EE1 as (? & <-), EE2 as (? & <-).
        destruct (list_rev_destruct l'') as [ El'' | (y & l''' & ->) ].
        * (* impossible *)
          pose proof (tr_trav_waitlist_pos_notnil ch l) as HH.
          rewrite EE in HH.
          simpl in HH.
          now apply Forall_app, proj2, Forall_inv in HH.
        * rewrite app_comm_cons, ! pos_succ_last, <- app_comm_cons.
          simpl.
          rewrite E0.
          specialize (IH ch _ _ _ _ EE).
          rewrite pos_succ_last in IH.
          destruct IH as (IH1 & IH2).
          split; auto; congruence.
    - split; [ | intros [=] ].
      destruct (list_rev_destruct chn) as [ -> | (chn' & ch & Echn) ].
      1: inversion E; now destruct res1.
      rewrite <- (firstn_all chn) in E at 2.
      apply tr_trav_waitlist_continue_pre in E; auto.
      destruct E as (? & El & -> & -> & E0' & ->).
      cbn delta -[nth_error] iota beta.
      pose proof (le_n (length chn)) as Htmp%nth_error_None.
      now rewrite <- El, Htmp.
  Qed.

  (* the invariant template *)

  Inductive traversal_invariant (tr : tree) : list B -> tree -> Prop :=
    | TInv_terminate : traversal_invariant tr nil tr
    | TInv_intermediate : forall stk pos sub pf, 
      pos <> nil -> (* if this is not present, then we may allow that the traversal terminates immediately after popping the root *)
      tr_locate tr pos = Some sub ->
      stk = (map tr_rootid (snd (tr_trav_waitlist tr pos) ++ (sub :: nil))) ->
      pf = pre_iter_visited_prefix tr pos ->
      traversal_invariant tr stk pf.

  Fact traversal_invariant_stacknil [tr pf]
    (H : traversal_invariant tr nil pf) : tr = pf.
  Proof.
    inversion H; subst.
    - reflexivity.
    - match goal with HH : nil = map _ _ |- _ => 
        rewrite -> map_app in HH; simpl in HH; symmetry in HH; apply app_eq_nil in HH; eqsolve
      end.
  Qed.

  Fact traversal_invariant_stacknotnil [tr stk pf] (E : stk <> nil)
    (H : traversal_invariant tr stk pf) : 
    exists pos sub, pos <> nil /\
      tr_locate tr pos = Some sub /\
      stk = (map tr_rootid (snd (tr_trav_waitlist tr pos) ++ (sub :: nil))) /\
      pf = pre_iter_visited_prefix tr pos.
  Proof.
    inversion H; subst.
    - contradiction.
    - now exists pos, sub.
  Qed.

  (* two ways to re-establish the invariant after an iteration, corresponding to
      two possible transitions during traversal: the current node has/has no child *)

  Lemma traversal_invariant_trans_children [tr pos sub]
    (Hsub : tr_locate tr pos = Some sub) (Echn : tr_rootchn sub <> nil) :
    traversal_invariant tr 
      (map tr_rootid (snd (tr_trav_waitlist tr pos) ++ tr_rootchn sub))
      (post_iter_visited_prefix tr pos).
  Proof.
    destruct sub as [ni chn].
    simpl in Echn |- *.
    destruct (list_rev_destruct chn) as [ -> | (chn' & lst_ch & Echn') ]; try contradiction.
    assert (nth_error chn (length chn') = Some lst_ch) as Enth
      by (subst chn; rewrite nth_error_app2, Nat.sub_diag; auto).
    apply TInv_intermediate with (pos:=pos ++ (length chn' :: nil)) (sub:=lst_ch).
    - now destruct pos.
    - erewrite tr_locate_pos_app' by eassumption.
      simpl.
      now rewrite Enth.
    - erewrite tr_trav_waitlist_pos_app by eassumption.
      simpl.
      rewrite Enth, ! app_nil_r.
      simpl.
      rewrite <- app_assoc, ! map_app with (l:=snd _).
      do 2 f_equal.
      subst.
      now rewrite list.take_app.
    - unfold pre_iter_visited_prefix, post_iter_visited_prefix.
      rewrite -> pos_succ_last.
      (* slightly troublesome *)
      replace (S (length chn')) with (length chn) 
        by (subst chn; rewrite app_length, <- Nat.add_1_r; reflexivity).
      erewrite tr_locate_pos_app' by eassumption.
      simpl.
      pose proof (proj2 (nth_error_None chn (length chn)) (le_n (length chn))) as Hex.
      rewrite Hex; simpl.
      rewrite -> tr_vsplitr_leaf_lastover with (l:=pos ++ (length chn) :: nil).
      2: erewrite tr_locate_pos_app' by eassumption; simpl; now rewrite Hex.
      now rewrite removelast_last.
  Qed.

  Lemma traversal_invariant_trans_nochild [tr pos sub]
    (Hsub : tr_locate tr pos = Some sub) (Echn : tr_rootchn sub = nil) :
    traversal_invariant tr 
      (map tr_rootid (snd (tr_trav_waitlist tr pos))) 
      (* essentially for full = true, though *)
      (post_iter_visited_prefix tr pos).
  Proof.
    destruct sub as [ni chn].
    simpl in Echn |- *.
    subst chn.
    (* trick here *)
    rewrite -> tr_vsplitr_leaf2full.
    2: left; now rewrite Hsub.
    destruct (tr_trav_waitlist tr pos) as (res1, res2) eqn:EE.
    waitlist_align EE as_ Hlen.
    (* two possibilities: this is/is not the last iteration *)
    list_rev_codestruct Hlen as_ (res1' & l' & ->) (res2' & sub' & ->); simpl.
    - rewrite tr_vsplitr_full_trav_term.
      2: now rewrite EE.
      apply TInv_terminate.
    - pose proof EE as (Hcont_t1 & Hcont_t2)%tr_vsplitr_continue.
      pose proof EE as (Hcont_w1 & Hcont_w2)%tr_trav_waitlist_continue.
      2: now rewrite Hsub.
      apply TInv_intermediate with (pos:=l') (sub:=sub').
      + pose proof (tr_trav_waitlist_pos_notnil tr pos) as Htmp.
        rewrite EE in Htmp.
        simpl in Htmp.
        now rewrite Forall_app, Forall_cons_iff in Htmp.
      + assumption.
      + now rewrite -> Hcont_w2.
      + unfold pre_iter_visited_prefix.
        rewrite Hcont_t2 by (rewrite Hsub; reflexivity).
        assumption.
  Qed.

  Corollary traversal_invariant_trans [tr pos sub] (Hsub : tr_locate tr pos = Some sub) :
    traversal_invariant tr 
      (map tr_rootid (snd (tr_trav_waitlist tr pos) ++ tr_rootchn sub))
      (post_iter_visited_prefix tr pos).
  Proof.
    destruct (list_ifnil_destruct (tr_rootchn sub)) as [ H | H ].
    - rewrite H, app_nil_r.
      eapply traversal_invariant_trans_nochild; eauto.
    - eapply traversal_invariant_trans_children; eauto.
  Qed.

  (* initial condition *)

  Lemma traversal_invariant_init tr : 
    traversal_invariant tr (map tr_rootid (tr_rootchn tr)) (Node (tr_rootinfo tr) nil).
  Proof.
    destruct tr as [ni chn].
    simpl.
    destruct (list_ifnil_destruct chn) as [ -> | Hnn ].
    - now apply TInv_terminate.
    - now apply (@traversal_invariant_trans_children (Node ni chn) nil _ eq_refl Hnn).
  Qed.

End Reversed_Preorder_Traversal_Theory.

End RoseTree.

Global Arguments tree : clear implicits.

(* need some tweak, otherwise will need to put @ before when doing induction, or
    face the "Not the right number of induction arguments" error *)
Global Arguments prefixtr_ind_2 [_].

Global Arguments subtr_trans {_} [_ _ _] _ _.
Global Arguments prefixtr_trans {_} [_ _ _] _ _.
