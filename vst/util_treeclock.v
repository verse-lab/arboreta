Require Import VST.floyd.proofauto.
Require Import arboreta.clocks.treeclock.
From arboreta.vst Require Import treeclock_clight util_vst array_support.
From arboreta.utils Require Import util libtac.

(* utilities of treeclock with the support of VST *)

#[export] Instance nat_EqDec : EqDec nat.
Proof. exact Nat.eq_dec. Qed.

Global Notation treeclock := (tree (nodeinfo nat)).

Fact tc_getclk_in_int_range tc (H : Foralltr (fun sub : treeclock => 
  Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) :
  forall t, Z.of_nat (tc_getclk t tc) <= Int.max_signed.
Proof.
  intros t. 
  unfold tc_getclk.
  destruct (tr_getnode t tc) as [ res | ] eqn:E.
  - eapply tr_getnode_res_Foralltr in E; [ | apply H ].
    tauto.
  - pose proof (Int.max_signed_pos); lia.
Qed.

Fact tc_getclk_in_int_range_prefix (tc tc' : treeclock) (Hpf : prefixtr tc tc')
  (H : Foralltr (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc') :
  Foralltr (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc.
Proof.
  rewrite -> Foralltr_Forall_subtree in H |- *.
  unfold tc_rootclk, tc_rootaclk in *.
  pose proof (List.Forall_map tr_rootinfo (fun sub : nodeinfo nat => 
    Z.of_nat (info_clk sub) <= Int.max_signed /\ Z.of_nat (info_aclk sub) <= Int.max_signed)) as Htmp.
  simpl in Htmp.
  rewrite <- Htmp, -> Forall_forall in H |- *.
  intros x Hin%(prefixtr_flatten_info_incl Hpf).
  now apply H.
Qed.

(* seems not useful now, but keep it anyway *)
(*
Fact tc_join_partial_getclk_in_int_range (tc tc' : treeclock) 
  (Hnodup : NoDup (map tr_rootid (tr_flatten tc)))
  (Hnodup' : NoDup (map tr_rootid (tr_flatten tc')))
  (H : Foralltr (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc)
  (H' : Foralltr (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc') :
  Foralltr (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) (tc_join_partial tc tc').
Proof.
  (* ... *)
  pose proof H as H_. pose proof H' as H'_.
  rewrite -> Foralltr_Forall_subtree in H, H' |- *.
  unfold tc_rootclk, tc_rootaclk in *.
  pose proof (List.Forall_map tr_rootinfo (fun sub : @nodeinfo nat => 
    Z.of_nat (info_clk sub) <= Int.max_signed /\ Z.of_nat (info_aclk sub) <= Int.max_signed)) as Htmp.
  simpl in Htmp.
  rewrite <- Htmp in H, H' |- *.
  eapply Permutation_Forall. 1: symmetry; apply tc_join_partial_dom_info.
  apply Forall_app. split.
  - rewrite Forall_forall in H |- *.
    intros x Hin%(prefixtr_flatten_info_incl (tc_detach_nodes_fst_is_prefix _ _)).
    now apply H.
  - pose proof (tc_attach_nodes_dom_info _ _ Hnodup Hnodup') as Hnodup''.
    destruct (tc_attach_nodes (snd (tc_detach_nodes (tr_flatten tc') tc)) tc') as [(u, clk, aclk) chn] eqn:E.
    epose proof (tc_attach_nodes_rootinfo_same _ _) as Htmp2.
    rewrite E in Htmp2. simpl in Htmp2.
    simpl in Hnodup'' |- *.
    rewrite <- map_app, -> tr_flatten_direct_result, <- app_comm_cons in Hnodup''.
    simpl in Hnodup''. rewrite <- Htmp2 in Hnodup''. 
    apply Permutation_cons_inv in Hnodup''.
    constructor; simpl.
    + apply Foralltr_self in H'_, H_. now rewrite <- Htmp2 in H'_.
    + eapply Permutation_Forall. 1: symmetry; apply Hnodup''.
      rewrite -> map_app, Forall_app. split.
      * rewrite -> tr_flatten_direct_result in H'.
        simpl in H'. now rewrite -> Forall_cons_iff in H'.
      * (* why so tedious? *)
        rewrite -> Forall_forall.
        intros ni (ch' & Hin_ch' & (sub'' & <- & Hin_sub'')%in_map_iff)%map_flat_map_In.
        match type of Hin_ch' with In _ (flat_map _ ?tcs) => assert (In ch' (flat_map tr_flatten tcs)) as Htmp3 end.
        {
          eapply Permutation_in. 1: symmetry; apply tr_flatten_root_chn_split.
          apply in_app_iff, or_intror.
          eapply Permutation_in. 1: symmetry; apply tr_flatten_root_chn_split.
          now apply in_app_iff, or_introl.
        }
        rewrite -> in_flat_map in Htmp3.
        destruct Htmp3 as (sub' & Hin_sub' & Htmp3).
        eapply Forall_forall in Hin_sub'. 2: apply tc_detach_nodes_snd2fst.
        simpl in Hin_sub'.
        destruct Hin_sub' as (sub & Hin_sub & ->).
        pose proof (subtc_trans _ _ _ Hin_sub'' Htmp3) as Htmp3'.
        apply subtr_flatten_incl, incl_map with (f:=tr_rootinfo) in Hin_sub.
        apply in_map with (f:=tr_rootinfo), (prefixtr_flatten_info_incl (tc_detach_nodes_fst_is_prefix _ _)), Hin_sub in Htmp3'.
        eapply Forall_forall in Htmp3'. 2: apply H.
        now apply Htmp3'.
Qed.
*)

Fact tr_size_bounded_by_dim tc dim (Hdim : 0 < dim)
  (H : Foralltr (fun tc' : treeclock => Z.of_nat (tr_rootid tc') < dim) tc) 
  (Hnodup : NoDup (map tr_rootid (tr_flatten tc))) :
  Z.of_nat (tr_size tc) <= dim.
Proof.
  assert (incl (map tr_rootid (tr_flatten tc)) (seq 0 (Z.to_nat dim))) as Htmp.
  {
    hnf.
    intros t (sub & E & Hin)%in_map_iff.
    eapply Foralltr_subtr in Hin; [ | apply H ].
    simpl in Hin.
    apply in_seq.
    lia.
  }
  eapply NoDup_incl_length in Htmp; try assumption.
  rewrite -> map_length, -> seq_length in Htmp.
  unfold tr_size.
  lia.
Qed.
(*
(* rather unwanted *)
Definition tc_remove_ch (tc : treeclock) (idx : nat) : treeclock :=
  let 'Node ni chn := tc in
  Node ni (List.filter (fun tc' => negb (has_same_id idx tc')) chn).

(* FIXME: temporary. this is still bad *)

Fact tc_remove_ch_when_nodup ni pre sub suf 
  (Hnodup : NoDup (map tr_rootid (tr_flatten (Node ni (pre ++ sub :: suf))))) :
  tc_remove_ch (Node ni (pre ++ sub :: suf)) (tr_rootid sub) = Node ni (pre ++ suf).
Proof.
  apply NoDup_cons_iff, proj2, id_nodup_root_chn_split, proj1 in Hnodup.
  rewrite -> map_app in Hnodup. simpl in Hnodup.
  apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_pre & Hnodup & Hdj1).
  apply NoDup_cons_iff in Hnodup. destruct Hnodup as (Hdj2 & _).
  simpl in Hdj1.
  unfold tc_remove_ch. f_equal. rewrite -> filter_app. simpl.
  unfold has_same_id at 2. 
  destruct (eqdec (tr_rootid sub) (tr_rootid sub)) eqn:E; try contradiction.
  simpl.
  rewrite -> ! filter_all_true; auto.
  all: setoid_rewrite negb_true_iff.
  all: unfold has_same_id.
  all: intros ch'' Hin''; destruct (eqdec (tr_rootid ch'') (tr_rootid sub)) as [ EE | ]; 
    simpl; try eqsolve.
  - exfalso. apply Hdj2. rewrite <- EE. now apply in_map.
  - exfalso. apply (Hdj1 _ (in_map tr_rootid _ _ Hin'')). now left.
Qed.
*)

(* describing how to do single attach, in two phases *)
(*
(* FIXME: really repeating proof! *)
Fact tc_attach_nodes_single tc forest sub
  (* can be unified actually *)
  (Hnotin1 : find (has_same_id (tr_rootid sub)) forest = None)
  (Hnotin2 : ~ In (tr_rootid sub) (map tr_rootid (tr_flatten tc)))
  fr (Hfr : match fr with 
    | nil => tr_rootchn sub = nil
    (* really fine-grained *)
    | a :: fr' => tr_rootid a = tr_rootid sub /\ tr_rootchn a = tr_rootchn sub /\ fr' = nil
    end) :
  forall l tc_par (H : tr_locate tc l = Some tc_par),
  exists tc_par', tr_locate (tc_attach_nodes forest tc) l = Some tc_par' /\
    tc_par' = tc_attach_nodes forest tc_par /\
    tr_locate_update (tc_attach_nodes forest tc) l 
      (Node (tr_rootinfo tc_par') (sub :: tr_rootchn tc_par')) =
    tc_attach_nodes (fr ++ forest) 
      (tr_locate_update tc l (Node (tr_rootinfo tc_par) (Node (tr_rootinfo sub) nil :: tr_rootchn tc_par))).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl in Hnotin2. apply Decidable.not_or in Hnotin2.
  destruct Hnotin2 as (Hneq & Hnotin2).
  rewrite -> map_flat_map_In in Hnotin2.
  destruct l as [ | x l ].
  - simpl in H.
    injection H as <-.
    eexists. split; [ reflexivity | ]. split; [ reflexivity | ].
    simpl. f_equal.
    destruct fr as [ | subi fr ].
    + destruct sub. simpl in Hfr. subst. simpl. do 2 f_equal. simpl in Hnotin1. now rewrite Hnotin1.
    + destruct Hfr as (E1 & E2 & ->).
      simpl. unfold has_same_id. fold (tr_rootid sub).
      rewrite -> ! E1.
      destruct (eqdec (tr_rootid sub) (tr_rootid sub)); try contradiction.
      simpl.
      f_equal. 1: rewrite E2; now destruct sub.
      f_equal.
      * erewrite -> map_ext_Forall. 1: reflexivity.
        apply Forall_forall. intros ch Hin. apply tc_attach_nodes_forest_cleanhd.
        rewrite E1.
        intros ?; apply Hnotin2; eauto.
      * destruct (eqdec (tr_rootid sub) (info_tid ni)); try congruence.
        simpl. reflexivity.
  - simpl in H.
    destruct (nth_error chn x) as [ ch | ] eqn:Enth; try discriminate.
    pose proof Enth as Hinrange%nth_error_some_inrange.
    pose proof Enth as Hin%nth_error_In.
    rewrite -> Forall_forall in IH.
    assert (~ In (tr_rootid sub) (map tr_rootid (tr_flatten ch))) as Htmp by (intros ?; apply Hnotin2; eauto).
    specialize (IH _ Hin Htmp _ _ H).
    destruct IH as (tc_par' & Ea & Eb & IH).
    eexists. split.
    1:{
      simpl.
      rewrite -> nth_error_app1. 2: now rewrite map_length.
      erewrite -> map_nth_error. 2: apply Enth.
      apply Ea.
    }
    split; [ assumption | ].
    simpl.
    rewrite -> nth_error_app1. 2: now rewrite map_length.
    erewrite -> map_nth_error. 2: apply Enth.
    rewrite -> Enth, -> IH.
    simpl. f_equal.
    rewrite <- upd_Znth_map, -> upd_Znth_app1.
    2: rewrite Zlength_map, Zlength_correct; lia.
    f_equal.
    + erewrite -> map_ext_Forall. 1: reflexivity.
      apply Forall_forall. intros ch' Hin'. 
      destruct fr. 1: reflexivity.
      destruct Hfr as (E1 & E2 & ->).
      apply tc_attach_nodes_forest_cleanhd.
      rewrite E1.
      intros ?; apply Hnotin2; eauto.
    + destruct fr. 1: reflexivity.
      destruct Hfr as (E1 & E2 & ->).
      simpl. unfold has_same_id.
      rewrite E1.
      destruct (eqdec (tr_rootid sub) (info_tid ni)); try congruence.
      simpl. reflexivity.
Qed.
*)
(*
Fact tr_vsplitr_forward l (Hnotnil : l <> nil) : 
  forall tc (sub : treeclock) (H : tr_locate tc l = Some sub),
  (* TODO is this exists redundant? *)
  exists tc_par, tr_locate (tr_vsplitr (isSome (tr_locate tc (pos_succ l))) tc (pos_succ l)) 
      (List.repeat 0%nat (length l - 1)%nat) = Some tc_par /\
    tr_vsplitr false tc l =
    tr_locate_update (tr_vsplitr (isSome (tr_locate tc (pos_succ l))) tc (pos_succ l)) 
      (List.repeat 0%nat (length l - 1)%nat) (Node (tr_rootinfo tc_par) (Node (tr_rootinfo sub) nil :: tr_rootchn tc_par)).
Proof.
  destruct l as [ | x0 l ]; try contradiction.
  clear Hnotnil.
  revert x0.
  cbn delta [length Nat.sub] iota beta. rewrite -> ! Nat.sub_0_r.
  induction l as [ | x l IH ]; intros x0 [ni chn]; intros; simpl in H.
  all: destruct (nth_error chn x0) as [ ch0 | ] eqn:Ech0; try discriminate.
  - injection H as ->.
    eexists. split; [ reflexivity | ].
    pose proof (pos_succ_last nil x0) as Htmp.
    simpl in Htmp.
    rewrite -> ! Htmp.
    clear Htmp.
    destruct (nth_error chn (S x0)) as [ ch' | ] eqn:Ech'.
    + pose proof Ech' as Ech''.
      simpl in Ech' |- *; rewrite Ech', Ech0; simpl.
      f_equal. f_equal.
      (* TODO this should be repeating the proof somewhere *)
      apply nth_error_split in Ech''.
      destruct Ech'' as (pre & suf & Echn & Elen).
      pose proof Echn as Echn'.
      rewrite <- firstn_skipn with (n:=S x0) (l:=chn) in Echn'.
      rewrite -> Echn, -> list.take_app_alt in Echn' at 1; auto.
      apply app_inv_head in Echn'.
      rewrite Echn'. f_equal. 1: now destruct ch'.
      now apply firstn_skipn_onemore in Echn'.
    + pose proof Ech' as Hx0%nth_error_None.
      simpl in Ech' |- *; rewrite Ech', Ech0; simpl.
      now rewrite skipn_all2.
  - destruct (nth_error (tr_rootchn ch0) x) as [ chch | ] eqn:Echch.
    2: discriminate.
    specialize (IH x ch0 sub).
    removehead IH.
    2: simpl; now rewrite Echch.
    destruct IH as (tc_par & Etc_par & IH).
    rewrite -> ! pos_succ_cons.
    set (ll:=(x :: l)) in *.
    eexists. split.
    + simpl. rewrite Ech0. simpl. apply Etc_par.
    + simpl. rewrite Ech0, Echch. f_equal.
      rewrite -> upd_Znth0. f_equal.
      rewrite <- IH. subst ll. simpl. rewrite Echch. reflexivity.
Qed.
*)

(* a very niche case *)
(*
Fact tr_locate_update_prepend_dom [A : Type] l tcs ni' (f : nodeinfo -> A) : 
  forall tc sub (H : tr_locate tc l = Some sub) (E : f ni' = f (tr_rootinfo sub)), 
  Permutation (map f (map tr_rootinfo (tr_flatten (tr_locate_update tc l (Node ni' (tcs ++ tr_rootchn sub))))))
    (map f (map tr_rootinfo (flat_map tr_flatten tcs ++ tr_flatten tc))).
Proof.
  induction l as [ | x l IH ]; intros; simpl in *.
  - injection H as <-.
    rewrite E, <- flat_map_app, -> ! map_app, -> tr_flatten_direct_result with (tc:=tc).
    simpl.
    apply Permutation_middle.
  - destruct tc as [ni chn].
    simpl in H |- *.
    destruct (nth_error chn x) as [ ch | ] eqn:Enth; try discriminate.
    specialize (IH _ _ H E).
    pose proof Enth as (pre & suf & -> & Elen)%nth_error_split.
    rewrite upd_Znth_char.
    2: rewrite Zlength_correct; now f_equal.
    simpl.
    rewrite <- ! flat_map_app, -> ! map_app.
    simpl.
    rewrite -> ! map_app, -> IH, -> ! map_app.
    (* handcraft *)
    rewrite <- Permutation_middle.
    constructor.
    rewrite -> ! app_assoc.
    do 2 apply Permutation_app_tail.
    apply Permutation_app_comm.
Qed.
*)
