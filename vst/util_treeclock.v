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
