Require Import VST.floyd.proofauto.
Require Import arboreta.clocks.treeclock.
From arboreta.vst Require Import treeclock_clight util_vst array_support.
From arboreta.utils Require Import libtac.

(* utilities of treeclock with the support of VST *)

#[export] Instance nat_EqDec : EqDec nat.
Proof. constructor. apply Nat.eq_dec. Qed.

Fact tc_getclk_in_int_range tc (H : Foralltc (fun sub : treeclock => 
  Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) :
  forall t, Z.of_nat (tc_getclk t tc) <= Int.max_signed.
Proof.
  intros t. 
  unfold tc_getclk.
  destruct (tc_getnode t tc) as [ res | ] eqn:E.
  - eapply tc_getnode_res_Foralltc in E; [ | apply H ].
    lia.
  - pose proof (Int.max_signed_pos); lia.
Qed.

Fact tc_getclk_in_int_range_prefix (tc tc' : @treeclock nat) (Hpf : prefixtc tc tc')
  (H : Foralltc (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc') :
  Foralltc (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc.
Proof.
  rewrite -> Foralltc_Forall_subtree in H |- *.
  unfold tc_rootclk, tc_rootaclk in *.
  pose proof (List.Forall_map tc_rootinfo (fun sub : @nodeinfo nat => 
    Z.of_nat (info_clk sub) <= Int.max_signed /\ Z.of_nat (info_aclk sub) <= Int.max_signed)) as Htmp.
  simpl in Htmp.
  rewrite <- Htmp, -> Forall_forall in H |- *.
  intros x Hin%(prefixtc_flatten_info_incl Hpf).
  now apply H.
Qed.

(* TODO seems not useful now, but keep it anyway *)
Fact tc_join_partial_getclk_in_int_range (tc tc' : @treeclock nat) 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  (Hnodup' : NoDup (map tc_roottid (tc_flatten tc')))
  (H : Foralltc (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc)
  (H' : Foralltc (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc') :
  Foralltc (fun sub : treeclock => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) (tc_join_partial tc tc').
Proof.
  (* ... *)
  pose proof H as H_. pose proof H' as H'_.
  rewrite -> Foralltc_Forall_subtree in H, H' |- *.
  unfold tc_rootclk, tc_rootaclk in *.
  pose proof (List.Forall_map tc_rootinfo (fun sub : @nodeinfo nat => 
    Z.of_nat (info_clk sub) <= Int.max_signed /\ Z.of_nat (info_aclk sub) <= Int.max_signed)) as Htmp.
  simpl in Htmp.
  rewrite <- Htmp in H, H' |- *.
  eapply Permutation_Forall. 1: symmetry; apply tc_join_partial_dom_info.
  apply Forall_app. split.
  - rewrite Forall_forall in H |- *.
    intros x Hin%(prefixtc_flatten_info_incl (tc_detach_nodes_fst_is_prefix _ _)).
    now apply H.
  - pose proof (tc_attach_nodes_dom_info _ _ Hnodup Hnodup') as Hnodup''.
    destruct (tc_attach_nodes (snd (tc_detach_nodes (tc_flatten tc') tc)) tc') as [(u, clk, aclk) chn] eqn:E.
    epose proof (tc_attach_nodes_rootinfo_same _ _) as Htmp2.
    rewrite E in Htmp2. simpl in Htmp2.
    simpl in Hnodup'' |- *.
    rewrite <- map_app, -> tc_flatten_direct_result, <- app_comm_cons in Hnodup''.
    simpl in Hnodup''. rewrite <- Htmp2 in Hnodup''. 
    apply Permutation_cons_inv in Hnodup''.
    constructor; simpl.
    + apply Foralltc_self in H'_, H_. now rewrite <- Htmp2 in H'_.
    + eapply Permutation_Forall. 1: symmetry; apply Hnodup''.
      rewrite -> map_app, Forall_app. split.
      * rewrite -> tc_flatten_direct_result in H'.
        simpl in H'. now rewrite -> Forall_cons_iff in H'.
      * (* TODO why so tedious? *)
        rewrite -> Forall_forall.
        intros ni (ch' & Hin_ch' & (sub'' & <- & Hin_sub'')%in_map_iff)%map_flat_map_In.
        match type of Hin_ch' with In _ (flat_map _ ?tcs) => assert (In ch' (flat_map tc_flatten tcs)) as Htmp3 end.
        {
          eapply Permutation_in. 1: symmetry; apply tc_flatten_root_chn_split.
          apply in_app_iff, or_intror.
          eapply Permutation_in. 1: symmetry; apply tc_flatten_root_chn_split.
          now apply in_app_iff, or_introl.
        }
        rewrite -> in_flat_map in Htmp3.
        destruct Htmp3 as (sub' & Hin_sub' & Htmp3).
        eapply Forall_forall in Hin_sub'. 2: apply tc_detach_nodes_snd2fst.
        simpl in Hin_sub'.
        destruct Hin_sub' as (sub & Hin_sub & ->).
        pose proof (subtc_trans _ _ _ Hin_sub'' Htmp3) as Htmp3'.
        apply subtc_flatten_incl, incl_map with (f:=tc_rootinfo) in Hin_sub.
        apply in_map with (f:=tc_rootinfo), (prefixtc_flatten_info_incl (tc_detach_nodes_fst_is_prefix _ _)), Hin_sub in Htmp3'.
        eapply Forall_forall in Htmp3'. 2: apply H.
        now apply Htmp3'.
Qed.

Fact tc_size_bounded_by_dim tc dim (Hdim : 0 < dim)
  (H : Foralltc (fun tc' : treeclock => Z.of_nat (tc_roottid tc') < dim) tc) 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  Z.of_nat (tc_size tc) <= dim.
Proof.
  assert (incl (map tc_roottid (tc_flatten tc)) (seq 0 (Z.to_nat dim))) as Htmp.
  {
    hnf.
    intros t (sub & E & Hin)%in_map_iff.
    eapply Foralltc_subtc in Hin; [ | apply H ].
    simpl in Hin.
    apply in_seq.
    lia.
  }
  eapply NoDup_incl_length in Htmp; try assumption.
  rewrite -> map_length, -> seq_length in Htmp.
  unfold tc_size.
  lia.
Qed.

(* makes use of upd_Znth *)
Fixpoint tc_locate_update (tc : @treeclock nat) (pos : list nat) sub : @treeclock nat :=
  match pos with
  | nil => sub
  | x :: pos' =>
    let 'Node ni chn := tc in
    match nth_error chn x with
    | Some ch => Node ni (upd_Znth (Z.of_nat x) chn (tc_locate_update ch pos' sub))
    | None => tc (* invalid pos, no change *)
    end
  end.

(* rather unwanted *)
Definition tc_remove_ch (tc : @treeclock nat) (idx : nat) : @treeclock nat :=
  let 'Node ni chn := tc in
  (* TODO may use remove, instead of filter? *)
  Node ni (List.filter (fun tc' => negb (has_same_tid idx tc')) chn).

(* FIXME: temporary. this is still bad *)

Fact tc_remove_ch_when_nodup ni pre sub suf 
  (Hnodup : NoDup (map tc_roottid (tc_flatten (Node ni (pre ++ sub :: suf))))) :
  tc_remove_ch (Node ni (pre ++ sub :: suf)) (tc_roottid sub) = Node ni (pre ++ suf).
Proof.
  apply NoDup_cons_iff, proj2, tid_nodup_root_chn_split, proj1 in Hnodup.
  rewrite -> map_app in Hnodup. simpl in Hnodup.
  apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_pre & Hnodup & Hdj1).
  apply NoDup_cons_iff in Hnodup. destruct Hnodup as (Hdj2 & _).
  simpl in Hdj1.
  unfold tc_remove_ch. f_equal. rewrite -> filter_app. simpl.
  unfold has_same_tid at 2. 
  destruct (eqdec (tc_roottid sub) (tc_roottid sub)) eqn:E; try contradiction.
  simpl.
  rewrite -> ! filter_all_true; auto.
  all: setoid_rewrite negb_true_iff.
  all: unfold has_same_tid.
  all: intros ch'' Hin''; destruct (eqdec (tc_roottid ch'') (tc_roottid sub)) as [ EE | ]; 
    simpl; try eqsolve.
  - exfalso. apply Hdj2. rewrite <- EE. now apply in_map.
  - exfalso. apply (Hdj1 _ (in_map tc_roottid _ _ Hin'')). now left.
Qed.

Fact tc_detach_nodes_single tc
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  forall res 
  (* this should be a derived conclusion from Hnodup, but for now ignore it *)
  (* (Hneq : tc_roottid res <> tc_roottid tc)  *)
  l tc_par (Hsub : subtc_witness l tc_par tc) (Hin : In res (tc_rootchn tc_par)),
  tc_detach_nodes (res :: nil) tc = 
  (tc_locate_update tc l (tc_remove_ch tc_par (tc_roottid res)), (res :: nil)).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in Hnodup.
  rewrite -> NoDup_cons_iff in Hnodup. destruct Hnodup as (Hnotin & Hnodup).
  (* only one special child to be considered *)
  pose proof Hsub as Htmp. eapply par_subtc_trace with (res:=res) in Htmp; auto.
  simpl in Htmp. destruct Htmp as (ch & Hin_ch & Hsub_ch).
  (*
  assert (exists ch, In ch chn /\ subtc res ch) as (ch & Hin_ch & Hsub_ch).
  {
    destruct l as [ | x l ].
    - hnf in Hsub. simpl in Hsub. injection Hsub as <-. simpl in Hin.
      exists res. split; auto. hnf. apply tc_flatten_self_in.
    - hnf in Hsub. simpl in Hsub.
      destruct (nth_error chn x) as [ ch | ] eqn:Enth; try eqsolve.
      pose proof Enth as Hin_ch. apply nth_error_In in Hin_ch.
      exists ch. split; auto. eapply subtc_trans.
      + apply subtc_chn, Hin.
      + apply subtc_witness_iff. eauto.
  }
  *)
  pose proof (in_split _ _ Hin_ch) as (pre & suf & Echn).
  rewrite Echn in Hnodup. rewrite <- flat_map_app, -> map_app in Hnodup.
  simpl in Hnodup. rewrite -> map_app in Hnodup.
  apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_pre & Hnodup & Hdj1).
  apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_ch & Hnodup_suf & Hdj2).
  (* tc_roottid res not in pre/suf *)
  assert (forall ch', In ch' pre \/ In ch' suf -> ~ In (tc_roottid res) (map tc_roottid (tc_flatten ch'))) as Hnotin'.
  {
    (* TODO why tedious? *)
    intros ch' H Hn.
    (*
    subst chn. rewrite <- flat_map_app, -> map_app in Hnodup.
    simpl in Hnodup. rewrite -> map_app in Hnodup.
    apply NoDup_app in Hnodup. destruct Hnodup as (_ & Hnodup & Hdj1).
    apply NoDup_app in Hnodup. destruct Hnodup as (_ & _ & Hdj2).
    *)
    specialize (Hdj1 (tc_roottid res)). specialize (Hdj2 (tc_roottid res)).
    rewrite -> map_flat_map_In, -> in_app_iff in Hdj1.
    rewrite -> map_flat_map_In in Hdj2.
    rewrite -> 1 in_map_iff in Hdj1, Hdj2.
    (* pose proof (tc_flatten_self_in res) as Hself.
    apply in_map with (f:=tc_roottid) in Hself. *)
    destruct H as [ H | H ].
    - apply Hdj1. 1: eauto. left. eauto.
    - apply Hdj2; eauto.
  }
  (* avoid some cumbersome things *)
  cbn delta -[tc_getnode] iota beta.
  simpl. rewrite -> ! Echn, -> map_app. simpl.
  erewrite -> map_ext_Forall with (l:=pre) (g:=fun tc' => (tc', nil)).
  2:{ 
    rewrite -> Forall_forall. intros ch' H. specialize (Hnotin' _ (or_introl H)). 
    apply tc_detach_nodes_intact. simpl. intros.
    destruct ch'. simpl in *. eqsolve.
  }
  erewrite -> map_ext_Forall with (l:=suf).
  2:{ 
    rewrite -> Forall_forall. intros ch' H. specialize (Hnotin' _ (or_intror H)). 
    apply tc_detach_nodes_intact. simpl. intros. 
    destruct ch'. simpl in *. eqsolve.
  }
  assert (forall ch' : treeclock, In ch' pre \/ In ch' suf -> 
    tc_roottid ch' <> tc_roottid res) as Hnotin''.
  {
    intros ch' Hin'. apply Hnotin' in Hin'.
    intros E. rewrite <- E in Hin'. 
    (* TODO why this is repeating? *)
    apply False_ind, Hin', in_map, tc_flatten_self_in.
  }
  destruct l as [ | x l ].
  - simpl in Hsub. injection Hsub as <-. simpl in Hin.
    rewrite -> Echn. simpl. rewrite -> filter_app. simpl. 
    rewrite -> ! filter_all_true; auto.
    2-3: intros ch' Hin'; apply negb_true_iff, has_same_tid_false.
    3: specialize (Hnotin' _ (or_introl Hin')).
    2: specialize (Hnotin' _ (or_intror Hin')).
    2-3: intros EE; rewrite -> EE in Hnotin'; apply Hnotin', in_map, tc_flatten_self_in.
    assert (res = ch) as <-.
    {
      rewrite -> Echn, -> in_app in Hin. simpl in Hin.
      rewrite <- or_assoc, -> or_comm with (B:=ch = res), -> or_assoc in Hin.
      destruct Hin as [ | Hin ]; auto.
      apply Hnotin' in Hin.
      apply False_ind, Hin, in_map, tc_flatten_self_in.
    }
    pose proof (eq_refl (tc_roottid res)) as Htmp.
    rewrite <- has_same_tid_true in Htmp. rewrite -> Htmp. simpl.
    rewrite tc_detach_nodes_intact.
    2:{
      simpl. intros t HH [ <- | [] ].
      destruct res. simpl in Hnodup_ch, HH. 
      rewrite -> NoDup_cons_iff in Hnodup_ch. eqsolve. 
    }
    rewrite <- List.map_cons with (f:=(fun ch' : treeclock => (ch', []))), <- map_app, <- Echn.
    (* TODO repeat above *)
    destruct (List.split (map (fun ch : treeclock => (ch, [])) chn))
      as (new_chn, forest) eqn:Esplit, 
      (partition _ new_chn)
      as (forest', new_chn') eqn:Epar.
    rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
    rewrite -> partition_filter in Epar.
    simpl in Esplit.
    apply pair_equal_split in Esplit, Epar.
    destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
    rewrite -> map_id_eq in Enew_chn. subst new_chn.
    replace (concat forest) with (@nil (@treeclock nat)) in *.
    2:{ 
      symmetry. apply concat_nil_Forall.
      subst forest. apply List.Forall_map. now apply Forall_forall.
    }

    simpl. f_equal. 1: f_equal.
    all: subst new_chn' forest' chn; rewrite -> filter_app; simpl.
    1: rewrite -> ! filter_all_true; auto.
    4: rewrite -> ! filter_all_false; auto.
    2-3: setoid_rewrite negb_true_iff.
    all: unfold has_same_tid.
    2-3,5-6: intros ch'' Hin''; destruct (eqdec (tc_roottid res) (tc_roottid ch'')) as [ EE | ]; 
      simpl; try eqsolve.
    2-5: eapply False_ind, Hnotin''; eauto.
    all: destruct (eqdec (tc_roottid res) (tc_roottid res)); try eqsolve.
  - (* use IH *)
    hnf in Hsub. simpl in Hsub.
    destruct (nth_error chn x) as [ ch' | ] eqn:Enth; try eqsolve.
    assert (length pre = x) as Elen.
    {
      destruct (Nat.eq_dec (length pre) x) as [ | Hneq ]; auto.
      assert (x < Datatypes.length pre \/ (Datatypes.length (pre ++ [ch])) <= x)%nat as Htmp.
      { rewrite -> last_length. lia. }
      assert (In ch' pre \/ In ch' suf) as HH.
      {
        subst chn.
        destruct Htmp as [ Htmp | Htmp ].
        - eapply nth_error_app1 in Htmp. rewrite -> Enth in Htmp.
          symmetry in Htmp. left. now apply nth_error_In in Htmp.
        - rewrite -> app_cons_assoc in Enth.
          eapply nth_error_app2 in Htmp. rewrite -> Enth in Htmp.
          symmetry in Htmp. right. now apply nth_error_In in Htmp.
      }
      apply Hnotin' in HH.
      assert (subtc tc_par ch') as HH2 by (apply subtc_witness_iff; eauto).
      eapply subtc_chn, subtc_trans with (tc'':=res) (tc':=tc_par) in Hin. 2: apply HH2.
      now apply False_ind, HH, in_map.
    }
    assert (ch = ch') as <-.
    { 
      subst chn x. rewrite -> nth_error_app2, -> Nat.sub_diag in Enth; try lia.
      simpl in Enth. eqsolve.
    } 
    (*
    assert (ch = ch') as <-.
    {
      (* TODO repeating? *)
      apply nth_error_In in Enth.
      rewrite -> Echn, -> in_app in Enth. simpl in Enth.
      rewrite <- or_assoc, -> or_comm with (B:=ch = ch'), -> or_assoc in Enth.
      destruct Enth as [ | Enth ]; auto.
      apply Hnotin' in Enth.
      assert (subtc tc_par ch') as HH by (apply subtc_witness_iff; eauto).
      eapply subtc_chn, subtc_trans with (tc'':=res) (tc':=tc_par) in Hin. 2: apply HH.
      now apply False_ind, Enth, in_map.
    }
    *)
    rewrite -> Forall_forall in IH. 
    specialize (IH _ Hin_ch Hnodup_ch _ _ _ Hsub Hin).
    rewrite -> IH. simpl. rewrite -> Echn in Enth. rewrite Enth. 
    remember (tc_locate_update ch l (tc_remove_ch tc_par (tc_roottid res))) as res'.
    (* TODO repeat above *)
    rewrite -> split_app. simpl. 
    destruct (List.split (map (fun ch' : treeclock => (ch', [])) pre))
      as (new_chn_pre, forest_pre) eqn:Esplit_pre,
      (List.split (map (fun ch' : treeclock => (ch', [])) suf))
      as (new_chn_suf, forest_suf) eqn:Esplit_suf,
      (partition _ (new_chn_pre ++ res' :: new_chn_suf))
      as (forest', new_chn') eqn:Epar.
    rewrite -> split_map_fst_snd, -> ! map_map in Esplit_pre, Esplit_suf.
    rewrite -> partition_filter in Epar.
    simpl in Esplit_pre, Esplit_suf.
    apply pair_equal_split in Esplit_pre, Esplit_suf, Epar.
    destruct Esplit_pre as (Enew_chn_pre & Eres_pre), 
      Esplit_suf as (Enew_chn_suf & Eres_suf), Epar as (Eres' & Enew_chn').
    rewrite -> map_id_eq in Enew_chn_pre, Enew_chn_suf. subst new_chn_pre new_chn_suf.
    replace (concat (forest_pre ++ [res] :: forest_suf)) with ([res]) in *.
    2:{ 
      symmetry. rewrite -> concat_app. simpl. 
      rewrite -> ! (proj2 (concat_nil_Forall _)); auto.
      all: subst; apply List.Forall_map; now apply Forall_forall.
    }

    assert (tc_roottid ch <> tc_roottid res) as Hneq.
    {
      destruct ch as [(v, ?, ?) ?]. simpl. intros ->.
      simpl in Hnodup_ch. apply NoDup_cons_iff, proj1 in Hnodup_ch.
      apply par_subtc_trace with (res:=res) in Hsub; auto.
      simpl in Hsub. destruct Hsub as (ch0 & Hin0 & Hsub0).
      apply Hnodup_ch, map_flat_map_In.
      exists ch0. split; auto. now apply in_map.
    }
    assert (tc_roottid res' <> tc_roottid res) as Hneq'.
    {
      epose proof (tc_detach_nodes_fst_is_prefix _ _) as Htmp.
      rewrite IH in Htmp. simpl in Htmp. 
      apply prefixtc_rootinfo_same, tc_rootinfo_tid_inj in Htmp. eqsolve.
    }
    (* TODO repeating *)
    simpl. f_equal. 1: f_equal. 2: f_equal.
    all: subst new_chn' forest' chn; rewrite -> filter_app; simpl.
    1: rewrite -> ! filter_all_true; auto.
    4: rewrite -> ! filter_all_false; auto.
    2-3: setoid_rewrite negb_true_iff.
    all: unfold has_same_tid.
    2-3,5-6: intros ch'' Hin''; destruct (eqdec (tc_roottid res) (tc_roottid ch'')) as [ EE | ]; 
      simpl; try eqsolve.
    2-5: eapply False_ind, Hnotin''; eauto.
    all: destruct (eqdec (tc_roottid res) (tc_roottid res')); simpl; try eqsolve.
    rewrite -> upd_Znth_char; auto.
    subst x. apply Zlength_correct.
Qed.

(* describing how to do single attach, in two phases *)

(* FIXME: really repeating proof! *)
Fact tc_attach_nodes_single tc forest sub
  (* can be unified actually *)
  (Hnotin1 : find (has_same_tid (tc_roottid sub)) forest = None)
  (Hnotin2 : ~ In (tc_roottid sub) (map tc_roottid (tc_flatten tc)))
  fr (Hfr : match fr with 
    | nil => tc_rootchn sub = nil
    (* really fine-grained *)
    | a :: fr' => tc_roottid a = tc_roottid sub /\ tc_rootchn a = tc_rootchn sub /\ fr' = nil
    end) :
  forall l tc_par (H : tc_locate tc l = Some tc_par),
  exists tc_par', tc_locate (tc_attach_nodes forest tc) l = Some tc_par' /\
    tc_par' = tc_attach_nodes forest tc_par /\
    tc_locate_update (tc_attach_nodes forest tc) l 
      (Node (tc_rootinfo tc_par') (sub :: tc_rootchn tc_par')) =
    tc_attach_nodes (fr ++ forest) 
      (tc_locate_update tc l (Node (tc_rootinfo tc_par) (Node (tc_rootinfo sub) nil :: tc_rootchn tc_par))).
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
      simpl. unfold has_same_tid. fold (tc_roottid sub).
      rewrite -> ! E1.
      destruct (eqdec (tc_roottid sub) (tc_roottid sub)); try contradiction.
      simpl.
      f_equal. 1: rewrite E2; now destruct sub.
      f_equal.
      * erewrite -> map_ext_Forall. 1: reflexivity.
        apply Forall_forall. intros ch Hin. apply tc_attach_nodes_forest_cleanhd.
        rewrite E1.
        intros ?; apply Hnotin2; eauto.
      * destruct (eqdec (tc_roottid sub) (info_tid ni)); try congruence.
        simpl. reflexivity.
  - simpl in H.
    destruct (nth_error chn x) as [ ch | ] eqn:Enth; try discriminate.
    pose proof Enth as Hinrange%nth_error_some_inrange.
    pose proof Enth as Hin%nth_error_In.
    rewrite -> Forall_forall in IH.
    assert (~ In (tc_roottid sub) (map tc_roottid (tc_flatten ch))) as Htmp by (intros ?; apply Hnotin2; eauto).
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
      simpl. unfold has_same_tid.
      rewrite E1.
      destruct (eqdec (tc_roottid sub) (info_tid ni)); try congruence.
      simpl. reflexivity.
Qed.

Fact tc_vertical_splitr_forward l (Hnotnil : l <> nil) : 
  forall tc sub (H : tc_locate tc l = Some sub),
  (* TODO is this exists redundant? *)
  exists tc_par, tc_locate (tc_vertical_splitr (ssrbool.isSome (tc_locate tc (pos_succ l))) tc (pos_succ l)) 
      (List.repeat 0%nat (length l - 1)%nat) = Some tc_par /\
    tc_vertical_splitr false tc l =
    tc_locate_update (tc_vertical_splitr (ssrbool.isSome (tc_locate tc (pos_succ l))) tc (pos_succ l)) 
      (List.repeat 0%nat (length l - 1)%nat) (Node (tc_rootinfo tc_par) (Node (tc_rootinfo sub) nil :: tc_rootchn tc_par)).
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
  - destruct (nth_error (tc_rootchn ch0) x) as [ chch | ] eqn:Echch.
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

(* TODO will this be useful? *)

Fact tc_locate_update_pos_app pos1 : forall tc pos2 sub res (H : tc_locate tc pos1 = Some res),
  tc_locate (tc_locate_update tc pos1 sub) (pos1 ++ pos2) = tc_locate sub pos2.
Proof.
  induction pos1 as [ | x pos1 IH ]; intros; simpl in *.
  - injection H as <-.
    reflexivity.
  - destruct tc as [ni chn].
    simpl in *.
    destruct (nth_error chn x) eqn:E; try discriminate.
    simpl.
    (* length trick *)
    pose proof E as (pre & suf & -> & Elen)%nth_error_split.
    rewrite -> upd_Znth_char.
    2: rewrite Zlength_correct; f_equal; assumption.
    subst x.
    rewrite -> nth_error_app2; auto.
    rewrite -> Nat.sub_diag. simpl.
    eapply IH; eauto.
Qed.

Fact tc_vertical_splitr_tofull l : forall tc sub (H : tc_locate tc l = Some sub), 
  tc_vertical_splitr true tc l = tc_locate_update (tc_vertical_splitr false tc l) (List.repeat 0%nat (length l)) sub.
Proof.
  induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in *.
  - now injection H as <-.
  - destruct (nth_error chn x) as [ ch | ] eqn:Enth; try discriminate.
    specialize (IH _ _ H).
    rewrite upd_Znth0.
    congruence.
Qed.

(* a very niche case *)

Fact tc_locate_update_prepend_dom [A : Type] l tcs ni' (f : nodeinfo -> A) : 
  forall tc sub (H : tc_locate tc l = Some sub) (E : f ni' = f (tc_rootinfo sub)), 
  Permutation (map f (map tc_rootinfo (tc_flatten (tc_locate_update tc l (Node ni' (tcs ++ tc_rootchn sub))))))
    (map f (map tc_rootinfo (flat_map tc_flatten tcs ++ tc_flatten tc))).
Proof.
  induction l as [ | x l IH ]; intros; simpl in *.
  - injection H as <-.
    rewrite E, <- flat_map_app, -> ! map_app, -> tc_flatten_direct_result with (tc:=tc).
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
