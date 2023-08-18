Require Import VST.floyd.proofauto.
Require Import distributedclocks.clocks.treeclock.
From distributedclocks.vst Require Import treeclock_clight util_vst array_support.
From distributedclocks.utils Require Import libtac.

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


