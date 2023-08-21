From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
From distributedclocks.clocks Require Export treeclock.
Import ssreflect.SsrSyntax.

From stdpp Require list.

Section Degenerated_TreeClock.

Context {thread : Type} `{thread_eqdec : EqDec thread}.

Fixpoint tc_get_updated_nodes_join_degen tc tc' : treeclock :=
  let: Node info_u' chn_u' := tc' in
  Node info_u' (filtermap (fun tc'' => negb (tc_rootclk tc'' <=? (tc_getclk (tc_roottid tc'') tc))) 
    (tc_get_updated_nodes_join_degen tc) chn_u')
.

Lemma tc_get_updated_nodes_join_degen_is_prefix tc tc' :
  prefixtc (tc_get_updated_nodes_join_degen tc tc') tc'.
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> filtermap_correct.
  econstructor.
  1: eapply filter_sublist.
  now apply Forall2_mapself_l, Forall_filter.
Qed.

Lemma tc_get_updated_nodes_join_degen_shape tc' :
  forall tc (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc'),
  Foralltc (fun tc' => tc_getclk (tc_roottid tc') tc < tc_rootclk tc') 
    (tc_get_updated_nodes_join_degen tc tc').
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le |- *.
  rewrite -> filtermap_correct.
  constructor.
  - now simpl.
  - clear u' clk_u' aclk_u' Hroot_clk_le.
    (* do a simple induction *)
    induction chn' as [ | ch' chn' IH' ].
    1: constructor.
    rewrite -> List.Forall_cons_iff in IH.
    simpl.
    rewrite <- Nat.ltb_antisym at 1.
    destruct (tc_getclk (tc_roottid ch') tc <? tc_rootclk ch') eqn:E.
    2: intuition.
    simpl.
    apply Nat.ltb_lt in E.
    intuition.
Qed.

(* TODO this is much similar to the proof for original treeclock. need revision *)

Corollary tc_get_updated_nodes_join_degen_sound tc' (Hnodup: NoDup (map tc_roottid (tc_flatten tc')))
  tc (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') :
  forall t, tc_getnode t (tc_get_updated_nodes_join_degen tc tc') ->
    tc_getclk t tc < tc_getclk t tc'.
Proof.
  pose proof (tc_get_updated_nodes_join_degen_shape _ _ Hroot_clk_le) as H.
  apply Foralltc_Forall_subtree in H.
  intros t Hres.
  rewrite <- tc_getnode_subtc_iff, -> in_map_iff in Hres.
  destruct Hres as (sub & <- & Hin).
  pose proof Hin as Einfo.
  apply in_map with (f:=tc_rootinfo) in Einfo.
  eapply prefixtc_flatten_info_incl in Einfo.
  2: apply tc_get_updated_nodes_join_degen_is_prefix.
  rewrite -> in_map_iff in Einfo.
  destruct Einfo as (sub' & Einfo & Hin').
  pose proof (tc_rootinfo_tid_inj _ _ Einfo) as Et.
  pose proof (tc_rootinfo_clk_inj _ _ Einfo) as Eclk.
  pose proof (tid_nodup_find_self _ Hnodup) as Hself.
  rewrite -> List.Forall_forall in H, Hself.
  specialize (H _ Hin).
  specialize (Hself _ Hin').
  rewrite -> Et in Hself.
  unfold tc_getclk at 2.
  unfold tc_getnode.
  rewrite -> Hself.
  congruence.
Qed.

Lemma tc_get_updated_nodes_join_degen_complete tc' (Hnodup: NoDup (map tc_roottid (tc_flatten tc'))) : 
  forall tc (Hdmono: Foralltc (dmono_single tc) tc')
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc')
  t (Hlt : tc_getclk t tc < tc_getclk t tc'),
    (tc_getnode t (tc_get_updated_nodes_join_degen tc tc')).
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le, Hnodup |- *.
  rewrite -> filtermap_correct.
  unfold tc_getclk in Hlt at 2.
  cbn in Hlt |- *.
  destruct (eqdec u' t) as [ <- | Htneq ] eqn:Etdec.
  1: intuition.
  simpl.
  rewrite -> NoDup_cons_iff in Hnodup.

  destruct (find (has_same_tid t) (flat_map tc_flatten chn')) as [ res | ] eqn:E.
  2: now destruct (tc_getnode t tc).
  apply find_some in E.
  destruct E as (Hin & Et).
  rewrite -> has_same_tid_true in Et.
  rewrite -> in_flat_map in Hin.
  destruct Hin as (ch & Hin_ch & Hin).

  (* tc_rootclk res --> getclk t ch *)
  pose proof (tid_nodup_find_self (tc_flatten ch)) as Hres_ch.
  removehead Hres_ch.
  2: eapply tid_nodup_chn_ch; eauto; intuition.
  rewrite -> List.Forall_forall in Hres_ch.
  specialize (Hres_ch _ Hin).
  assert (tc_rootclk res = tc_getclk t ch) as Eclk_ch.
  1: subst t; unfold tc_getclk, tc_getnode; now rewrite -> Hres_ch.
  rewrite -> Eclk_ch in Hlt.
  pose proof (tid_nodup_chn_ch _ (proj2 Hnodup)) as Hnodup_chn'.
  rewrite -> Foralltc_cons_iff in Hdmono.
  destruct Hdmono as (Hdmono & Hdmono_chn').
  rewrite -> List.Forall_forall in IH, Hdmono_chn'.

  (* show that "tc_rootclk ch < tc_getclk (tc_roottid ch) tc" with dmono *)
  destruct (tc_rootclk ch <=? tc_getclk (tc_roottid ch) tc) eqn:Eclk_le_ch.
  1:{
    apply Nat.leb_le in Eclk_le_ch.
    specialize (Hdmono_chn' _ Hin_ch).
    apply Foralltc_self in Hdmono_chn'.
    destruct ch as [(v, clk_v, ?) ?].
    simpl in Eclk_le_ch, Hdmono_chn'.
    specialize (Hdmono_chn' Eclk_le_ch).
    apply tc_ge_all_getclk_ge with (t:=t) in Hdmono_chn'.
    lia.
  }
  apply Nat.leb_gt in Eclk_le_ch.
  specialize (IH _ Hin_ch (Hnodup_chn' _ Hin_ch) _ (Hdmono_chn' _ Hin_ch) Eclk_le_ch _ Hlt).
  rewrite <- tc_getnode_in_iff.
  rewrite <- tc_getnode_subtc_iff in IH.
  apply map_flat_map_In.
  exists (tc_get_updated_nodes_join_degen tc ch).
  split; auto.
  apply in_map, filter_In.
  split; auto.
  apply negb_true_iff.
  now apply Nat.leb_gt.
Qed.

(* the only shape condition making sense here is tid_nodup, and the only respect condition is dmono *)
(*
(* FIXME: broken. fix later? *)
Lemma tc_attach_nodes_degen_tid_nodup tc tc' 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) (Hnodup' : NoDup (map tc_roottid (tc_flatten tc')))
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc')
  (Hdmono: Foralltc (dmono_single tc) tc') :
  NoDup (map tc_roottid (tc_flatten (tc_attach_nodes 
    (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join_degen tc tc')) tc)) 
    (tc_get_updated_nodes_join_degen tc tc')))).
Proof.
  pose proof (tc_attach_nodes_result 
    (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join_degen tc tc')) tc))
    (tc_get_updated_nodes_join_degen tc tc')) as Hso.
  remember (tc_get_updated_nodes_join_degen tc tc') as prefix_tc' eqn:Eprefix.
  destruct (tc_detach_nodes (tc_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
  simpl in Hso |- *.
  pose proof (tc_get_updated_nodes_join_degen_is_prefix tc tc') as Hprefix.
  rewrite <- Eprefix in Hprefix.
  pose proof (tid_nodup_prefix_preserve _ _ Hprefix Hnodup') as Hnodup_pf.
  assert (forest = snd (tc_detach_nodes (tc_flatten prefix_tc') tc)) as Eforest by now rewrite -> Edetach.
  pose proof (tc_detach_nodes_tid_nodup (tc_flatten prefix_tc') tc Hnodup) as Hnodup_forest.
  rewrite -> Edetach in Hnodup_forest.
  simpl in Hnodup_forest.

  eapply simple_overlaytc_nodup.
  2: apply Hso.
  3: assumption.
  - intros t.
    simpl.
    destruct (find (has_same_tid t) forest) as [ res | ] eqn:E.
    2: simpl; constructor.
    apply find_some in E.
    destruct E as (E & _).
    apply proj1, tid_nodup_chn_ch with (ch:=res) in Hnodup_forest.
    2: assumption.
    destruct res.
    now apply NoDup_cons_iff in Hnodup_forest.
  - pose proof (tc_detach_nodes_forest_recombine _ _ Hnodup Hnodup_pf) as Hperm.
    rewrite <- Eforest in Hperm.
    eapply Permutation.Permutation_NoDup.
    1: apply Permutation.Permutation_map, Permutation.Permutation_flat_map, Hperm.
    now apply tid_nodup_root_chn_split.
  - intros t H t' Hres.
    destruct (find (has_same_tid t') forest) as [ [ni chn] | ] eqn:E.
    2: auto.
    simpl in Hres.
    (* cannot find in children *)
    apply find_some in E.
    destruct E as (Hin & E).
    rewrite -> has_same_tid_true in E.
    subst forest.
    (* pose proof Hin as Hsnd. *)
    pose proof (tc_detach_nodes_snd2fst (tc_flatten prefix_tc') tc) as Hsnd2fst.
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
Qed.

Lemma tc_attach_nodes_degen_dmono tc tc' 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) (Hnodup' : NoDup (map tc_roottid (tc_flatten tc')))
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc')
  (Hdmono: Foralltc (dmono_single tc) tc') tc_larger 
    (Hdmono1: Foralltc (dmono_single tc_larger) tc)
    (Hdmono2: Foralltc (dmono_single tc_larger) tc') :
  Foralltc (dmono_single tc_larger) (tc_attach_nodes 
    (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join_degen tc tc')) tc)) 
    (tc_get_updated_nodes_join_degen tc tc')).
Proof.
  pose proof (tc_attach_nodes_result 
    (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join_degen tc tc')) tc))
    (tc_get_updated_nodes_join_degen tc tc')) as Hso.
  remember (tc_get_updated_nodes_join_degen tc tc') as prefix_tc' eqn:Eprefix.
  destruct (tc_detach_nodes (tc_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
  simpl in Hso |- *.
  pose proof (tc_get_updated_nodes_join_degen_is_prefix tc tc') as Hprefix.
  rewrite <- Eprefix in Hprefix.
  assert (forest = snd (tc_detach_nodes (tc_flatten prefix_tc') tc)) as Eforest by now rewrite -> Edetach.

  revert Hso.
  apply dmono_simple_overlaytc_pre with (Q:=fun t => tc_getclk t tc).
  - intros t.
    destruct (find (has_same_tid t) forest) as [ [(t', clk, aclk) chn] | ] eqn:E.
    2:{
      exists 0.
      now apply tc_respect_nochn_trivial.
    }
    simpl.
    apply find_some in E.
    rewrite -> has_same_tid_true in E.
    simpl in E.
    destruct E as (Hin & <-).
    (* unify getclk t tc and clk ... slightly troublesome *)
    pose proof (tc_detach_nodes_snd_is_subprefix (tc_flatten prefix_tc') tc) as Hsnd2pf.
    rewrite <- Eforest, -> List.Forall_forall in Hsnd2pf.
    specialize (Hsnd2pf _ Hin).
    destruct Hsnd2pf as (sub & Hin_sub & E).
    pose proof (prefixtc_rootinfo_same _ _ E) as Einfo.
    pose proof (tid_nodup_find_self_sub _ Hnodup _ Hin_sub) as Hres.
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
    exists aclk.
    rewrite <- Foralltc_idempotent, -> Foralltc_Forall_subtree, -> List.Forall_forall in Hdmono1.
    specialize (Hdmono1 _ Hin_sub).
    eapply dmono_prefix_preserve; eauto.
  - eapply dmono_prefix_preserve; eauto.
  - pose proof (tc_get_updated_nodes_join_degen_shape _ _ Hroot_clk_le) as H.
    subst prefix_tc'.
    eapply Foralltc_impl.
    2: apply H.
    simpl.
    lia.
Qed.
*)
Definition tc_join_degen tc tc' :=
  let: mkInfo z' clk_z' aclk_z' := tc_rootinfo tc' in
  if clk_z' <=? (tc_getclk z' tc)
  then tc
  else 
    let: subtree_tc' := tc_get_updated_nodes_join_degen tc tc' in
    let: (pivot, forest) := tc_detach_nodes (tc_flatten subtree_tc') tc in
    let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
    let: Node info_z chn_z := pivot in 
    Node info_z ((Node (mkInfo w clk_w (info_clk info_z)) chn_w) :: chn_z).

Fixpoint tc_eraseaclk (tc : @treeclock thread) := 
  let: Node (mkInfo u clk _) chn := tc in Node (mkInfo u clk 0) (map tc_eraseaclk chn).

End Degenerated_TreeClock.
