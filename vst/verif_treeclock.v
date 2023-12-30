Require Import VST.floyd.proofauto.
Require Import arboreta.clocks.treeclock.
From arboreta.vst Require Import treeclock_clight util_vst array_support util_treeclock.
From arboreta.utils Require Import util libtac.

Local Ltac intuition_solver ::= auto.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_clock := Tstruct _Clock noattr.
Definition t_struct_node := Tstruct _Node noattr.
Definition t_struct_treeclock := Tstruct _TreeClock noattr.

(* this is hard to use since it needs to be unfolded every time *)
(* Definition is_pos_tint z : Prop := 0 <= z <= Int.max_signed. *)

Definition clock_payload (clk aclk : Z) : reptype t_struct_clock :=
  (Vint (Int.repr clk), Vint (Int.repr aclk)).

Definition clock_rep (clk aclk : Z) (p : val) : mpred :=
  (* FIXME: why there are these two constraints? *)
  !! (0 <= clk <= Int.max_signed) && !! (0 <= aclk <= Int.max_signed) &&
  data_at Tsh t_struct_clock (clock_payload clk aclk) p.

Definition node_payload (next prev par headch : Z) : reptype t_struct_node :=
  (Vint (Int.repr next), 
    (Vint (Int.repr prev), 
      (Vint (Int.repr par), Vint (Int.repr headch)))).

Definition node_rep (next prev par headch : Z) (p : val) : mpred :=
  data_at Tsh t_struct_node (node_payload next prev par headch) p.

Definition tc_rootclk_proj (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  nth_error l (tr_rootid tc) = Some (clock_payload (Z.of_nat (tc_rootclk tc)) (Z.of_nat (tc_rootaclk tc))).

Definition is_tc_clockarray_proj (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  Eval unfold tc_rootclk_proj in Foralltr (tc_rootclk_proj l) tc.

Definition default_clockstruct := clock_payload 0%Z 0%Z.

(*
  Here, there is a choice between "nth_error" and "Znth". 
  For now, the choice is to make more use of "nth_error", since there is no counterpart 
    like "Znth_error"; but for the array part, we will switch to "Znth" since it is 
    more commonly used in array access. 
  For length, we try consistently using "Zlength". 
*)

Definition clockarray_emptypart (l : list (reptype t_struct_clock)) (tcs : list treeclock) : Prop :=
  forall n np, find (has_same_id n) tcs = None -> nth_error l n = Some np -> 
    np = default_clockstruct.

(* TODO could also be per-field description so that there will be only one branch *)

(* typically requires that default_nodefield <= 0 *)
Definition default_nodefield := (-1)%Z.

Definition default_nodestruct := node_payload default_nodefield default_nodefield default_nodefield default_nodefield.

Definition tcs_head_Z_default (dft : Z) (tcs : list treeclock) : Z := 
  match tcs with nil => dft | ch :: _ => Z.of_nat (tr_rootid ch) end.

Definition tcs_head_Z := tcs_head_Z_default default_nodefield.

Definition tc_headch_Z (tc : treeclock) : Z := tcs_head_Z (tr_rootchn tc).

Global Arguments tcs_head_Z_default dft tcs : simpl nomatch.
(* Global Arguments tcs_head_Z tcs : simpl nomatch. *)
Global Arguments tcs_head_Z _ /.
Global Arguments tc_headch_Z !tc.

Fact tcs_head_Z_default_rev_last dft tcs :
  tcs_head_Z_default dft (rev tcs) = 
  match list.last tcs with Some ch => Z.of_nat (tr_rootid ch) | None => dft end.
Proof.
  destruct (list.last tcs) as [ ch | ] eqn:E.
  - apply list.last_Some in E. destruct E as (l' & ->).
    rewrite -> rev_app_distr. now simpl.
  - apply list.last_None in E. now subst.
Qed.

Fact tcs_head_Z_default_rev_last' dft ch tcs :
  tcs_head_Z_default dft (rev (tcs ++ (ch :: nil))) = Z.of_nat (tr_rootid ch).
Proof. now rewrite tcs_head_Z_default_rev_last, list.last_snoc. Qed.

Fact tcs_head_Z_default_notnil dft tcs tcs' (H : tcs <> nil) :
  tcs_head_Z_default dft (tcs ++ tcs') = tcs_head_Z_default dft tcs.
Proof. now destruct tcs. Qed.

Definition is_tc_nodearray_proj_chnaux (par : nat) (l : list (reptype t_struct_node)) :
  forall (prev : Z) (chn : list treeclock), Prop := 
  fix aux prev chn {struct chn} : Prop := 
  match chn with
  | nil => True
  | ch :: chn' => 
    nth_error l (tr_rootid ch) = 
    Some (node_payload (match chn' with nil => default_nodefield | ch' :: _ => (Z.of_nat (tr_rootid ch')) end) 
      prev (Z.of_nat par) (tc_headch_Z ch)) /\
    aux (Z.of_nat (tr_rootid ch)) chn'
  end.

Definition is_tc_nodearray_proj_aux (l : list (reptype t_struct_node)) (tc : treeclock): Prop :=
  is_tc_nodearray_proj_chnaux (tr_rootid tc) l default_nodefield (tr_rootchn tc).

Global Arguments is_tc_nodearray_proj_aux _ _/.

Definition is_tc_nodearray_proj_root (l : list (reptype t_struct_node)) (tc : treeclock): Prop :=
  nth_error l (tr_rootid tc) = 
  Some (node_payload default_nodefield default_nodefield default_nodefield (tc_headch_Z tc)).

Definition is_tc_nodearray_proj (l : list (reptype t_struct_node)) (tc : treeclock) : Prop :=
  Foralltr (is_tc_nodearray_proj_aux l) tc.

(* for the whole tree *)
Definition is_tc_nodearray_proj_full (l : list (reptype t_struct_node)) (tc : treeclock) : Prop :=
  is_tc_nodearray_proj_root l tc /\ is_tc_nodearray_proj l tc.

Definition nodearray_emptypart (l : list (reptype t_struct_node)) (tcs : list treeclock) : Prop :=
  forall n np, find (has_same_id n) tcs = None -> nth_error l n = Some np -> np = default_nodestruct.

Definition treeclock_payload (dim rootid : Z) (clockarr nodearr : val) 
  (stk : val) (top : Z) : reptype t_struct_treeclock :=
  (Vint (Int.repr dim), (Vint (Int.repr rootid), (clockarr, (nodearr, 
    (stk, Vint (Int.repr top)))))).

(* separation logic style predicate *)

(* for segmentation purpose, need to bound both beginning and end *)
Definition tc_chn_rep (dim : Z) (plnode plclk : val) (par : nat) (lst : Z) : 
  forall (prev : Z) (chn : list treeclock), mpred := 
  fix aux prev chn {struct chn} : mpred := 
  match chn with
  | nil => emp
  | ch :: chn' => 
    (* may be redundant? *)
    (* TODO 0 <= may be redundant? *)
    !! (0 <= Z.of_nat (tr_rootid ch) < dim) &&
    (* by design, this should be bundled with clock_rep *)
    (*     
    !! (0 <= Z.of_nat (tc_rootclk ch) <= Int.max_signed) &&
    !! (0 <= Z.of_nat (tc_rootaclk ch) <= Int.max_signed) && 
    *)
    (clock_rep (Z.of_nat (tc_rootclk ch)) (Z.of_nat (tc_rootaclk ch)) 
      (offset_val (sizeof t_struct_clock * Z.of_nat (tr_rootid ch)) plclk) *
    node_rep 
      (tcs_head_Z_default lst chn')
      (* (match chn' with nil => lst | ch' :: _ => (Z.of_nat (tr_rootid ch')) end)  *)
      prev (Z.of_nat par) (tc_headch_Z ch)
      (offset_val (sizeof t_struct_node * Z.of_nat (tr_rootid ch)) plnode) *
    aux (Z.of_nat (tr_rootid ch)) chn')%logic
  end.

Fixpoint tc_rep_noroot (dim : Z) (plnode plclk : val) (tc : treeclock) : mpred :=
  let 'Node ni chn := tc in
  (tc_chn_rep dim plnode plclk (info_tid ni) default_nodefield default_nodefield chn *
  (* TODO is fold proper here? or use allp? *)
  fold_right_sepcon (map (tc_rep_noroot dim plnode plclk) chn))%logic.

Definition tc_root_rep (dim : Z) (plnode plclk : val) (tc : treeclock) : mpred :=
  (* may be redundant? *)
    (* TODO 0 <= may be redundant? *)
  !! (0 <= Z.of_nat (tr_rootid tc) < dim) &&
  (clock_rep (Z.of_nat (tc_rootclk tc)) (Z.of_nat (tc_rootaclk tc)) 
    (offset_val (sizeof t_struct_clock * Z.of_nat (tr_rootid tc)) plclk) *
  node_rep default_nodefield default_nodefield default_nodefield (tc_headch_Z tc)
    (offset_val (sizeof t_struct_node * Z.of_nat (tr_rootid tc)) plnode))%logic.

Definition tc_subroot_rep (dim : Z) (plnode plclk : val) (tc : treeclock) z1 z2 z3 : mpred :=
  (* may be redundant? *)
    (* TODO 0 <= may be redundant? *)
  !! (0 <= Z.of_nat (tr_rootid tc) < dim) &&
  (clock_rep (Z.of_nat (tc_rootclk tc)) (Z.of_nat (tc_rootaclk tc)) 
    (offset_val (sizeof t_struct_clock * Z.of_nat (tr_rootid tc)) plclk) *
  node_rep z1 z2 z3 (tc_headch_Z tc)
    (offset_val (sizeof t_struct_node * Z.of_nat (tr_rootid tc)) plnode))%logic.

Definition tc_rep (dim : Z) (plnode plclk : val) (tc : treeclock) : mpred :=
  (tc_root_rep dim plnode plclk tc * tc_rep_noroot dim plnode plclk tc)%logic.

(* TODO the representation of unused_bag_rep is debatable *)

(* Definition unused_bag_rep (dim : Z) (plnode plclk : val) (l : list nat) : mpred := *)
Definition unused_bag_rep (dim : Z) (plnode plclk : val) (tcs : list treeclock) : mpred :=
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock default_clockstruct (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node default_nodestruct (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic
    (* (filter (fun i => negb (ssrbool.isSome (find (has_same_id (Z.to_nat i)) tcs))) (upto (Z.to_nat dim)))). *)
    (filter (fun t => negb (ssrbool.isSome (find (has_same_id t) tcs))) 
      (map Z.to_nat (upto (Z.to_nat dim))))).
    (* (ListSet.set_diff Z.eq_dec (upto (Z.to_nat dim)) (map Z.of_nat l))). *)

(* sometimes the treeclock corresponds to an empty tree, but do not consider it for now *)

(* factor the dim out; it should not change during the operation? *)
(* seems like top should be consistently -1 *)
Definition treeclock_rep (dim : Z) (tc : treeclock) (plclk plnode : val) 
  (plstk : val) p : mpred :=
  (* EX dim : Z,  *)
  (* EX lclk_ptrs : list val,  *)
  (* EX lnode_ptrs : list val,  *)
  (* TODO should this be raw (reptype t_struct_clock) or the result of some (map list)? *)
  EX lclk : list (reptype t_struct_clock), 
  EX lnode : list (reptype t_struct_node), 

  EX lstk : list val, 

  (* TODO the clk and aclk must become bounded somewhere.
      if they are bounded with a Foralltr, then we may simply bound tid as well 
        so that we do not need the tid_bounded lemmas and nth_error 
    but for now, we only bound clk and aclk to avoid premature optimization
  *)
  !! (Foralltr (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) &&
  (* this is necessary in the current setting, since the root may not appear in the node array *)
  !! (Z.of_nat (tr_rootid tc) < dim) &&
  (* !! (Zlength lclk_ptrs = dim) &&  *)
  !! (Zlength lclk = dim) &&
  (* !! (Zlength lnode_ptrs = dim) &&  *)
  !! (Zlength lnode = dim) &&
  !! (Zlength lstk = dim) &&
  !! (is_tc_clockarray_proj lclk tc) && !! (clockarray_emptypart lclk (tr_flatten tc)) &&
  !! (is_tc_nodearray_proj_full lnode tc) && !! (nodearray_emptypart lnode (tr_flatten tc)) &&
  (* TODO this should be subsumed? *)
  (* !! (Foralltr (fun t => Z.of_nat (tr_rootid t) < dim) tc) && *)
  data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tr_rootid tc)) 
    plclk plnode plstk (-1)) p * 
  data_at Tsh (tarray t_struct_clock dim) lclk plclk *
  data_at Tsh (tarray t_struct_node dim) lnode plnode *
  (* data_at Tsh (tarray tshort dim) lstk plstk. *)
  data_at Tsh (tarray tint dim) lstk plstk.

(* simple bounded properties *)
(* TODO should I use Z.< instead? *)

Fact is_tc_nodearray_proj_chnaux_tid_bounded lnode par prev chn (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn) :
  Forall (fun tc' => Z.of_nat (tr_rootid tc') < Zlength lnode) chn.
Proof.
  revert lnode prev Hproj.
  induction chn as [ | ch chn IH ]; intros; constructor; simpl in Hproj.
  - now apply proj1, nth_error_some_inrange_Z in Hproj.
  - eapply IH. apply (proj2 Hproj).
Qed.

Fact is_tc_nodearray_proj_tid_bounded lnode tc (Hproj : is_tc_nodearray_proj lnode tc)
  (HH : Z.of_nat (tr_rootid tc) < Zlength lnode) :
  Foralltr (fun tc' => Z.of_nat (tr_rootid tc') < Zlength lnode) tc.
Proof.
  destruct tc as [(u, clk, aclk) chn].
  simpl in HH.
  rewrite Foralltr_cons_iff'. split. 1: simpl; auto.
  rewrite <- Foralltr_Forall_chn_comm.
  eapply Foralltr_impl. 2: apply Hproj.
  intros ? H. simpl in H. revert H. now apply is_tc_nodearray_proj_chnaux_tid_bounded. 
Qed.

(* TODO is the exists a good design or not? *)

Definition node_struct_regular_wk dim np : Prop :=
  exists z1 z2 z3 z4, 
    np = node_payload z1 z2 z3 z4 /\
    default_nodefield <= z1 < dim /\
    default_nodefield <= z2 < dim /\
    default_nodefield <= z3 < dim /\
    default_nodefield <= z4 < dim.

(* generally, par will not be default *)
Definition node_struct_regular dim np : Prop :=
  exists z1 z2 z3 z4, 
    np = node_payload z1 z2 z3 z4 /\
    default_nodefield <= z1 < dim /\
    default_nodefield <= z2 < dim /\
    default_nodefield < z3 < dim /\
    default_nodefield <= z4 < dim.

Fact node_struct_regular_weaken dim np : 
  node_struct_regular dim np -> node_struct_regular_wk dim np.
Proof.
  intros (z1 & z2 & z3 & z4 & -> & ? & ? & ? & ?).
  hnf. exists z1, z2, z3, z4. unfold default_nodefield in *. intuition lia.
Qed.

Fact is_tc_nodearray_proj_chnaux_regular lnode par prev chn (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn)
  (* dim (Hlen : Zlength lnode = dim)  *)
  (Hu : Z.of_nat par < Zlength lnode) (Hprev : default_nodefield <= prev < Zlength lnode)
  (Hchn : Forall (fun ch => default_nodefield <= tc_headch_Z ch < Zlength lnode) chn) :
  Forall (fun tc' => node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tr_rootid tc')) lnode)) chn.
Proof.
  revert prev lnode Hu Hproj Hprev Hchn. 
  induction chn as [ | ch chn IH ]; intros; constructor; simpl in Hproj.
  - hnf.
    match type of Hproj with _ = Some (node_payload ?z1 ?z2 ?z3 ?z4) /\ _ => 
      exists z1, z2, z3, z4 end.
    split. 1: now apply proj1, nth_error_Znth_result in Hproj.
    split. 2: split; auto. 2: split; [ unfold default_nodefield; lia | now inversion Hchn ].
    destruct chn. 
    2: apply proj2, is_tc_nodearray_proj_chnaux_tid_bounded in Hproj.
    2: rewrite -> Forall_cons_iff in Hproj; destruct Hproj as (Hproj & _).
    all: unfold default_nodefield; lia.
  - destruct Hproj as (Htmp & Hproj). apply nth_error_some_inrange_Z in Htmp.
    inversion_clear Hchn.
    apply IH with (prev:=(Z.of_nat (tr_rootid ch))); auto; unfold default_nodefield; try lia; try tauto.
Qed. 

Fact is_tc_nodearray_proj_headch_inrange lnode tc (Hproj : is_tc_nodearray_proj lnode tc) :
  default_nodefield <= tc_headch_Z tc < Zlength lnode.
Proof.
  pose proof (Zlength_nonneg lnode).
  destruct tc as [ ? [ | ] ]; cbn; unfold default_nodefield; simpl; try lia.
  apply Foralltr_self in Hproj. 
  apply is_tc_nodearray_proj_chnaux_tid_bounded in Hproj; auto.
  inversion_clear Hproj. lia.
Qed.

(* leave out the root is more convenient for this proof *)
Fact is_tc_nodearray_proj_regular_chn lnode tc (Hproj : is_tc_nodearray_proj lnode tc)
  (Hu : Z.of_nat (tr_rootid tc) < (Zlength lnode)) :
  Forall (Foralltr (fun tc' => node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tr_rootid tc')) lnode))) (tr_rootchn tc).
Proof.
  revert lnode Hproj Hu.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  simpl in Hu.
  apply Foralltr_cons_iff in Hproj. destruct Hproj as (Hchn & Hproj). simpl in Hchn. 
  simpl in Hchn.
  pose proof Hchn as Hchn'. apply is_tc_nodearray_proj_chnaux_tid_bounded in Hchn'.
  apply is_tc_nodearray_proj_chnaux_regular in Hchn; simpl; auto.
  2: unfold default_nodefield; lia.
  2:{
    rewrite -> Forall_forall in Hproj, Hchn' |- *. 
    intros ch Hin. specialize (Hproj _ Hin). specialize (Hchn' _ Hin).
    now apply is_tc_nodearray_proj_headch_inrange in Hproj.
  }
  rewrite -> Forall_forall in IH, Hproj, Hchn, Hchn' |- *.
  intros ch Hin. specialize (Hproj _ Hin). specialize (Hchn _ Hin). specialize (Hchn' _ Hin).
  destruct ch as [(v, ?, ?) chn_ch] eqn:Ech. simpl in *.
  constructor; simpl; auto.
  replace chn_ch with (tr_rootchn ch) by now rewrite Ech.
  apply IH; rewrite Ech; auto.
Qed.

Fact is_tc_nodearray_proj_regular lnode tc (Hproj : is_tc_nodearray_proj lnode tc)
  (* dim (Hlen : Zlength lnode = dim)  *)
  (Hu : Z.of_nat (tr_rootid tc) < (Zlength lnode))
  (HH : node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tr_rootid tc)) lnode)) :
  Foralltr (fun tc' => node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tr_rootid tc')) lnode)) tc.
Proof.
  destruct tc as [(u, ?, ?) chn] eqn:Etc. simpl in *.
  constructor; simpl; auto.
  replace chn with (tr_rootchn tc) by now rewrite Etc.
  apply is_tc_nodearray_proj_regular_chn; rewrite Etc; auto.
Qed.

Fact is_tc_nodearray_proj_full_regular_wk lnode tc (Hproj : is_tc_nodearray_proj_full lnode tc) :
  (* dim (Hlen : Zlength lnode = dim)  *)
  (* (Hu : Z.of_nat (tr_rootid tc) < (Zlength lnode))  *)
  Foralltr (fun tc' => node_struct_regular_wk (Zlength lnode) (Znth (Z.of_nat (tr_rootid tc')) lnode)) tc.
Proof.
  (* eapply Foralltr_impl. 1: intros ?; apply node_struct_regular_weaken. *)
  destruct Hproj as (Hroot & Hproj). hnf in Hroot.
  destruct tc as [(u, ?, ?) chn] eqn:Etc. simpl in *.
  constructor.
  - simpl. apply nth_error_Znth_result in Hroot.
    hnf. do 4 eexists. rewrite -> Hroot. split; [ reflexivity | ].
    apply is_tc_nodearray_proj_headch_inrange in Hproj.
    pose proof (Zlength_nonneg lnode).
    unfold default_nodefield. intuition lia.
  - eapply Forall_impl.
    + intros ? HH; eapply Foralltr_impl.
      intros ?; apply node_struct_regular_weaken.
      apply HH.
    + replace chn with (tr_rootchn tc) by now rewrite Etc.
      apply is_tc_nodearray_proj_regular_chn.
      * now subst tc.
      * rewrite Etc. simpl. now apply nth_error_some_inrange_Z in Hroot.
Qed.

Fact nodearray_proj_regular lnode tc (Hproj1 : is_tc_nodearray_proj_full lnode tc) 
  (Hproj2 : nodearray_emptypart lnode (tr_flatten tc)) :
  (* dim (Hlen : Zlength lnode = dim)  *)
  Forall (node_struct_regular_wk (Zlength lnode)) lnode.
Proof.
  (* revert lnode Hproj1 Hproj2.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros. *)
  apply Forall_Znth.
  intros n Hr. destruct (tr_getnode (Z.to_nat n) tc) as [ res | ] eqn:E.
  - apply is_tc_nodearray_proj_full_regular_wk in Hproj1.
    apply (tr_getnode_res_Foralltr _ Hproj1) in E.
    destruct E as (E & Eid). rewrite -> Eid, -> Z2Nat.id in E; auto; try lia.
  - destruct (nth_error lnode (Z.to_nat n)) eqn:Ee.
    2:{ apply nth_error_None in Ee. rewrite <- ZtoNat_Zlength in Ee. lia. }
    pose proof Ee as Ee'.
    apply nth_error_Znth_result in Ee'. rewrite -> Z2Nat.id in Ee'; auto; try lia.
    rewrite -> Ee'.
    apply Hproj2 in Ee; auto. subst.
    hnf. do 4 eexists. split; [ reflexivity | ].
    unfold default_nodefield. intuition lia.
Qed.

(* but what if one only wants to read the parent field? *)
(* FIXME: what is the relationship between this and "read_correct"? here proved a simple specific version ... *)
(* TODO these seem like template properties. can they be automatically derived? 
    or, at least obtain some common proof patterns ... *)

Definition node_struct_get_headch (np : reptype t_struct_node) :=
  match np with (_, (_, (_, res))) => res end.

Definition node_struct_get_par (np : reptype t_struct_node) :=
  match np with (_, (_, (res, _))) => res end.

Definition is_tc_nodearray_proj_onlyheadch lnode tc :=
  node_struct_get_headch (Znth (Z.of_nat (tr_rootid tc)) lnode) = 
    Vint (Int.repr (tc_headch_Z tc)).

Definition is_tc_nodearray_proj_onlypar_aux par lnode chn :=
  Forall (fun tc0 => node_struct_get_par (Znth (Z.of_nat (tr_rootid tc0)) lnode) = 
    Vint (Int.repr (Z.of_nat par))) chn.

Definition is_tc_nodearray_proj_onlypar lnode tc :=
  Foralltr (fun tc' => is_tc_nodearray_proj_onlypar_aux (tr_rootid tc') lnode (tr_rootchn tc')) tc.

Fact is_tc_nodearray_proj_onlyheadch_chn_derived par lnode chn :
  forall prev (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn), 
  Forall (is_tc_nodearray_proj_onlyheadch lnode) chn.
Proof.
  induction chn as [ | ch chn IH ]; intros; simpl in Hproj |- *; constructor.
  - apply proj1, nth_error_Znth_result in Hproj.
    hnf. unfold node_struct_get_headch.
    rewrite Hproj.
    reflexivity.
  - eapply IH.
    apply (proj2 Hproj).
Qed.

Fact is_tc_nodearray_proj_onlyheadch_derived lnode tc
  (Hproj : is_tc_nodearray_proj lnode tc) 
  (H : is_tc_nodearray_proj_onlyheadch lnode tc) : 
  Foralltr (is_tc_nodearray_proj_onlyheadch lnode) tc.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  hnf in Hproj |- *.
  rewrite Foralltr_cons_iff in Hproj |- *.
  constructor; try assumption.
  simpl in Hproj.
  destruct Hproj as (Hq%is_tc_nodearray_proj_onlyheadch_chn_derived & Hproj).
  eapply Forall_impl_impl in Hproj.
  2: apply IH.
  now apply Forall_impl_impl with (P:=is_tc_nodearray_proj_onlyheadch lnode) in Hproj.
Qed.

Fact is_tc_nodearray_proj_onlyheadch_derived_full lnode tc
  (Hproj : is_tc_nodearray_proj_full lnode tc) :
  Foralltr (is_tc_nodearray_proj_onlyheadch lnode) tc.
Proof.
  destruct Hproj as (Hroot & Hproj).
  apply is_tc_nodearray_proj_onlyheadch_derived; try assumption.
  hnf.
  apply nth_error_Znth_result in Hroot.
  rewrite Hroot.
  reflexivity.
Qed.

Fact is_tc_nodearray_proj_onlypar_aux_derived par lnode chn :
  forall prev (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn), 
  is_tc_nodearray_proj_onlypar_aux par lnode chn.
Proof.
  induction chn as [ | ch chn IH ]; intros; simpl in Hproj |- *; constructor.
  - apply proj1, nth_error_Znth_result in Hproj.
    unfold node_struct_get_par.
    rewrite Hproj.
    reflexivity.
  - eapply IH.
    apply (proj2 Hproj).
Qed.

Fact is_tc_nodearray_proj_onlypar_derived lnode tc
  (Hproj : is_tc_nodearray_proj lnode tc) : is_tc_nodearray_proj_onlypar lnode tc.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  hnf in Hproj |- *.
  rewrite Foralltr_cons_iff in Hproj |- *.
  simpl in Hproj |- *.
  constructor.
  - eapply is_tc_nodearray_proj_onlypar_aux_derived, (proj1 Hproj).
  - eapply Forall_impl_impl. 
    1: apply IH.
    apply (proj2 Hproj).
Qed.

Fact is_tc_nodearray_proj_onlypar_prefix_preserve lnode tc tc'
  (Hprefix : prefixtr tc tc')
  (Hproj : is_tc_nodearray_proj_onlypar lnode tc') : is_tc_nodearray_proj_onlypar lnode tc.
Proof.
  revert tc Hprefix Hproj.
  induction tc' as [ni' chn' IH] using tree_ind_2; intros.
  destruct tc as [ni chn].
  apply prefixtr_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  subst ni.
  hnf in Hproj |- *.
  rewrite -> Foralltr_cons_iff in Hproj |- *.
  simpl in Hproj |- *.
  destruct Hproj as (Hself & Hproj).
  split.
  - hnf in Hself |- *.
    (* TODO tedious ad hoc reasoning *)
    pose proof (List.Forall_map tr_rootid
      (fun t => node_struct_get_par (Znth (Z.of_nat t) lnode) = 
        Vint (Int.repr (Z.of_nat (info_tid ni'))))) as Htmp.
    simpl in Htmp.
    rewrite <- Htmp in Hself |- *.
    (* FIXME: replace this with some Forall2_?? *)
    replace (map tr_rootid chn) with (map tr_rootid chn_sub).
    2:{
      clear -Hcorr.
      induction Hcorr; simpl; try reflexivity.
      f_equal; try assumption.
      symmetry.
      now apply tr_rootinfo_id_inj, prefixtr_rootinfo_same.
    }
    apply sublist_map with (f:=tr_rootid) in Hsub.
    revert Hself.
    now apply sublist_Forall.
  - eapply sublist_Forall in Hproj, IH.
    2-3: apply Hsub.
    pose proof (Forall2_forall_exists_l Hcorr) as Hcorr_in.
    rewrite -> List.Forall_forall in IH, Hproj |- *.
    intros ch Hin.
    destruct (Hcorr_in _ Hin) as (ch' & Hin' & Hprefix).
    specialize (IH _ Hin' _ Hprefix).
    specialize (Hproj _ Hin').
    eapply IH; eauto.
Qed.

Fact is_tc_nodearray_proj_onlypar_read_parent lnode tc (Hproj : is_tc_nodearray_proj_onlypar lnode tc) :
  forall l (Hnotnil : l <> nil) sub (H : tr_locate tc l = Some sub), 
  base.fmap (fun tc0 => Vint (Int.repr (Z.of_nat (tr_rootid tc0)))) (tr_locate tc (removelast l)) = 
    Some (node_struct_get_par (Znth (Z.of_nat (tr_rootid sub)) lnode)).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  destruct l as [ | x l ]; try contradiction.
  simpl in H.
  destruct (nth_error chn x) as [ ch | ] eqn:Enth; try discriminate.
  apply exists_last in Hnotnil.
  destruct Hnotnil as (l' & x' & E).
  rewrite E, removelast_last.
  destruct l' as [ | y' l' ].
  - simpl. simpl in E. destruct l; try discriminate. injection E as <-.
    simpl in H. injection H as <-.
    eapply Foralltr_self, Forall_forall in Hproj.
    2: simpl; eapply nth_error_In, Enth.
    rewrite Hproj. reflexivity.
  - rewrite <- app_comm_cons in E. injection E as <-.
    subst l. simpl.
    rewrite Enth.
    apply nth_error_In in Enth.
    apply Foralltr_chn in Hproj.
    simpl in Hproj.
    rewrite -> Forall_forall in Hproj, IH.
    replace l' with (removelast (l' ++ (x' :: nil))) in |- * by now rewrite removelast_last.
    apply IH; try assumption.
    2: now destruct l'.
    now apply Hproj.
Qed.

Fact is_tc_clockarray_proj_nth lclk tc (Hproj : is_tc_clockarray_proj lclk tc) :
  Foralltr (fun tc' => (Znth (Z.of_nat (tr_rootid tc')) lclk) = 
    clock_payload (Z.of_nat (tc_rootclk tc')) (Z.of_nat (tc_rootaclk tc'))) tc.
Proof.
  eapply Foralltr_impl. 2: apply Hproj. 
  simpl. intros tc' H.
  apply List.nth_error_nth with (d:=default) in H.
  rewrite <- nth_Znth', -> H.
  reflexivity.
Qed.

Fact clockarray_proj_tc_getinfo lclk tc (Hproj1 : is_tc_clockarray_proj lclk tc) 
  (Hproj2 : clockarray_emptypart lclk (tr_flatten tc)) 
  i (Hi : 0 <= i < Zlength lclk) :
  (* Vint (Int.repr (Z.of_nat (tc_getclk (Z.to_nat i) tc))) = fst (Znth i lclk). *)
  Znth i lclk = (Vint (Int.repr (Z.of_nat (tc_getclk (Z.to_nat i) tc))), 
    Vint (Int.repr (Z.of_nat (match tr_getnode (Z.to_nat i) tc with Some res => tc_rootaclk res | None => 0%nat end)))).
Proof.
  unfold tc_getclk, tr_getnode. 
  destruct (find (has_same_id (Z.to_nat i)) (tr_flatten tc)) as [ res | ] eqn:E.
  - eapply tr_getnode_res_Foralltr in E. 2: apply Hproj1.
    simpl in E. destruct E as (Ee%nth_error_Znth_result, Eid). 
    rewrite -> Eid, -> Z2Nat.id in Ee; try lia.
    now rewrite Ee.
  - hnf in Hproj2.
    destruct (nth_error lclk (Z.to_nat i)) eqn:E'.
    2: apply nth_error_None in E'; rewrite -> Zlength_correct in Hi; lia.
    pose proof E' as E''%nth_error_Znth_result. 
    rewrite -> Z2Nat.id in E''; try lia. rewrite E''.
    apply Hproj2 in E'; auto.
Qed. 

Fact clockarray_proj_tc_getinfo' lclk tc (Hproj1 : is_tc_clockarray_proj lclk tc) 
  (Hproj2 : clockarray_emptypart lclk (tr_flatten tc)) 
  (t : nat) (Hi : Z.of_nat t < Zlength lclk) :
  Znth (Z.of_nat t) lclk = (Vint (Int.repr (Z.of_nat (tc_getclk t tc))), 
    Vint (Int.repr (Z.of_nat (match tr_getnode t tc with Some res => tc_rootaclk res | None => 0%nat end)))).
Proof. 
  eapply clockarray_proj_tc_getinfo with (i:=Z.of_nat t) in Hproj2; eauto.
  2: split; [ apply Zle_0_nat | assumption ].
  now rewrite Nat2Z.id in Hproj2.
Qed.

Fact unused_bag_rep_perm dim plnode plclk tcs1 tcs2
  (Hperm : Permutation (map tr_rootid tcs1) (map tr_rootid tcs2)) :
  unused_bag_rep dim plnode plclk tcs1 = unused_bag_rep dim plnode plclk tcs2.
Proof.
  unfold unused_bag_rep.
  erewrite -> filter_ext. 1: reflexivity.
  (* TODO awkward isSome and is_true *)
  simpl. intros a. f_equal.
  pose proof (trs_find_in_iff a tcs1) as H1.
  pose proof (trs_find_in_iff a tcs2) as H2.
  erewrite -> Permutation_in_mutual in H1. 2: apply Hperm.
  rewrite -> H1 in H2.
  now apply eq_true_iff_eq.
Qed.

Fact unused_bag_rep_alloc dim plnode plclk tcs 
  tc (H : Z.of_nat (tr_rootid tc) < dim) (Hnotin : find (has_same_id (tr_rootid tc)) tcs = None) :
  unused_bag_rep dim plnode plclk tcs = 
  (* (unused_bag_rep dim plnode plclk (tc :: tcs) * tc_root_rep dim plnode plclk tc)%logic. *)
  (unused_bag_rep dim plnode plclk (tc :: tcs) *
    data_at Tsh t_struct_clock default_clockstruct (offset_val (sizeof t_struct_clock * Z.of_nat (tr_rootid tc)) plclk) *
    data_at Tsh t_struct_node default_nodestruct (offset_val (sizeof t_struct_node * Z.of_nat (tr_rootid tc)) plnode))%logic.
Proof.
  unfold unused_bag_rep.
  simpl.
  pose proof (Permutation_upto_pick (tr_rootid tc) (Z.to_nat dim)) as Hperm.
  removehead Hperm. 2: lia.
  rewrite -> seq_upto in Hperm.
  erewrite -> fold_right_sepcon_permutation at 1.
  2: apply Permutation_map, Permutation_filter, Hperm.
  match goal with |- _ = (fold_right_sepcon ?ll * _ * _)%logic => 
    erewrite -> fold_right_sepcon_permutation with (al:=ll) end.
  2: apply Permutation_map, Permutation_filter, Hperm.
  simpl. rewrite Hnotin. simpl.
  unfold has_same_id at 2. 
  destruct (eqdec (tr_rootid tc) (tr_rootid tc)); simpl; try contradiction.
  rewrite -> sepcon_comm at 1. 
  rewrite -> sepcon_assoc at 1.
  f_equal. f_equal. f_equal.
  apply filter_ext_in_iff. intros x. rewrite -> ! in_app_iff, -> ! in_seq.
  intros HH. unfold has_same_id. destruct (eqdec (tr_rootid tc) x); try lia.
  now simpl.
Qed.

Lemma tc_chn_rep_segment plclk plnode dim par pre :
  forall lst prev ch suf, 
  tc_chn_rep dim plnode plclk par lst prev (pre ++ ch :: suf) =
  (tc_chn_rep dim plnode plclk par (Z.of_nat (tr_rootid ch)) prev pre *
    tc_subroot_rep dim plnode plclk ch 
      (tcs_head_Z_default lst suf)
      (* (match suf with nil => lst | ch' :: _ => (Z.of_nat (tr_rootid ch')) end)  *)
      (tcs_head_Z_default prev (rev pre))
      (* (match (rev pre) with nil => prev | ch' :: _ => (Z.of_nat (tr_rootid ch')) end)  *)
      (Z.of_nat par) *
    tc_chn_rep dim plnode plclk par lst (Z.of_nat (tr_rootid ch)) suf)%logic.
Proof.
  induction pre as [ | p pre IH ] using rev_ind; intros; cbn delta -[sizeof tc_headch_Z] iota beta zeta.
  - unfold tc_subroot_rep. apply pred_ext; entailer!.
  - rewrite <- app_cons_assoc, -> ! IH with (ch:=p), -> ! tcs_head_Z_default_rev_last'.
    cbn delta -[sizeof tc_headch_Z] iota beta zeta. 
    unfold tc_subroot_rep. apply pred_ext; entailer!.
Qed.

(* seems like disjointness is not needed here? *)
Lemma tc_chn_proj2rep plclk plnode lclk lnode dim par  
  (Hlenc : Zlength lclk = dim) (Hlenn : Zlength lnode = dim) :
  forall chn prev (Hchn_clk : Forall (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) chn)
  (Hprojc : Forall (is_tc_clockarray_proj lclk) chn) (* hmm *)
  (Hprojn : is_tc_nodearray_proj_chnaux par lnode prev chn),
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (Znth (Z.of_nat i) lclk) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (Znth (Z.of_nat i) lnode) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic (map tr_rootid chn)) |--
  tc_chn_rep dim plnode plclk par default_nodefield prev chn.
Proof.
  intros chn. induction chn as [ | ch chn IH ]; intros.
  - simpl. entailer.
  - cbn delta [map fold_right_sepcon] iota beta.
    rewrite Forall_cons_iff in Hchn_clk, Hprojc. simpl in Hprojn.
    destruct Hchn_clk as ((Hc1 & Hc2) & Hchn_clk), Hprojc as (Hch_c & Hprojc), 
      Hprojn as (Hch_n & Hprojn).
    specialize (IH (Z.of_nat (tr_rootid ch)) Hchn_clk Hprojc Hprojn).
    sep_apply IH. cbn delta [tc_chn_rep] iota beta.
    unfold clock_rep, node_rep.
    entailer!.
    1: apply nth_error_some_inrange_Z in Hch_n; lia.
    hnf in Hch_c. apply Foralltr_self in Hch_c.
    apply nth_error_Znth_result in Hch_c, Hch_n. rewrite Hch_c, Hch_n.
    entailer!.
Qed.

(* FIXME: much repetition in the proofs of rep2proj. need revision
  a question: is the bounding of clk really needed, as one of the !!? 
  can it be removed, since it is something already known, when given the treeclock_rep? *)

Lemma tc_chn_rep2proj plclk plnode par dim
  (* (Hcompc : field_compatible (tarray t_struct_clock dim) [] plclk)
  (Hcompn : field_compatible (tarray t_struct_node dim) [] plnode)  *)
  :
  (* this nodup may be a derived condition of fold_right_sepcon or tc_chn_rep, 
    but make it an assumption here anyway; guess would be more convenient in this case *) 
  forall chn prev (Hnodup : trs_roots_NoDupId chn), 
  tc_chn_rep dim plnode plclk par default_nodefield prev chn |--
  EX f g, 
  !! (Forall (fun sub => Z.of_nat (tr_rootid sub) < dim /\
    (Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed)) chn) &&
  !! (forall lclk, 
    Zlength lclk = dim ->
    Forall (fun i => Znth (Z.of_nat i) lclk = f (Z.of_nat i)) (map tr_rootid chn) ->
    Forall (tc_rootclk_proj lclk) chn) && (* hmm *)
  !! (forall lnode, 
    Zlength lnode = dim ->
    Forall (fun i => Znth (Z.of_nat i) lnode = g (Z.of_nat i)) (map tr_rootid chn) ->
    is_tc_nodearray_proj_chnaux par lnode prev chn) &&
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (f (Z.of_nat i)) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (g (Z.of_nat i)) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic (map tr_rootid chn)).
Proof.
  intros chn. induction chn as [ | ch chn IH ]; intros.
  1:{
    simpl. Exists (fun _ : Z => default_clockstruct) (fun _ : Z => default_nodestruct).
    entailer!.
  }
  cbn delta [map fold_right_sepcon tc_chn_rep] iota beta.
  hnf in Hnodup.
  simpl in Hnodup. rewrite -> NoDup_cons_iff in Hnodup. destruct Hnodup as (Hnotin & Hnodup).
  unfold clock_rep, node_rep.
  Intros. sep_apply IH. Intros f g.
  Exists (fun x : Z => if Z.eqb x (Z.of_nat (tr_rootid ch)) then
    (clock_payload (Z.of_nat (tc_rootclk ch)) (Z.of_nat (tc_rootaclk ch)))
    else f x)
  (fun x : Z => if Z.eqb x (Z.of_nat (tr_rootid ch)) then
    (node_payload (tcs_head_Z_default default_nodefield chn) prev (Z.of_nat par) (tc_headch_Z ch))
    else g x).
  apply andp_right1.
  (* TODO pervasive repeating *)
  - entailer!. split; [ | split ].
    1,3: intros ll Hlen (Ha & Hb)%Forall_cons_iff; simpl in Ha; rewrite Z.eqb_refl in Ha.
    + simpl. split.
      * apply Znth_nth_error_result; auto. rewrite -> Zlength_correct in Hlen; lia.
      * match goal with HH : context[is_tc_nodearray_proj_chnaux] |- _ => apply HH; auto end.
        eapply Forall_impl_impl. 2: apply Hb.
        apply Forall_forall. intros x Hin. 
        destruct (Z.of_nat x =? Z.of_nat (tr_rootid ch)) eqn:E; auto.
        apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. now apply Hnotin in Hin.
    + constructor.
      * apply Znth_nth_error_result; auto. rewrite -> Zlength_correct in Hlen; lia.
      * match goal with HH : context[tc_rootclk_proj] |- _ => apply HH; auto end.
        eapply Forall_impl_impl. 2: apply Hb.
        apply Forall_forall. intros x Hin. 
        destruct (Z.of_nat x =? Z.of_nat (tr_rootid ch)) eqn:E; auto.
        apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. now apply Hnotin in Hin.
    + constructor; auto with lia.
  - Intros. rewrite ! Z.eqb_refl. entailer!.
    erewrite -> map_ext_Forall at 1; [ apply derives_refl | simpl ].
    apply Forall_forall. intros x Hin.
    destruct (Z.eqb (Z.of_nat x) (Z.of_nat (tr_rootid ch))) eqn:E; try reflexivity.
    apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. apply Hnotin in Hin. destruct Hin.
Qed.

Lemma tc_proj2rep_noroot plclk plnode lclk lnode dim   
  (Hlenc : Zlength lclk = dim) (Hlenn : Zlength lnode = dim) :
  (* is_tc_clockarray_proj here? *)
  forall tc (Htc_clk : Foralltr (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc)
  (Hprojc : is_tc_clockarray_proj lclk tc) (* hmm *)
  (Hprojn : is_tc_nodearray_proj lnode tc),
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (Znth (Z.of_nat i) lclk) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (Znth (Z.of_nat i) lnode) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (map tr_rootid (flat_map tr_flatten (tr_rootchn tc)))) 
    (* (flat_map (fun tc' => map tr_rootid (tr_flatten tc')) (tr_rootchn tc)))  *)
  |-- tc_rep_noroot dim plnode plclk tc.
Proof.
  intros tc.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  cbn delta -[sizeof] iota beta.
  hnf in Hprojc, Hprojn. rewrite -> Foralltr_cons_iff in Hprojc, Hprojn, Htc_clk.
  destruct Hprojc as (_ & Hprojc), Hprojn as (Hchn & Hprojn), Htc_clk as (_ & Hchn_clk).
  simpl in Hchn.
  apply tc_chn_proj2rep with (lclk:=lclk) (lnode:=lnode) (plclk:=plclk) 
    (plnode:=plnode) (dim:=dim) in Hchn; auto.
  2: eapply Forall_impl; [ | apply Hchn_clk ]; apply Foralltr_self.
  pose proof (tr_flatten_root_chn_split chn) as Hperm.
  apply Permutation_map with (f:=tr_rootid) in Hperm.
  erewrite -> fold_right_sepcon_permutation.
  2: apply Permutation_map, Hperm.
  rewrite -> ! map_app, -> fold_right_sepcon_app.
  sep_apply Hchn. fold fold_right_sepcon. apply cancel_left.
  (* maybe an inner induction will help? *)
  clear Hperm Hchn. 
  induction chn as [ | ch chn IH2 ]; cbn delta -[sizeof] iota beta; auto.
  rewrite <- flat_map_app, -> ! map_app, -> fold_right_sepcon_app.
  rewrite -> Forall_cons_iff in IH, Hchn_clk, Hprojc, Hprojn.
  sep_apply (proj1 IH); try tauto. fold fold_right_sepcon. apply cancel_left.
  sep_apply IH2; try tauto.
  apply derives_refl.
Qed.

Lemma tc_rep_noroot2proj plclk plnode dim
  (* (Hcompc : field_compatible (tarray t_struct_clock dim) [] plclk)
  (Hcompn : field_compatible (tarray t_struct_node dim) [] plnode)  *)
  :
  forall tc (Hnodup : tr_NoDupId tc), 
  tc_rep_noroot dim plnode plclk tc |--
  EX f g, 
  !! (Forall (Foralltr (fun sub => Z.of_nat (tr_rootid sub) < dim /\
    Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed)) (tr_rootchn tc)) &&
  !! (forall lclk, 
    Zlength lclk = dim ->
    Forall (fun i => Znth (Z.of_nat i) lclk = f (Z.of_nat i))
        (* over all subch, or tc? *)
      (map tr_rootid (flat_map tr_flatten (tr_rootchn tc))) ->
    Forall (is_tc_clockarray_proj lclk) (tr_rootchn tc)) && (* hmm *)
  !! (forall lnode, 
    Zlength lnode = dim ->
    Forall (fun i => Znth (Z.of_nat i) lnode = g (Z.of_nat i)) 
      (map tr_rootid (flat_map tr_flatten (tr_rootchn tc))) ->
    is_tc_nodearray_proj lnode tc) &&
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (f (Z.of_nat i)) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (g (Z.of_nat i)) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (map tr_rootid (flat_map tr_flatten (tr_rootchn tc)))).
Proof.
  intros tc.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  cbn delta -[sizeof] iota beta.
  hnf in Hnodup.
  simpl in Hnodup. rewrite -> NoDup_cons_iff in Hnodup. destruct Hnodup as (Hnotin & Hnodup).
  (* prepare this *)
  pose proof (tr_flatten_root_chn_split chn) as Hperm.
  apply Permutation_map with (f:=tr_rootid) in Hperm. rewrite map_app in Hperm.
  pose proof Hnodup as Hnodup'.
  eapply Permutation_NoDup in Hnodup'. 2: apply Hperm.
  rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hnodup'.
  setoid_rewrite base.elem_of_list_In in Hnodup'.
  destruct Hnodup' as (Hnodup_chn & Hdj & Hnodup_chn').

  sep_apply tc_chn_rep2proj; auto.
  Intros f g. fold (fold_right_sepcon).
  (* now need some change to rule out the root nodes of chn *)
  enough 
  (fold_right_sepcon (map (tc_rep_noroot dim plnode plclk) chn) |-- 
    EX f0 g0, 
    !! (Forall (Foralltr (fun sub => Z.of_nat (tr_rootid sub) < dim /\
      Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
      Z.of_nat (tc_rootaclk sub) <= Int.max_signed)) (flat_map tr_rootchn chn)) &&
    !! (forall lclk, 
      Zlength lclk = dim ->
      Forall (fun i => (f0 (Z.of_nat i)) = Znth (Z.of_nat i) lclk) 
        (map tr_rootid (flat_map tr_flatten (flat_map tr_rootchn chn))) ->
      Forall (is_tc_clockarray_proj lclk) (flat_map tr_rootchn chn)) &&
    !! (forall lnode, 
      Zlength lnode = dim ->
      Forall (fun i => (g0 (Z.of_nat i)) = Znth (Z.of_nat i) lnode) 
        (map tr_rootid (flat_map tr_flatten (flat_map tr_rootchn chn))) ->
      Forall (is_tc_nodearray_proj lnode) chn) &&
    fold_right_sepcon (map (fun i => 
      data_at Tsh t_struct_clock (f0 (Z.of_nat i)) 
        (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
      data_at Tsh t_struct_node (g0 (Z.of_nat i)) 
        (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
      (map tr_rootid (flat_map tr_flatten (flat_map tr_rootchn chn))))) as Hgoal.
  - sep_apply Hgoal. Intros f0 g0. fold (fold_right_sepcon).
    rewrite sepcon_comm, sepcon_map_data_at_merge_app with (fdec:=Nat.eq_dec); auto.
    erewrite <- fold_right_sepcon_permutation.
    2: apply Permutation_map, Hperm.
    (* Z is really inconvenient here ... *)
    Exists 
      (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) (map tr_rootid chn) then f x else f0 x)
      (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) (map tr_rootid chn) then g x else g0 x).
    apply andp_right1.
    + entailer!. split; [ | split ].
      1,3: intros ll Hlen Htmp; eapply Permutation_Forall in Htmp; [ | apply Hperm ]; 
        rewrite Forall_app in Htmp; destruct Htmp as (Ha & Hb).
      * constructor.
        --match goal with HH : context[is_tc_nodearray_proj_chnaux] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Ha.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tr_rootid chn)).
        --match goal with HH : context[is_tc_nodearray_proj] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Hb.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. destruct (in_dec Nat.eq_dec x (map tr_rootid chn)) as [ Heq | ]; auto.
          specialize (Hdj x). tauto.
      * unfold is_tc_clockarray_proj.
        eapply Forall_impl. 1: intros ? HH; apply Foralltr_cons_iff'; apply HH.
        apply Forall_and.
        --match goal with HH : context[tc_rootclk_proj] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Ha.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tr_rootid chn)).
        --apply Forall_map, Forall_concat. rewrite <- flat_map_concat_map.
          match goal with HH : context[is_tc_clockarray_proj] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Hb.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. destruct (in_dec Nat.eq_dec x (map tr_rootid chn)) as [ Heq | ]; auto.
          specialize (Hdj x). tauto.
      * eapply Forall_impl. 1: intros ? HH; apply Foralltr_cons_iff'; apply HH.
        apply Forall_and; auto.
        (* TODO streamline this *)
        apply Forall_map, Forall_concat. rewrite <- flat_map_concat_map. auto.
    + Intros.
      erewrite map_ext with (l:=(map tr_rootid (flat_map tr_flatten chn))).
      1: apply derives_refl.
      intros x. simpl. rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tr_rootid chn)).
  - (* induction on chn? *)
    clear Hnotin clk aclk.
    clear H H1 f g u Hperm Hnodup_chn H0 Hdj.
    induction chn as [ | ch chn IH2 ].
    1:{
      simpl. Exists (fun _ : Z => default_clockstruct) (fun _ : Z => default_nodestruct).
      entailer!.
    }
    (* need both nodup, one for IH, another for use *)
    simpl in Hnodup. rewrite -> map_app, -> NoDup_app_iff in Hnodup.
    destruct Hnodup as (Hnodup_ch & Hnodup_chn & _).
    simpl in Hnodup_chn'. rewrite <- flat_map_app, -> map_app, -> NoDup_app_iff in Hnodup_chn'.
    destruct Hnodup_chn' as (Hnodup_ch' & Hnodup_chn' & Hdj).
    rewrite Forall_cons_iff in IH. destruct IH as (Hch & IH).
    cbn delta [map flat_map fold_right_sepcon] beta iota.
    sep_apply Hch. Intros f g. fold (fold_right_sepcon).
    sep_apply IH2. Intros f0 g0. fold (fold_right_sepcon).
    (* do not merge here ... *)
    Exists 
      (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) 
        (map tr_rootid (flat_map tr_flatten (tr_rootchn ch))) then f x else f0 x)
      (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) 
        (map tr_rootid (flat_map tr_flatten (tr_rootchn ch))) then g x else g0 x).
    apply andp_right1.
    + entailer!. split; [ | split ].
      1,3: intros ll Hlen Htmp; rewrite <- flat_map_app, -> map_app, -> Forall_app in Htmp; 
        destruct Htmp as (Ha & Hb).
      * constructor.
        --match goal with HH : context[is_tc_nodearray_proj] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Ha.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. 
          now destruct (in_dec Nat.eq_dec x (map tr_rootid (flat_map tr_flatten (tr_rootchn ch)))).
        --match goal with HH : context[Forall (is_tc_nodearray_proj _)] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Hb.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. 
          destruct (in_dec Nat.eq_dec x (map tr_rootid (flat_map tr_flatten (tr_rootchn ch)))) as [ Heq | ]; auto.
          specialize (Hdj x). tauto.
      * apply Forall_app. split.
        --match goal with HH : context[Forall (is_tc_clockarray_proj _) (tr_rootchn ch)] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Ha.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. 
          now destruct (in_dec Nat.eq_dec x (map tr_rootid (flat_map tr_flatten (tr_rootchn ch)))).
        --match goal with HH : context[Forall (is_tc_clockarray_proj _) (flat_map tr_rootchn chn)] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Hb.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. 
          destruct (in_dec Nat.eq_dec x (map tr_rootid (flat_map tr_flatten (tr_rootchn ch)))) as [ Heq | ]; auto.
          specialize (Hdj x). tauto.
      * now apply Forall_app.
    + Intros. 
      rewrite sepcon_comm, sepcon_map_data_at_merge_app with (fdec:=Nat.eq_dec); auto.
      rewrite <- map_app, -> flat_map_app.
      erewrite map_ext with (l:=(map tr_rootid
        (flat_map tr_flatten (tr_rootchn ch ++ flat_map tr_rootchn chn)))).
      1: apply derives_refl.
      intros x. simpl. rewrite Nat2Z.id. 
      now destruct (in_dec Nat.eq_dec x (map tr_rootid (flat_map tr_flatten (tr_rootchn ch)))).
Qed.

Lemma tc_proj2rep plclk plnode lclk lnode dim   
  (Hlenc : Zlength lclk = dim) (Hlenn : Zlength lnode = dim)
  tc (Htc_clk : Foralltr (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc)
  (Hprojc : is_tc_clockarray_proj lclk tc)
  (Hprojn : is_tc_nodearray_proj_full lnode tc) :
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (Znth (Z.of_nat i) lclk) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (Znth (Z.of_nat i) lnode) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (map tr_rootid (tr_flatten tc))) |-- 
  tc_rep dim plnode plclk tc.
Proof.
  destruct tc as [(u, ?, ?) chn] eqn:E.
  cbn delta -[sizeof] iota beta.
  replace chn with (tr_rootchn tc) by now rewrite E.
  subst tc. destruct Hprojn as (Hroot & Hprojn).
  sep_apply (tc_proj2rep_noroot plclk plnode lclk lnode dim); try tauto.
  unfold tc_rep. simpl tr_rootchn. 
  (* TODO why no cancel_right? *)
  match goal with |- _ |-- (?a * ?b) => rewrite (sepcon_comm a b) end.
  apply cancel_left.
  pose proof Hroot as Htmp. apply nth_error_some_inrange_Z in Htmp. simpl in Htmp.
  hnf in Hroot. apply nth_error_Znth_result in Hroot. simpl in Hroot. 
  apply Foralltr_self, nth_error_Znth_result in Hprojc. simpl in Hprojc. 
  rewrite Hroot, Hprojc.
  unfold tc_root_rep, clock_rep, node_rep. simpl.
  entailer!. 
  apply Foralltr_self in Htc_clk. simpl in Htc_clk. lia.
Qed.

Lemma tc_rep2proj plclk plnode dim tc (Hnodup : tr_NoDupId tc) :
  tc_root_rep dim plnode plclk tc * tc_rep_noroot dim plnode plclk tc |--
  EX f g, 
  !! (Foralltr (fun sub => Z.of_nat (tr_rootid sub) < dim /\
    Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) &&
  !! (forall lclk, 
    Zlength lclk = dim ->
    Forall (fun i => Znth (Z.of_nat i) lclk = f (Z.of_nat i)) (map tr_rootid (tr_flatten tc)) ->
    is_tc_clockarray_proj lclk tc) &&
  !! (forall lnode, 
    Zlength lnode = dim ->
    Forall (fun i => Znth (Z.of_nat i) lnode = g (Z.of_nat i)) (map tr_rootid (tr_flatten tc)) ->
    is_tc_nodearray_proj_full lnode tc) &&
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (f (Z.of_nat i)) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (g (Z.of_nat i)) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (map tr_rootid (tr_flatten tc))).
Proof.
  sep_apply tc_rep_noroot2proj. Intros f g.
  destruct tc as [(u, clk, aclk) chn]. 
  unfold tc_root_rep, clock_rep, node_rep. Intros. 
  unfold tc_headch_Z. cbn delta -[sizeof] beta iota in * |- *. 
  (* fold (tcs_head_Z chn).  *)
  hnf in Hnodup.
  simpl in Hnodup. rewrite -> NoDup_cons_iff in Hnodup. destruct Hnodup as (Hnotin & Hnodup).
  Exists (fun x : Z => if Z.eqb x (Z.of_nat u) 
    then (clock_payload (Z.of_nat clk) (Z.of_nat aclk)) else f x)
  (fun x : Z => if Z.eqb x (Z.of_nat u) then
    (node_payload default_nodefield default_nodefield default_nodefield (tcs_head_Z chn))
    else g x).
  apply andp_right1.
  - entailer!. split; [ | split ].
    1,3: intros ll Hlen (Ha & Hb)%Forall_cons_iff; simpl in Ha; rewrite Z.eqb_refl in Ha.
    + hnf. split.
      * hnf. simpl. apply Znth_nth_error_result; auto. rewrite -> Zlength_correct in Hlen; lia.
      * match goal with HH : context[is_tc_nodearray_proj] |- _ => apply HH; auto end.
        eapply Forall_impl_impl. 2: apply Hb.
        apply Forall_forall. intros x Hin. 
        destruct (Z.of_nat x =? Z.of_nat u) eqn:E; auto.
        apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. now apply Hnotin in Hin.
    + constructor.
      * apply Znth_nth_error_result; auto. simpl. rewrite -> Zlength_correct in Hlen; lia.
      * match goal with HH : context[is_tc_clockarray_proj] |- _ => apply HH; auto end.
        eapply Forall_impl_impl. 2: apply Hb.
        apply Forall_forall. intros x Hin. 
        destruct (Z.of_nat x =? Z.of_nat u) eqn:E; auto.
        apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. now apply Hnotin in Hin.
    + constructor; simpl; auto with lia.
  - Intros. rewrite ! Z.eqb_refl. entailer!.
    erewrite -> map_ext_Forall at 1; [ apply derives_refl | simpl ].
    apply Forall_forall. intros x Hin.
    destruct (Z.eqb (Z.of_nat x) (Z.of_nat u)) eqn:E; try reflexivity.
    apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. apply Hnotin in Hin. destruct Hin.
Qed.

(* TODO is the bag representation actually necessary or not? *)

Lemma tc_array_emptypart2bag plclk plnode lclk lnode dim 
  (Hlenc : Zlength lclk = dim) (Hlenn : Zlength lnode = dim)
  tcs (Hprojc : clockarray_emptypart lclk tcs)
  (Hprojn : nodearray_emptypart lnode tcs) :
  fold_right_sepcon (map (fun i => 
    (* actually, the Znth here should all be equal to default *)
    data_at Tsh t_struct_clock (Znth (Z.of_nat i) lclk) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (Znth (Z.of_nat i) lnode) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (filter (fun t => negb (ssrbool.isSome (find (has_same_id t) tcs))) 
      (map Z.to_nat (upto (Z.to_nat dim))))) |-- 
  unused_bag_rep dim plnode plclk tcs.
Proof.
  unfold unused_bag_rep.
  erewrite map_ext_Forall. 1: apply derives_refl.
  simpl. apply Forall_forall. intros t (Hin & Hnotin%negb_true_iff)%filter_In. 
  rewrite <- seq_upto, -> in_seq in Hin. simpl in Hin.
  assert (0 <= Z.of_nat t < dim) as Hin' by lia.
  destruct (find (has_same_id t) tcs) eqn:E; try discriminate.
  hnf in Hprojc, Hprojn.
  rewrite Zlength_correct in Hlenc, Hlenn.
  (* ... *)
  f_equal; [ destruct (nth_error lclk t) eqn:EE | destruct (nth_error lnode t) eqn:EE ].
  all: try apply nth_error_None in EE; try lia.
  all: f_equal; apply nth_error_Znth_result.
  - pose proof EE as Etmp. apply Hprojc in Etmp; congruence.
  - pose proof EE as Etmp. apply Hprojn in Etmp; congruence.
Qed.

Fact tc_all_roottid_equal_to_range_filter tc (Hnodup : tr_NoDupId tc) 
  dim (Hdim : Foralltr (fun tc' : treeclock => Z.of_nat (tr_rootid tc') < dim) tc) :
  Permutation (map tr_rootid (tr_flatten tc))
  (filter (fun t : nat => ssrbool.isSome (find (has_same_id t) (tr_flatten tc)))
    (map Z.to_nat (upto (Z.to_nat dim)))).
Proof.
  apply NoDup_Permutation; auto.
  - apply NoDup_filter. rewrite <- seq_upto. apply seq_NoDup.
  - intros x. rewrite <- seq_upto, -> filter_In, -> in_seq, -> trs_find_in_iff.
    split; try tauto. intros HH. split; auto.
    rewrite <- trs_find_in_iff in HH.
    apply Foralltr_Forall_subtree in Hdim; auto.
    rewrite -> Forall_forall in Hdim. 
    rewrite in_map_iff in HH. destruct HH as (sub & <- & Hin).
    apply Hdim in Hin. lia.
Qed.

Lemma tc_array2rep_and_bag plclk plnode lclk lnode dim tc
  (Hlenc : Zlength lclk = dim) (Hlenn : Zlength lnode = dim) (Hdim : 0 < dim)
  (Htc_clk : Foralltr (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc)
  (* now this is required *)
  (Hnodup : tr_NoDupId tc) 
  (Hprojc : is_tc_clockarray_proj lclk tc)
  (Hprojn : is_tc_nodearray_proj_full lnode tc) 
  (Hprojce : clockarray_emptypart lclk (tr_flatten tc))
  (Hprojne : nodearray_emptypart lnode (tr_flatten tc)) :
  data_at Tsh (tarray t_struct_clock dim) lclk plclk *
    data_at Tsh (tarray t_struct_node dim) lnode plnode |--
  !! (field_compatible (tarray t_struct_clock dim) [] plclk) &&
  !! (field_compatible (tarray t_struct_node dim) [] plnode) &&
  tc_rep dim plnode plclk tc * 
    unused_bag_rep dim plnode plclk (tr_flatten tc).
Proof.
  do 2 sep_apply data_at_array_unfold.
  fold (fold_right_sepcon). normalize.
  rewrite -> sepcon_comm.
  rewrite -> sepcon_map_data_at_merge_sepcon, -> upto_seq, -> seq_upto, -> map_map. 
  erewrite -> fold_right_sepcon_permutation.
  2: apply Permutation_map, Permutation_split_combine.
  rewrite -> map_app, -> fold_right_sepcon_app.
  apply sepcon_derives. all: cycle 1.
  - apply tc_array_emptypart2bag; auto.
  - eapply derives_trans. 2: apply tc_proj2rep; eauto.
    erewrite -> fold_right_sepcon_permutation.
    1: apply derives_refl.
    destruct Hprojn as (Hroot & Hprojn). 
    apply nth_error_some_inrange_Z, is_tc_nodearray_proj_tid_bounded in Hroot; auto.
    symmetry. apply Permutation_map, tc_all_roottid_equal_to_range_filter; auto.
    rewrite <- Hlenn. auto.
Qed.

Lemma tc_rep_and_bag2array_pre plclk plnode dim tc (Hdim : 0 < dim)
  (* (Hcompc : field_compatible (tarray t_struct_clock dim) [] plclk)
  (Hcompn : field_compatible (tarray t_struct_node dim) [] plnode) *)
  (Hnodup : tr_NoDupId tc) :
  tc_root_rep dim plnode plclk tc * tc_rep_noroot dim plnode plclk tc *
    unused_bag_rep dim plnode plclk (tr_flatten tc) |--
  EX f g, 
  !! (Foralltr (fun sub => Z.of_nat (tr_rootid sub) < dim /\
    Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) &&
  !! (forall lclk, 
    Zlength lclk = dim ->
    (forall i, 0 <= i < dim ->
      Znth i lclk = f i) ->
        (* (if in_dec Nat.eq_dec (Z.to_nat i) (map tr_rootid (tr_flatten tc)) 
        then f i else default_clockstruct)) -> *)
    is_tc_clockarray_proj lclk tc /\ clockarray_emptypart lclk (tr_flatten tc)) &&
  !! (forall lnode, 
    Zlength lnode = dim ->
    (forall i, 0 <= i < dim ->
      Znth i lnode = g i) ->
        (* (if in_dec Nat.eq_dec (Z.to_nat i) (map tr_rootid (tr_flatten tc)) 
        then g i else default_nodestruct)) -> *)
    is_tc_nodearray_proj_full lnode tc /\ nodearray_emptypart lnode (tr_flatten tc)) &&
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (f i) 
      (offset_val (sizeof t_struct_clock * i) plclk) *
    data_at Tsh t_struct_node (g i) 
      (offset_val (sizeof t_struct_node * i) plnode))%logic 
    (upto (Z.to_nat dim))).
Proof.
  sep_apply tc_rep2proj. Intros f g.
  unfold unused_bag_rep.
  (* prepare various *)
  match goal with HH : Foralltr _ _ |- _ => rename HH into Hb end.
  assert (Forall (fun x => Z.of_nat x < dim) (map tr_rootid (tr_flatten tc))) as Htid.
  { apply List.Forall_map, Foralltr_Forall_subtree. now apply Foralltr_and in Hb. }
  epose proof (tc_all_roottid_equal_to_range_filter _ Hnodup dim ?[Goalq]) as Hperm.
  [Goalq]: now apply Foralltr_and in Hb.
  match type of Hperm with Permutation ?al ?bl => assert (forall x, In x al <-> In x bl) as Hinin end.
  { pose proof Hperm as Hperm'. symmetry in Hperm'. intros. split; intros. all: eapply Permutation_in; eauto. }

  erewrite -> fold_right_sepcon_permutation at 1.
  2: apply Permutation_map, Hperm.
  erewrite -> sepcon_map_data_at_merge_app with (fdec:=Nat.eq_dec).
  2:{ intros a. rewrite ! filter_In, negb_true_iff. eqsolve. }
  erewrite -> fold_right_sepcon_permutation.
  2: symmetry; apply Permutation_map, Permutation_split_combine.
  Exists (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) (map tr_rootid (tr_flatten tc)) 
    then f x else default_clockstruct)
  (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) (map tr_rootid (tr_flatten tc)) 
    then g x else default_nodestruct).
  apply andp_right1.
  - entailer!. split.
    all: intros ll Hlen Hcorr.
    + split.
      * match goal with HH : context[is_tc_nodearray_proj_full] |- _ => apply HH; auto end.
        apply Forall_forall. intros x Hin.
        rewrite Hcorr. 2: rewrite Forall_forall in Htid; apply Htid in Hin; lia.
        rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tr_rootid (tr_flatten tc))).
      * hnf. intros x np Hn He.
        assert (0 <= Z.of_nat x < dim) as Hrange by (apply nth_error_some_inrange_Z in He; lia).
        specialize (Hcorr _ Hrange).
        apply nth_error_Znth_result in He. rewrite <- He, -> Hcorr.
        rewrite Nat2Z.id. 
        destruct (in_dec Nat.eq_dec x (map tr_rootid (tr_flatten tc))) as [ Hin | ]; auto.
        now apply trs_find_in_iff_neg in Hn.
    + split.
      * match goal with HH : context[is_tc_clockarray_proj] |- _ => apply HH; auto end.
        apply Forall_forall. intros x Hin.
        rewrite Hcorr. 2: rewrite Forall_forall in Htid; apply Htid in Hin; lia.
        rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tr_rootid (tr_flatten tc))).
      * hnf. intros x np Hn He.
        assert (0 <= Z.of_nat x < dim) as Hrange by (apply nth_error_some_inrange_Z in He; lia).
        specialize (Hcorr _ Hrange).
        apply nth_error_Znth_result in He. rewrite <- He, -> Hcorr.
        rewrite Nat2Z.id. 
        destruct (in_dec Nat.eq_dec x (map tr_rootid (tr_flatten tc))) as [ Hin | ]; auto.
        now apply trs_find_in_iff_neg in Hn.
  - Intros. rewrite map_map. 
    erewrite -> map_ext_Forall at 1; [ apply derives_refl | simpl ].
    apply Forall_forall. intros x Hin. rewrite In_upto in Hin.
    rewrite Z2Nat.id in Hin; try lia. rewrite ! Z2Nat.id; try lia.
    repeat match goal with |- context[in_dec ?fd ?x ?ll] => destruct (in_dec fd x ll); simpl end.
    all: try reflexivity.
    all: specialize (Hinin (Z.to_nat x)); tauto.
Qed.

Lemma tc_rep_and_bag2array plclk plnode dim tc (Hdim : 0 < dim)
  (Hcompc : field_compatible (tarray t_struct_clock dim) [] plclk)
  (Hcompn : field_compatible (tarray t_struct_node dim) [] plnode)
  (Hnodup : tr_NoDupId tc) :
  tc_root_rep dim plnode plclk tc * tc_rep_noroot dim plnode plclk tc *
    unused_bag_rep dim plnode plclk (tr_flatten tc) |--
  EX lnode lclk, 
  !! (Zlength lnode = dim) &&
  !! (Zlength lclk = dim) &&
  !! (Foralltr (fun sub => Z.of_nat (tr_rootid sub) < dim /\
    Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) &&
  !! (is_tc_clockarray_proj lclk tc) && !! (clockarray_emptypart lclk (tr_flatten tc)) &&
  !! (is_tc_nodearray_proj_full lnode tc) && !! (nodearray_emptypart lnode (tr_flatten tc)) &&
  data_at Tsh (tarray t_struct_clock dim) lclk plclk *
    data_at Tsh (tarray t_struct_node dim) lnode plnode.
Proof.
  sep_apply tc_rep_and_bag2array_pre.
  Intros f g. rewrite <- sepcon_map_data_at_merge_sepcon.
  sep_apply (data_at_array_fold Tsh t_struct_clock plclk dim Hdim f Hcompc).
  Intros lclk. fold (fold_right_sepcon).
  sep_apply (data_at_array_fold Tsh t_struct_node plnode dim Hdim g Hcompn).
  Intros lnode.
  Exists lnode lclk.
  match goal with HH : context[is_tc_clockarray_proj] |- _ => 
    specialize (HH lclk); do 2 (removehead HH; try lia; try assumption) end.
  match goal with HH : context[is_tc_nodearray_proj_full] |- _ => 
    specialize (HH lnode); do 2 (removehead HH; try lia; try assumption) end.
  entailer!. intuition.
Qed.

(* magic wand as frame *)

Lemma tc_rep_subtree_frame_pre tc : forall l sub (Hsub : subtr_witness l sub tc) 
  dim plnode plclk z1 z2 z3,
  tc_subroot_rep dim plnode plclk tc z1 z2 z3 *
    tc_rep_noroot dim plnode plclk tc |--
  EX z1' z2' z3' ,
  !! (l = nil -> z1 = z1' /\ z2 = z2' /\ z3 = z3') &&
  tc_subroot_rep dim plnode plclk sub z1' z2' z3' *
    tc_rep_noroot dim plnode plclk sub *
  (ALL sub', !! (tr_rootid sub = tr_rootid sub') -->
    ((tc_subroot_rep dim plnode plclk sub' z1' z2' z3' *
      tc_rep_noroot dim plnode plclk sub') -*
    tc_subroot_rep dim plnode plclk (tr_locate_upd tc l sub') z1 z2 z3 *
      tc_rep_noroot dim plnode plclk (tr_locate_upd tc l sub'))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  destruct l as [ | x l ].
  - hnf in Hsub. injection Hsub as <-.
    Exists z1 z2 z3.
    entailer!.
    simpl.
    apply allp_right. intros sub'.
    apply imp_andp_adjoint.
    Intros.
    apply wand_frame_intro'. entailer!.
  - hnf in Hsub. simpl in Hsub.
    destruct (nth_error chn x) as [ ch | ] eqn:Enth; try eqsolve.
    (* in_split is too weak *)
    (* 
    pose proof Enth as Hin_ch. apply nth_error_In in Hin_ch.
    pose proof (in_split _ _ Hin_ch) as (pre & suf & Echn). 
    *)
    pose proof (nth_error_split _ _ Enth) as (pre & suf & Echn & Hlen).
    assert (In ch chn) as Hin_ch by (subst chn; rewrite in_app_iff; simpl; tauto).
    unfold tc_subroot_rep at 1.
    Intros.
    cbn delta [tc_rep_noroot tr_rootid tc_rootclk tc_rootaclk tr_rootinfo info_tid info_clk info_aclk] beta iota.
    rewrite -> Echn at 2 3.
    rewrite -> map_app, -> fold_right_sepcon_app, -> tc_chn_rep_segment.
    cbn delta [fold_right_sepcon map] beta iota.
    rewrite -> Forall_forall in IH.
    specialize (IH _ Hin_ch _ _ Hsub dim plnode plclk 
      (tcs_head_Z_default default_nodefield suf)
      (tcs_head_Z_default default_nodefield (rev pre)) 
      (Z.of_nat u)).
    sep_apply IH.
    Intros z1' z2' z3'.
    fold fold_right_sepcon.
    Exists z1' z2' z3'.
    entailer!.
    apply allp_right. intros sub'.
    (* hint. *)
    allp_left sub'.
    fold fold_right_sepcon.
    apply imp_andp_adjoint. Intros. rewrite prop_imp; try assumption.
    apply wand_frame_intro'.
    match goal with |- ?a * ?b * _ |-- _ => sep_apply (wand_frame_elim' (a * b)%logic) end.
    1: now unfold tc_rep_noroot.
    fold fold_right_sepcon.
    simpl tr_locate_upd. rewrite Enth.
    unfold tc_rep_noroot at 4. fold tc_rep_noroot.
    rewrite -> ! upd_nth_exact; auto.
    rewrite -> map_app, -> fold_right_sepcon_app, -> tc_chn_rep_segment.
    cbn delta [fold_right_sepcon map] beta iota.
    unfold tc_subroot_rep at 2.
    cbn delta [tc_rep_noroot tr_rootid tc_rootclk tc_rootaclk tr_rootinfo info_tid info_clk info_aclk] beta iota.
    entailer!.

    (* still, need to destruct l and discuss? *)
    assert (tr_rootid (tr_locate_upd ch l sub') = tr_rootid ch) as Eid.
    {
      destruct l.
      - simpl in Hsub |- *. now injection Hsub as <-.
      - destruct ch as [ni chn]. simpl in Hsub |- *. destruct (nth_error chn n); eqsolve.
    }
    rewrite -> ! Eid.
    entailer!.
    destruct pre; unfold tc_headch_Z; simpl; now try rewrite Eid.
Qed. 

Lemma tc_rep_subtree_frame tc : forall l sub (Hsub : subtr_witness l sub tc) 
  dim plnode plclk z1 z2 z3,
  tc_subroot_rep dim plnode plclk tc z1 z2 z3 *
    tc_rep_noroot dim plnode plclk tc |--
  EX z1' z2' z3' ,
  !! (l = nil -> z1 = z1' /\ z2 = z2' /\ z3 = z3') &&
  tc_subroot_rep dim plnode plclk sub z1' z2' z3' *
    tc_rep_noroot dim plnode plclk sub *
  (ALL chn_sub', 
    (tc_subroot_rep dim plnode plclk (Node (tr_rootinfo sub) chn_sub') z1' z2' z3' *
      tc_rep_noroot dim plnode plclk (Node (tr_rootinfo sub) chn_sub')) -*
    tc_subroot_rep dim plnode plclk (tr_locate_upd tc l (Node (tr_rootinfo sub) chn_sub')) z1 z2 z3 *
      tc_rep_noroot dim plnode plclk (tr_locate_upd tc l (Node (tr_rootinfo sub) chn_sub'))).
Proof.
  intros.
  sep_eapply tc_rep_subtree_frame_pre.
  1: apply Hsub.
  Intros z1' z2' z3'. Exists z1' z2' z3'.
  entailer!.
  apply allp_right. intros chn_sub'.
  allp_left (Node (tr_rootinfo sub) chn_sub').
  now rewrite prop_imp.
Qed.

(* simple malloc/free spec; TODO may use the one in VSU? *)
Definition malloc_spec :=
  DECLARE _malloc
  WITH n : Z
  PRE [ tint ]
    PROP (4 <= n <= Int.max_unsigned)
    PARAMS (Vint (Int.repr n))
    SEP ()
  POST [ tptr tvoid ]
    EX v : val,
    PROP (malloc_compatible n v)
    RETURN (v)
    SEP (memory_block Tsh n v).

(* copied from sha/spec_sha.v with slight modification *)
Definition memset_spec :=
  DECLARE _memset
  WITH sh : share, p: val, n: Z, c: int
  PRE [ tptr tvoid, tint, tuint ]
    PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
    PARAMS (p; Vint c; Vint (Int.repr n))
    SEP (memory_block sh n p)
  POST [ tptr tvoid ]
    PROP() RETURN(p)
    SEP(data_at sh (tarray tuchar n) (Zrepeat (Vint c) n) p).

Definition join_spec :=
  DECLARE _join
  WITH dim : Z, 
    tc : treeclock, plclk : val, plnode : val, plstk : val, p : val,
    tc' : treeclock, plclk' : val, plnode' : val, plstk' : val, p' : val
  PRE [ tptr t_struct_treeclock, tptr t_struct_treeclock ]
    (* PROP (is_pos_tshort dim) *)
    PROP (0 <= dim <= Int.max_signed; 
      (* join requirement *)
      tc_shape_inv tc; tc_shape_inv tc'; tc_respect tc' tc; 
      (tc_getclk (tr_rootid tc) tc' <= tc_rootclk tc)%nat)
    PARAMS (p; p')
    SEP (treeclock_rep dim tc plclk plnode plstk p; 
      treeclock_rep dim tc' plclk' plnode' plstk' p')
  POST [ tvoid ]
    PROP () 
    RETURN ()
    (* nothing should change for p' *)
    SEP (treeclock_rep dim (tc_join tc tc') plclk plnode plstk p;
      treeclock_rep dim tc' plclk' plnode' plstk' p').

(* detach_from_neighbors does not modify clock, but in the rep-predicates nodes and clocks 
  are bundled together, so still need to mention the clock array pointer *)
Definition detach_from_neighbors_spec_local :=
  DECLARE _detach_from_neighbors
  WITH dim : Z, v1 : val, plclk : val, plnode : val, v2 : val, v3 : val, p : val, 
    par : nat, 
    pre : list treeclock, ch : treeclock, suf : list treeclock, 
    z1 : Z, z2 : Z, z3 : Z
  PRE [ tptr t_struct_treeclock, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; 
      Z.of_nat par < dim;
      (* required for judging whether par.headch = ch *)
      trs_roots_NoDupId (pre ++ ch :: suf))
    PARAMS (p; Vint (Int.repr (Z.of_nat (tr_rootid ch))); 
      offset_val (sizeof t_struct_node * Z.of_nat (tr_rootid ch)) plnode)
    SEP ((* no clock of this par node *)
      data_at Tsh t_struct_node (node_payload z1 z2 z3 (tcs_head_Z (pre ++ ch :: suf)))
        (offset_val (sizeof t_struct_node * Z.of_nat par) plnode); 
      tc_chn_rep dim plnode plclk par default_nodefield default_nodefield (pre ++ ch :: suf); 
      (* this treeclock struct is needed, though *)
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p)
  POST [ tvoid ]
    EX z1' z2' z3' : Z,
    PROP ()
    RETURN ()
    SEP (data_at Tsh t_struct_node (node_payload z1 z2 z3 (tcs_head_Z (pre ++ suf)))
        (offset_val (sizeof t_struct_node * Z.of_nat par) plnode); 
      tc_chn_rep dim plnode plclk par default_nodefield default_nodefield (pre ++ suf);
      (* hope we do not care about z1' z2' z3' ... *)
      tc_subroot_rep dim plnode plclk ch z1' z2' z3';
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p).

Definition detach_from_neighbors_spec :=
  DECLARE _detach_from_neighbors
  (* no need to specify v1? *)
  WITH dim : Z, v1 : val, plclk : val, plnode : val, v2 : val, v3 : val, p : val, 
    tc : treeclock, l : list nat, sub : treeclock
  PRE [ tptr t_struct_treeclock, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; 
      l <> nil; subtr_witness l sub tc;
      (* still required *)
      tr_NoDupId tc)
    PARAMS (p; Vint (Int.repr (Z.of_nat (tr_rootid sub))); 
      offset_val (sizeof t_struct_node * Z.of_nat (tr_rootid sub)) plnode)
    SEP (tc_rep dim plnode plclk tc;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p)
  POST [ tvoid ]
    EX z1' z2' z3' : Z,
    PROP ()
    RETURN ()
    SEP (tc_rep dim plnode plclk (tr_remove_node tc l);
      tc_subroot_rep dim plnode plclk sub z1' z2' z3';
      tc_rep_noroot dim plnode plclk sub;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p).

Definition push_child_spec_local :=
  DECLARE _push_child
  WITH dim : Z, v1 : val, plclk : val, plnode : val, v2 : val, v3 : val, p : val, 
    par : nat, 
    chn : list treeclock, sub : treeclock,
    z1 : Z, z2 : Z, z3 : Z, z4 : Z, z5 : Z, z6 : Z
  PRE [ tptr t_struct_treeclock, tint, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; 
      Z.of_nat par < dim)
    PARAMS (p; Vint (Int.repr (Z.of_nat par)); Vint (Int.repr (Z.of_nat (tr_rootid sub))); 
      offset_val (sizeof t_struct_node * Z.of_nat (tr_rootid sub)) plnode)
    SEP ((* no clock of this par node *)
      data_at Tsh t_struct_node (node_payload z1 z2 z3 (tcs_head_Z chn))
        (offset_val (sizeof t_struct_node * Z.of_nat par) plnode); 
      tc_chn_rep dim plnode plclk par default_nodefield default_nodefield chn;
      tc_subroot_rep dim plnode plclk sub z4 z5 z6;
      (* this treeclock struct is needed, though *)
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at Tsh t_struct_node (node_payload z1 z2 z3 (Z.of_nat (tr_rootid sub)))
        (offset_val (sizeof t_struct_node * Z.of_nat par) plnode); 
      tc_chn_rep dim plnode plclk par default_nodefield default_nodefield (sub :: chn); 
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p).

Definition push_child_spec :=
  DECLARE _push_child
  WITH dim : Z, v1 : val, plclk : val, plnode : val, v2 : val, v3 : val, p : val, 
    tc : treeclock, tc_par : treeclock, sub : treeclock, l : list nat, 
    z1 : Z, z2 : Z, z3 : Z
  PRE [ tptr t_struct_treeclock, tint, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; 
      (* the tc_par does not appear in the post condition, but appears in the expr of pointers and is kind of necessary *)
      Z.of_nat (tr_rootid tc_par) < dim; 
      subtr_witness l tc_par tc)
    PARAMS (p; Vint (Int.repr (Z.of_nat (tr_rootid tc_par))); Vint (Int.repr (Z.of_nat (tr_rootid sub))); 
      offset_val (sizeof t_struct_node * Z.of_nat (tr_rootid sub)) plnode)
    SEP (tc_rep dim plnode plclk tc;
      tc_subroot_rep dim plnode plclk sub z1 z2 z3;
      tc_rep_noroot dim plnode plclk sub;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (tc_rep dim plnode plclk (tr_prepend_nodes tc l (sub :: nil));
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p).

Definition get_updated_nodes_join_chn_spec :=
  DECLARE _get_updated_nodes_join_chn
  WITH dim : Z, 
    (* plnode is not used here *)
    tc : treeclock, plclk : val, plnode : val, plstk : val, top : nat, p : val,
    v1 : val, plclk' : val, plnode' : val, v2 : val, v3 : val, p' : val,
    (* decoupling clk and par' *)
    clk : nat, par' : nat, chn' : list treeclock, 
    lclk : list (reptype t_struct_clock), lstk : list val,
    lclk' : list (reptype t_struct_clock), lnode' : list (reptype t_struct_node)
  PRE [ tptr t_struct_treeclock, tptr t_struct_treeclock, tint, tint ]
    PROP (0 <= dim <= Int.max_signed; 
      Z.of_nat par' < dim; 
      Foralltr (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
        Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc;
      Forall (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
        Z.of_nat (tc_rootaclk sub) <= Int.max_signed) chn';
      (* at least we need this *)
      node_struct_get_headch (Znth (Z.of_nat par') lnode') = Vint (Int.repr (tcs_head_Z chn'));
      (* these are redundant, but add it here anyway *)
      0 <= Z.of_nat clk <= Int.max_signed;
      (* Forall (fun sub => Z.of_nat par' < dim) sub; *)
      (* need proj for self (tc) *)
      Zlength lclk = dim;
      Zlength lstk = dim;
      Zlength lclk' = dim;
      Zlength lnode' = dim;
      is_tc_clockarray_proj lclk tc; 
      clockarray_emptypart lclk (tr_flatten tc); 
      (* only need to constrain that subtree? *)
      Forall (is_tc_clockarray_proj lclk') chn'; 
      is_tc_nodearray_proj_chnaux par' lnode' default_nodefield chn';
      (* need bound the size of top *)
      Z.of_nat (top + length (tc_get_updated_nodes_join_aux tc clk chn')) <= dim)
    PARAMS (p; p'; Vint (Int.repr (Z.of_nat par')); Vint (Int.repr (Z.of_nat clk)))
    SEP (data_at Tsh (tarray t_struct_clock dim) lclk' plclk';
      data_at Tsh (tarray t_struct_node dim) lnode' plnode';
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk', (plnode', (v2, v3))))) p';
      (* for self (tc), the clock part is static *)
      data_at Tsh (tarray t_struct_clock dim) lclk plclk;
      data_at Tsh (tarray tint dim) lstk plstk;
      (* TODO use treeclock_payload or not? *)
      data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tr_rootid tc)) 
        plclk plnode plstk ((Z.of_nat top) - 1)) p)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at Tsh (tarray t_struct_clock dim) lclk' plclk';
      data_at Tsh (tarray t_struct_node dim) lnode' plnode';
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk', (plnode', (v2, v3))))) p';
      (* for self (tc), the clock part is static *)
      data_at Tsh (tarray t_struct_clock dim) lclk plclk;
      data_at Tsh (tarray tint dim) 
        (firstn top lstk ++
         (map (fun x => Vint (Int.repr (Z.of_nat x))) 
            (map tr_rootid (tc_get_updated_nodes_join_aux tc clk chn'))) ++
          skipn (top + length (tc_get_updated_nodes_join_aux tc clk chn')) lstk) plstk;
      data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tr_rootid tc)) 
        plclk plnode plstk (Z.of_nat (top + length (tc_get_updated_nodes_join_aux tc clk chn')) - 1)) p).

(* make two function specs for node_is_null; one is straightforward, another is for use *)

Definition node_is_null_spec_local :=
  DECLARE _node_is_null
  (* WITH dim : Z, p : val, np : reptype t_struct_node *)
  WITH dim : Z, p : val, z1 : Z, z2 : Z, z3 : Z, z4 : Z
  PRE [ tptr t_struct_node ]
    (* PROP (0 <= dim <= Int.max_signed; node_struct_regular dim np) *)
    PROP (0 <= dim <= Int.max_signed; 
      default_nodefield <= z1 < dim;
      default_nodefield <= z2 < dim;
      default_nodefield <= z3 < dim;
      default_nodefield <= z4 < dim)
    PARAMS (p)
    SEP (data_at Tsh t_struct_node (node_payload z1 z2 z3 z4) p)
  POST [ tint ]
    PROP () 
    RETURN (Val.of_bool ((z1 =? default_nodefield) && (z2 =? default_nodefield) &&
      (z3 =? default_nodefield) && (z4 =? default_nodefield))%bool)
    SEP (data_at Tsh t_struct_node (node_payload z1 z2 z3 z4) p).
(* FIXME: rewrite this definition using tr_rootid to make it easier to deal with? *)
Definition node_is_null_as_bool tc (idx : nat) :=
  ((match tc with Node (mkInfo idx' _ _) nil => Nat.eqb idx idx' | _ => false end) ||
    (match tr_getnode idx tc with None => true | _ => false end))%bool.

Definition node_is_null_spec :=
  DECLARE _node_is_null
  WITH dim : Z, idx : nat, lnode : list (reptype t_struct_node),
    tc : treeclock, v1 : val, plnode : val, v2 : val, v3 : val, p : val
  PRE [ tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; Z.of_nat idx < dim; 
      Z.of_nat (tr_rootid tc) < dim; 
      Zlength lnode = dim; 
      nodearray_emptypart lnode (tr_flatten tc); is_tc_nodearray_proj_full lnode tc)
    PARAMS (offset_val (sizeof t_struct_node * Z.of_nat idx) plnode)
    SEP (data_at Tsh (tarray t_struct_node dim) lnode plnode;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tr_rootid tc))), 
          (v1, (plnode, (v2, v3))))) p)
  POST [ tint ]
    PROP () 
    RETURN (Val.of_bool (node_is_null_as_bool tc idx))
    SEP (data_at Tsh (tarray t_struct_node dim) lnode plnode;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tr_rootid tc))), 
          (v1, (plnode, (v2, v3))))) p).

Definition Gprog : funspecs :=
  ltac:(with_library prog [
    join_spec; 
    node_is_null_spec;
    detach_from_neighbors_spec;
    push_child_spec;
    get_updated_nodes_join_chn_spec
  ]).

Section Main_Proof.

Local Tactic Notation "saturate_lemmas" :=
  let simplegen lm := (let Hq := fresh "_Hyp" in pose proof lm as Hq) in
  (* gen short_max_signed_le_int_max_signed; 
  gen short_max_signed_gt_0;  *)
  simplegen Int.min_signed_neg.

(* TODO two design choices: make a pair of tactics (with aux equations), 
  or make a customized Corollary *)

Local Tactic Notation "array_focus" constr(idx) constr(plstruct) "witheqn" ident(Hy) :=
  (* TODO this part may be extracted to be a compatible generator *)
  match goal with |- context[data_at Tsh (tarray ?ty ?size) ?lstruct plstruct] => 
    ((match goal with _ : field_compatible (tarray ty size) [] plstruct |- _ => idtac end) +
    (let Hcomp := fresh "_Hcomp" in
      assert_PROP (field_compatible (tarray ty size) [] plstruct) as Hcomp by entailer));
    sep_apply (SingletonHole.array_with_hole_intro Tsh _ idx size lstruct); try lia 
  end;
  match goal with |- context[field_address (tarray ?a ?size) (SUB ?b) ?c] => 
    assert (field_address (tarray a size) (SUB b) c = offset_val (sizeof a * b) c) as Hy
    by (apply arr_field_address; try lia; try assumption) end; 
  (* for normalize *)
  Intros.

Local Tactic Notation "read_clock'" "witheqn" hyp(Eclock_payload) :=
  match type of Eclock_payload with 
  Znth ?n ?lclk = (_, _) => rewrite -> Eclock_payload; forward; rewrite <- Eclock_payload
  end.

Local Tactic Notation "read_clock" "witheqn" hyp(Eclock_payload) :=
  match type of Eclock_payload with 
  Znth ?n ?lclk = clock_payload ?clk ?aclk => 
    unfold clock_payload in Eclock_payload; read_clock' witheqn Eclock_payload; 
    fold (clock_payload clk aclk) in Eclock_payload
  end.

Local Tactic Notation "array_unfocus'" "witheqn" hyp(Hy) :=
  rewrite <- Hy; 
  sep_apply SingletonHole.array_with_hole_elim.

Local Tactic Notation "array_unfocus" "witheqn" hyp(Hy) :=
  array_unfocus' witheqn Hy;
  rewrite upd_Znth_triv; try lia; try reflexivity; try assumption; clear Hy.

Local Tactic Notation "rewrite_sem_add_ptr_int" :=
  simpl sem_binary_operation';
  repeat match goal with |- context[force_val (sem_add_ptr_int ?ty Signed ?p ?v)] => 
    ((match goal with _ : isptr p |- _ => idtac end) +
    (let Hisptr := fresh "_Hisptr" in
      assert_PROP (isptr p) as Hisptr by entailer));
    rewrite -> sem_add_pi'; auto; try lia; try solve [ unfold default_nodefield in *; lia ]
  end.

Local Tactic Notation "repable_signed_gen" constr(lis) :=
  let rec gen q := 
    (match eval cbn in q with
    | nil => idtac
    | ?x :: ?q' => 
      (let Hq := fresh "_Hyp" in assert (repable_signed x) as Hq by (unfold default_nodefield in *; hnf; lia));
      gen q'
    end) in gen lis.

Lemma body_node_is_null_pre: 
  semax_body Vprog Gprog f_node_is_null node_is_null_spec_local.
Proof.
  saturate_lemmas.

  start_function.
  (* destruct H0 as (z1 & z2 & z3 & z4 & -> & Hz1 & Hz2 & Hz3 & Hz4). *)
  (* TODO here we have to unfold default_nodefield ... this is not very good *)
  unfold node_payload, default_nodefield in *.
  repable_signed_gen (z1 :: z2 :: z3 :: z4 :: nil).
  forward.
  remember ((Z.eqb z1 (-1)) && (Z.eqb z2 (-1)))%bool as b1.
  forward_if (temp _t'1 (Val.of_bool b1)).
  { rewrite -> neg_repr in H4. apply repr_inj_signed in H4; auto.
    forward. forward.
    entailer!.
    rewrite -> Z.eqb_refl. simpl.
    f_equal. now apply repable_signed_Z_eqb_Int_eq.
  }
  { rewrite -> neg_repr in H4. apply repr_inj_signed' in H4; auto.
    forward.
    entailer!.
    apply Z.eqb_neq in H4. change (-(1)) with (-1) in H4. now rewrite -> H4.
  }
  remember (b1 && (Z.eqb z3 (-1)))%bool as b2.
  forward_if (temp _t'2 (Val.of_bool b2)).
  { clear Heqb1. subst b1. simpl in Heqb2.
    forward. forward.
    entailer!.
    f_equal. now apply repable_signed_Z_eqb_Int_eq.
  }
  { clear Heqb1. subst b1. simpl in Heqb2.
    forward.
    entailer!.
  }
  remember (b2 && (Z.eqb z4 (-1)))%bool as b3.
  forward_if (temp _t'3 (Val.of_bool b3)).
  { clear Heqb2. subst b2. simpl in Heqb3.
    forward. forward.
    entailer!.
    f_equal. now apply repable_signed_Z_eqb_Int_eq.
  }
  { clear Heqb2. subst b2. simpl in Heqb3.
    forward.
    entailer!.
  }
  forward.
  (* entailer!. f_equal. now rewrite -> andb_comm with (b1:=(z1 =? -1)). *)
Qed.

Fact node_payload_cmp z1 z2 z3 z4 z1' z2' z3' z4' dim (Hdim : 0 <= dim <= Int.max_signed)
  (H1 : default_nodefield <= z1 < dim) (H1' : default_nodefield <= z1' < dim)
  (H2 : default_nodefield <= z2 < dim) (H2' : default_nodefield <= z2' < dim)
  (H3 : default_nodefield <= z3 < dim) (H3' : default_nodefield <= z3' < dim)
  (H4 : default_nodefield <= z4 < dim) (H4' : default_nodefield <= z4' < dim) :
  node_payload z1 z2 z3 z4 = node_payload z1' z2' z3' z4' <->
  z1 = z1' /\ z2 = z2' /\ z3 = z3' /\ z4 = z4'.
Proof.
  split.
  - intros H.
    saturate_lemmas.
    unfold node_payload in H.
    repable_signed_gen (z1 :: z2 :: z3 :: z4 :: z1' :: z2' :: z3' :: z4' :: nil).
    let rec gen lis := (match lis with nil => idtac 
      | (?x, ?y) :: ?lis' => 
        (let Hq := fresh "Hqq" in 
          assert (Int.repr x = Int.repr y) as Hq by congruence;
          apply repr_inj_signed in Hq; auto; subst x); 
        gen lis'
    end) in gen ((z1, z1') :: (z2, z2') :: (z3, z3') :: (z4, z4') :: nil).
  - now intros (-> & -> & -> & ->).
Qed.

Fact default_nodestruct_cmp z1 z2 z3 z4 dim (Hdim : 0 <= dim <= Int.max_signed)
  (H1 : default_nodefield <= z1 < dim)
  (H2 : default_nodefield <= z2 < dim)
  (H3 : default_nodefield <= z3 < dim)
  (H4 : default_nodefield <= z4 < dim) :
  node_payload z1 z2 z3 z4 = default_nodestruct <->
  z1 = default_nodefield /\ z2 = default_nodefield /\ z3 = default_nodefield /\ z4 = default_nodefield.
Proof.
  apply node_payload_cmp with (dim:=dim); auto.
  all: unfold default_nodefield; lia.
Qed.

(* TODO is this subsumption proof really meaningful? *)

Lemma subsume_node_is_null : funspec_sub (snd node_is_null_spec_local) (snd node_is_null_spec).
Proof.
  saturate_lemmas.

  do_funspec_sub.
  destruct w as ((((((((dim, idx), lnode), tc), ?), plnode), ?), ?), p).
  entailer!.
  array_focus (Z.of_nat idx) plnode witheqn Etmp.
  match goal with H1 : context[is_tc_nodearray_proj_full], 
    H2 : context[nodearray_emptypart] |- _ => 
    pose proof (nodearray_proj_regular _ _ H1 H2) as Hreg end.
  rewrite -> Forall_forall_Znth in Hreg. 
  specialize (Hreg _ (conj (Zle_0_nat idx) H1)).
  destruct Hreg as (z1 & z2 & z3 & z4 & Es & Hz1 & Hz2 & Hz3 & Hz4).
  rewrite -> Es.
  rewrite -> Etmp.
  match type of Etmp with _ = ?v => Exists (((((Zlength lnode, v), z1), z2), z3), z4) end.
  match goal with |- (_ * ?a * ?b) |-- _ => Exists (a * b)%logic end.
  entailer!.
  intros. entailer!.
  2: array_unfocus witheqn Etmp; auto.

  (* pure proof *)
  split. 2: match goal with |- Val.of_bool ?b <> _ => now destruct b end.
  match goal with HH : _ = ?b |- _ = ?b => rewrite <- HH; clear HH end.
  f_equal.
  unfold node_is_null_as_bool.
  destruct (tr_getnode idx tc) as [ res | ] eqn:E.
  - rewrite -> orb_false_r.
    destruct tc as [ (u, ?, ?) [ | ch chn ] ] eqn:Etc.
    + simpl in E. 
      destruct (eqdec u idx) as [ -> | ]; simpl in E; try eqsolve.
      injection E as <-.
      match goal with H : context[is_tc_nodearray_proj_full] |- _ => 
        destruct H as (Hca & _) end.
      hnf in Hca. simpl in Hca.
      apply nth_error_Znth_result in Hca. rewrite -> Hca in Es.
      symmetry in Es. rewrite -> default_nodestruct_cmp with (dim:=Zlength lnode) in Es; auto.
      destruct Es as (-> & -> & -> & ->).
      now rewrite -> Nat.eqb_refl, -> ! Z.eqb_refl.
    + remember (ch :: chn) as chnn eqn:Echn.
      match goal with H : context[is_tc_nodearray_proj_full] |- _ => 
        destruct H as (Hca & Hproj) end.
      apply trs_find_has_id in E. destruct E as (Hin & Eid).
      simpl in Hin. destruct Hin as [ <- | Hin ].
      * simpl in Eid. subst u.
        hnf in Hca. simpl in Hca.
        apply nth_error_Znth_result in Hca. rewrite -> Hca, -> Echn in Es.
        cbn in Es.
        rewrite -> node_payload_cmp with (dim:=Zlength lnode) in Es; auto.
        all: try solve [ unfold default_nodefield; lia ].
        apply is_tc_nodearray_proj_headch_inrange in Hproj.
        now rewrite -> Echn in Hproj.
      * apply is_tc_nodearray_proj_regular_chn in Hproj; auto.
        simpl in Hproj.
        apply in_flat_map in Hin. destruct Hin as (ch' & Hin_ch' & Hin).
        rewrite -> Forall_forall in Hproj. specialize (Hproj _ Hin_ch').
        rewrite -> Foralltr_Forall_subtree, -> Forall_forall in Hproj. specialize (Hproj _ Hin).
        rewrite -> Eid in Hproj. 
        destruct Hproj as (z1' & z2' & z3' & z4' & Estruct & ? & ? & ? & ?).
        (* lia is more powerful than I have thought. *)
        rewrite -> Estruct, -> node_payload_cmp with (dim:=Zlength lnode) in Es; auto; try lia.
  - rewrite -> orb_true_r. 
    (* TODO repeating somewhere above? *)
    destruct (nth_error lnode idx) eqn:Ee.
    2:{ apply nth_error_None in Ee. rewrite <- ZtoNat_Zlength in Ee. lia. }
    pose proof Ee as Ee'. 
    apply nth_error_Znth_result in Ee'. 
    match goal with H : context[nodearray_emptypart] |- _ => 
      apply H in Ee; auto end. subst r.
    rewrite -> Es in Ee'. 

    rewrite -> default_nodestruct_cmp with (dim:=Zlength lnode) in Ee'; auto.
    destruct Ee' as (-> & -> & -> & ->).
    now rewrite -> ! Z.eqb_refl.
Qed.

Corollary body_node_is_null: 
  semax_body Vprog Gprog f_node_is_null node_is_null_spec.
Proof.
  eapply semax_body_funspec_sub.
  1: apply body_node_is_null_pre.
  1: apply subsume_node_is_null.
  compute. (* ? *)
  repeat constructor; simpl; lia.
Qed.

(* FIXME: need around 16 seconds to check this *)

Lemma body_get_updated_nodes_join_chn: 
  semax_body Vprog Gprog f_get_updated_nodes_join_chn get_updated_nodes_join_chn_spec.
Proof.
  saturate_lemmas.

  start_function.
  (* prepare *)
  unfold treeclock_payload.
  match goal with HH : context[is_tc_nodearray_proj_chnaux] |- _ => rename HH into Hprojn' end.
  match goal with HH : Forall (is_tc_clockarray_proj lclk') _ |- _ => rename HH into Hprojc' end.
  match goal with HH : context [Forall ?a chn'] |- _ => 
    match a with context[tc_rootclk] => rename HH into Hcb_chn' end end.
  match goal with HH : context [Foralltr ?a tc] |- _ => 
    match a with context[tc_rootclk] => rename HH into Hcb_tc end end.
  pose proof (is_tc_nodearray_proj_chnaux_tid_bounded _ _ _ _ Hprojn') as Htid.

  forward. forward.
  array_focus (Z.of_nat par') plnode' witheqn Etmp.
  rewrite -> Etmp.
  rewrite_sem_add_ptr_int.
  (* only read headch *)
  destruct (Znth (Z.of_nat par') lnode') as (z1, (z2, (z3, z4))) eqn:Es.
  simpl in z1, z2, z3, z4, Es.
  match goal with HH : node_struct_get_headch _ = _ |- _ => rename HH into Hs end.
  unfold node_struct_get_headch in Hs. subst z4.
  forward.
  array_unfocus witheqn Etmp.
  deadvars.

  (* use freeze to write less things *)
  (* or no? *)
  (* freeze (0 :: 1 :: 2 :: 3 :: nil) group. *)
  (* FIXME: use firstn & skipn, or simply something like pre & suf? *)
  forward_loop
  (EX i : nat, EX prev : Z, 
    PROP ((0%nat <= i <= length chn')%nat; 
      Forall (fun tc' => (clk < tc_rootaclk tc' \/ (tc_getclk (tr_rootid tc') tc) < tc_rootclk tc')%nat) (firstn i chn');
      (* ... *)
      is_tc_nodearray_proj_chnaux par' lnode' prev (skipn i chn'))
    LOCAL (temp _vprime_tid (Vint (Int.repr (tcs_head_Z (skipn i chn')))); (* changed *)
      (* temp _nd_par (offset_val (sizeof (Tstruct _Node noattr) * Z.of_nat par') plnode'); *)
      temp _self p; temp _tc p';
      temp _par_clock (Vint (Int.repr (Z.of_nat clk))))
    SEP (data_at Tsh (tarray t_struct_node dim) lnode' plnode';
      data_at Tsh (tarray t_struct_clock dim) lclk' plclk';
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk', (plnode', (v2, v3))))) p';
      data_at Tsh (tarray t_struct_clock dim) lclk plclk;
      data_at Tsh (tarray tint dim) 
        (firstn top lstk ++
          (map (fun y : nat => Vint (Int.repr (Z.of_nat y)))
            (map tr_rootid (tc_get_updated_nodes_join_aux tc clk (firstn i chn')))) ++
        skipn (top + length (tc_get_updated_nodes_join_aux tc clk (firstn i chn'))) lstk) plstk;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim),
          (Vint (Int.repr (Z.of_nat (tr_rootid tc))),
          (plclk, (plnode, (plstk, Vint (Int.repr 
            (Z.of_nat (top + length (tc_get_updated_nodes_join_aux tc clk (firstn i chn'))) - 1))))))) p))%assert.  (* this %assert really helps. *)
  1:{ (* first in *)
    Exists 0%nat default_nodefield. entailer!. 1: simpl; constructor.
    simpl. rewrite Nat.add_0_r, firstn_skipn. entailer.
  }
  Intros i prev.
  match goal with HH : is_tc_nodearray_proj_chnaux _ _ _ (skipn _ _) |- _ => rename HH into Hprojn'' end.
  (* this would be useful *)
  assert (default_nodefield <= tcs_head_Z_default default_nodefield (skipn i chn') < dim) as _Hyp11.
  {
    hnf. destruct (skipn i chn') as [ | ch ? ] eqn:E'; simpl; unfold default_nodefield. 
    - lia.
    - assert (In ch chn') as Hin by (apply skipn_In with (n:=i); rewrite E'; simpl; now left).
      rewrite Forall_forall in Htid. apply Htid in Hin. lia.
  }
  repable_signed_gen (tcs_head_Z_default default_nodefield (skipn i chn') :: nil).
  (* TODO would this be extracted? *)
  assert (Int.repr (tcs_head_Z_default default_nodefield (skipn i chn')) = Int.repr (-1) <->
    i = length chn') as Htmp.
  {
    split. 2: intros ->; now rewrite skipn_exact_length.
    intros Heq.
    destruct (Nat.leb (length chn') i) eqn:E.
    1: apply Nat.leb_le in E; lia.
    apply Nat.leb_gt in E.
    (* tricky *)
    destruct (skipn i chn') as [ | ch ? ] eqn:E'.
    - apply firstn_1_skipn with (d:=Node (mkInfo 0%nat 0%nat 0%nat) nil) in E.
      rewrite E' in E. now simpl in E.
    - simpl in _Hyp11, Heq. apply repr_inj_signed in Heq; auto. lia.
  }
  epose proof (tc_get_updated_nodes_join_aux_app tc clk (firstn i chn') (skipn i chn') ?[Goalq]) as Haux.
  [Goalq]: assumption.
  rewrite firstn_skipn in Haux.

  forward_if.
  2:{ (* final out *)
    match goal with HH : Int.repr _ = _ |- _ => rename HH into Heq end.
    rewrite Htmp in Heq. subst i.
    forward. 
    (* 
    thaw group. 
    (* hard to simpl, if used freeze! *)
    cbv delta [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] beta iota.
    fold Nat.add.
    *)
    entailer!. rewrite ! firstn_exact_length. apply derives_refl.
  }
  destruct (Nat.leb (length chn') i) eqn:E.
  1:{ apply Nat.leb_le in E. assert (i = length chn') as Etmp by lia. tauto. }
  apply Nat.leb_gt in E.
  (* destruct suffix; simplify tcs_head_Z *)
  destruct (skipn i chn') as [ | [ (v', clk_v', aclk_v') chn_v' ] chn'' ] eqn:Esuf.
  1: now simpl in *.
  cbn delta [tcs_head_Z_default tcs_head_Z tr_rootid tr_rootinfo] beta iota in *.
  change info_id with (@info_tid nat) in *. cbn delta [info_tid] beta iota in *.
  simpl in Haux, Hprojn''.
  destruct Hprojn'' as (Es_v' & Hprojn'').
  match goal with HH : Z.of_nat (top + _) <= _ |- _ => rename HH into Hlentop end.
  rewrite -> Haux, -> app_length in Hlentop.
  (* also note that firstn (S i) is what *)
  pose proof (firstn_skipn_onemore chn' i (Node (mkInfo v' clk_v' aclk_v') chn_v') chn'') as Honemore.
  rewrite -> Esuf in Honemore. specialize (Honemore eq_refl).
  destruct Honemore as (Hfsto & Hskpo).

  forward. forward. forward. forward.
  rewrite_sem_add_ptr_int.
  (* get clock *)
  array_focus (Z.of_nat v') plclk witheqn Etmp.
  rewrite -> Etmp.
  assert (0 <= Z.of_nat v' < Zlength lclk) as Eclk by lia.
  eapply clockarray_proj_tc_getinfo in Eclk; eauto. 
  rewrite ! Nat2Z.id in Eclk. rewrite Eclk.
  forward.
  pose proof (tc_getclk_in_int_range _ Hcb_tc v') as _Hyp12.
  rewrite <- Eclk. 
  array_unfocus witheqn Etmp.
  (* get clock, again *)
  array_focus (Z.of_nat v') plclk' witheqn Etmp.
  rewrite -> Etmp.
  pose proof Hprojc' as Eclk'. 
  pose proof Hcb_chn' as Hcb_v'.
  rewrite <- firstn_skipn with (n:=i), -> Forall_app, -> Esuf, -> Forall_cons_iff in Eclk', Hcb_v'.
  apply proj2, proj1 in Eclk', Hcb_v'.
  apply Foralltr_self, nth_error_Znth_result in Eclk'.
  simpl in Eclk', Hcb_v'.
  destruct Hcb_v' as (Hcb_clk_v' & Hcb_aclk_v').
  read_clock witheqn Eclk'. 
  (* if we use semax_if then we should not unfocus so early! *)
  (* 
  clear Eclk'.
  array_unfocus witheqn Etmp. 
  *)

  (* now use semax_if to make things slightly easier; TODO repeating? *)
  apply semax_if_seq. forward_if.
  {
    clear Eclk'.
    array_unfocus witheqn Etmp. 
    (* seems like sometimes the Int.sign (Int.repr ...) will be simplified *)
    destruct (clk_v' <=? tc_getclk v' tc)%nat eqn:Eclk_le.
    1: apply Nat.leb_le in Eclk_le; lia.
    (* need to show that top can safely add 1 *)
    assert (Z.of_nat (top + length (tc_get_updated_nodes_join_aux tc clk (firstn i chn'))) < dim) as Htop1 
      by (simpl in Hlentop; lia).
    forward. forward. rewrite add_repr. 
    match goal with |- context[?a - 1 + 1] => replace (a - 1 + 1) with a by lia end.
    forward. forward. forward.

    (* change to next ch *)
    forward. forward. 
    rewrite_sem_add_ptr_int.
    array_focus (Z.of_nat v') plnode' witheqn Etmp.
    rewrite -> Etmp.
    apply nth_error_Znth_result in Es_v'. rewrite -> Es_v'. unfold node_payload.
    forward.
    array_unfocus witheqn Etmp.

    Exists (S i) (Z.of_nat v'). entailer!. 
    - rewrite -> Hfsto. apply Forall_app; split; auto. constructor; auto. simpl. right. lia.
    - rewrite -> ! Hfsto, -> ! tc_get_updated_nodes_join_aux_app, -> ! map_app, -> app_length; auto.
      simpl. rewrite Eclk_le. simpl.
      apply sepcon_derives.
      + (* tedious *)
        replace (Zlength lclk) with (Zlength lstk) in Htop1 by congruence.
        rewrite -> Nat.add_1_r, <- plus_n_Sm.
        match type of Htop1 with Z.of_nat ?qq < _ => remember qq as top' eqn:Etop' end.
        match goal with |- context[map ?ff (map ?gg ?lisf)] => remember (map ff (map gg lisf)) as lis eqn:Elis end.
        rewrite <- app_assoc. simpl app. rewrite -> ! app_assoc with (m:=lis).
        destruct (skipn top' lstk) as [ | vtmp suf' ] eqn:Esuf'.
        1:{
          (* TODO repeating *)
          assert (top' < length lstk)%nat as Htop1' by (rewrite Zlength_correct in Htop1; lia).
          apply firstn_1_skipn with (d:=default) in Htop1'. rewrite Esuf' in Htop1'. discriminate.
        }
        rewrite -> (proj2 (firstn_skipn_onemore _ _ _ _ Esuf')).
        rewrite -> upd_Znth_char; auto.
        subst top' lis. rewrite -> Zlength_correct, -> app_length, -> ! map_length, -> firstn_length_le; auto.
        rewrite -> Zlength_correct in Htop1. lia.
      + match goal with |- context[Z.of_nat (?a + (?b + 1)) - 1] => 
          replace (Z.of_nat (a + (b + 1)) - 1) with (Z.of_nat (a + b)) by lia end.
        apply derives_refl.
  }
  {
    destruct (clk_v' <=? tc_getclk v' tc)%nat eqn:Eclk_le.
    2: apply Nat.leb_gt in Eclk_le; lia.
    read_clock witheqn Eclk'.
    clear Eclk'.
    array_unfocus witheqn Etmp. 

    forward_if.
    1:{ (* early stop *)
      destruct (aclk_v' <=? clk)%nat eqn:Eaclk_le.
      2: apply Nat.leb_gt in Eaclk_le; lia.
      rewrite app_nil_r in Haux.
      forward. entailer!.
      rewrite ! Haux. entailer!.
    }
    destruct (aclk_v' <=? clk)%nat eqn:Eaclk_le.
    1: apply Nat.leb_le in Eaclk_le; lia.

    (* change to next ch *)
    forward. forward. 
    rewrite_sem_add_ptr_int.
    array_focus (Z.of_nat v') plnode' witheqn Etmp.
    rewrite -> Etmp.
    apply nth_error_Znth_result in Es_v'. rewrite -> Es_v'. unfold node_payload.
    forward.
    array_unfocus witheqn Etmp.

    Exists (S i) (Z.of_nat v'). entailer!. 
    - rewrite -> Hfsto. apply Forall_app; split; auto. constructor; auto. simpl. left. lia.
    - rewrite -> ! Hfsto, -> ! tc_get_updated_nodes_join_aux_app, -> ! map_app, -> app_length; auto.
      simpl. rewrite Eclk_le, Eaclk_le. simpl. rewrite ! Nat.add_0_r, app_nil_r.
      entailer!.
  }
Qed.

Lemma body_push_child_pre: 
  semax_body Vprog Gprog f_push_child push_child_spec_local.
Proof.
  saturate_lemmas.

  start_function.
  unfold tc_subroot_rep, node_rep, node_payload. Intros.
  repable_signed_gen (Z.of_nat (tr_rootid sub) :: Z.of_nat par :: nil).
  forward. forward. 
  rewrite_sem_add_ptr_int. forward.
  (* operate *)
  match goal with |- semax _ ?pls _ _ => pose (qq:=pls) end.
  pattern (tc_chn_rep dim plnode plclk par default_nodefield default_nodefield chn) in qq.
  pose proof (eq_refl qq) as Htmp. subst qq. 
  match type of Htmp with ?f _ = _ => 
    forward_if (f (tc_chn_rep dim plnode plclk par default_nodefield (Z.of_nat (tr_rootid sub)) chn)) end.
  all: clear Htmp.
  {
    destruct chn as [ | ch chn ]; try contradiction.
    simpl tc_chn_rep. simpl tcs_head_Z. Intros.
    unfold node_rep, node_payload.
    forward. forward.
    rewrite_sem_add_ptr_int. forward.
    simpl tc_chn_rep. simpl tcs_head_Z. 
    unfold node_rep, node_payload. 
    entailer!.
  }
  {
    assert_PROP (chn = nil).
    {
      (* TODO can this be extracted? *)
      destruct chn as [ | ch chn ]. 1: entailer.
      simpl tc_chn_rep. Intros.
      repable_signed_gen (Z.of_nat (tr_rootid ch) :: nil).
      match goal with HH : Int.repr _ = _ |- _ => rename HH into Heq end.
      cbn in Heq. rewrite -> neg_repr in Heq. apply repr_inj_signed in Heq; auto. lia.
    }
    subst chn.
    simpl tc_chn_rep. simpl tcs_head_Z.
    forward. entailer!.
  }

  forward. forward. forward. forward.
  simpl tc_chn_rep.
  unfold node_rep, node_payload.
  entailer!. (* ? *) entailer.
Qed.

Lemma subsume_push_child : funspec_sub (snd push_child_spec_local) (snd push_child_spec).
Proof.
  saturate_lemmas.

  do_funspec_sub.
  destruct w as (((((((((((((dim, v1), plclk), plnode), v2), v3), p), tc), tc_par), sub), l), z1), z2), z3).
  Intros.
  (* first do subtree split *)
  unfold tc_rep at 1, tc_root_rep at 1.
  (* TODO streamline this? *)
  fold (tc_subroot_rep dim plnode plclk tc default_nodefield default_nodefield default_nodefield).
  match goal with HH : context[subtr_witness] |- _ => rename HH into Hsub end.
  rewrite TT_andp.
  sep_apply (tc_rep_subtree_frame _ _ _ Hsub).
  Intros z1' z2' z3'.
  destruct tc_par as [ni chn].
  unfold tc_subroot_rep at 1, node_rep at 1. Intros.
  unfold tc_rep_noroot at 1. fold tc_rep_noroot.
  unfold tc_headch_Z at 1, tcs_head_Z at 1.
  cbn delta [tr_rootchn tr_rootid tc_rootclk tc_rootaclk tr_rootinfo] beta iota in *.
  change info_id with (@info_tid nat) in *.

  Exists (((((((((((((((dim, v1), plclk), plnode), v2), v3), p), info_tid ni), chn), sub), 
    z1'), z2'), z3'), z1), z2), z3).
  (* entailer!. *)
  (* entailer! can be used to normalize this bundle *)
  match goal with |- (?a * _ * (_ * ?b) * ?c * (_ * (?d * _)))%logic |-- _ => Exists (a * b * c * d)%logic end.
  entailer!.
  intros. entailer!.
  allp_left (sub :: chn).
  entailer!. fold fold_right_sepcon.
  match goal with |- (_ * ?a * ?b * ?c * ?d * ?e * ?f * ?g)%logic |-- _ => 
    sep_apply (wand_frame_elim' (a * b * c * d * e * f * g)%logic) end.
  1:{
    unfold tc_subroot_rep, tc_rep_noroot.
    fold tc_rep_noroot.
    simpl. 
    change info_id with (@info_tid nat) in *.
    entailer!.
  }
  unfold tr_prepend_nodes, tr_locate_apply.
  rewrite Hsub.
  now unfold tc_rep.
Qed.

Corollary body_push_child: 
  semax_body Vprog Gprog f_push_child push_child_spec.
Proof.
  eapply semax_body_funspec_sub.
  1: apply body_push_child_pre.
  1: apply subsume_push_child.
  compute. (* ? *)
  repeat constructor; simpl; lia.
Qed.

Lemma body_detach_from_neighbors_pre: 
  semax_body Vprog Gprog f_detach_from_neighbors detach_from_neighbors_spec_local.
Proof.
  saturate_lemmas.

  start_function.
  match goal with HH : context[trs_roots_NoDupId] |- _ => rename HH into Hnodup end.
  sep_apply tc_chn_rep_segment.
  unfold tc_subroot_rep, node_rep, node_payload. Intros.
  repable_signed_gen (Z.of_nat (tr_rootid ch) :: nil).
  forward. forward. forward. forward. forward.
  rewrite_sem_add_ptr_int. forward.

  (* TODO this would result in some repetition, but anyway for now *)
  apply semax_if_seq. forward_if.
  { 
    (* has to use assert_PROP to get the range of (tr_rootid t) *)
    assert_PROP (pre = nil).
    {
      destruct pre as [ | t pre ]. 1: entailer.
      simpl tc_chn_rep. Intros.
      repable_signed_gen (Z.of_nat (tr_rootid t) :: nil).
      match goal with HH : Int.repr _ = Int.repr _ |- _ => rename HH into Heq end.
      cbn in Heq. apply repr_inj_signed in Heq; auto.
      hnf in Hnodup. simpl in Hnodup. apply NoDup_cons_iff, proj1 in Hnodup.
      rewrite map_app, in_app in Hnodup. simpl in Hnodup. lia.
    }
    subst pre.
    simpl app. simpl tc_chn_rep. 
    forward. simpl tcs_head_Z.

    forward_if.
    {
      assert (suf <> nil) as Hsuf by (destruct suf; auto).
      destruct suf as [ | t suf ]; try contradiction.
      simpl tc_chn_rep. simpl tcs_head_Z_default. Intros.
      unfold node_rep, node_payload. 
      forward. forward.
      rewrite_sem_add_ptr_int. forward.

      unfold tc_subroot_rep, node_rep, node_payload.
      simpl tc_chn_rep. simpl tcs_head_Z.
      do 3 EExists.
      entailer!.
    }
    {
      assert_PROP (suf = nil).
      {
        destruct suf as [ | t suf ]. 1: entailer.
        simpl tc_chn_rep. Intros.
        repable_signed_gen (Z.of_nat (tr_rootid t) :: nil).
        match goal with HH : Int.repr _ = _ |- _ => rename HH into Heq end.
        cbn in Heq. rewrite -> neg_repr in Heq. apply repr_inj_signed in Heq; auto. lia.
      }
      subst suf.
      forward.

      unfold tc_subroot_rep, node_rep, node_payload.
      do 3 EExists.
      entailer!.
    }
  }
  {
    assert (pre <> nil) as Hpre by (destruct pre; auto).
    apply exists_last in Hpre. destruct Hpre as (pre' & t' & ->).
    rewrite -> ! tcs_head_Z_default_rev_last'.
    (* still, need one segment *)
    rewrite -> tc_chn_rep_segment.
    simpl tc_chn_rep. simpl tcs_head_Z_default.
    unfold tc_subroot_rep, node_rep, node_payload. Intros.
    forward. forward. 
    rewrite_sem_add_ptr_int. forward.

    forward_if.
    {
      assert (suf <> nil) as Hsuf by (destruct suf; auto).
      destruct suf as [ | t suf ]; try contradiction.
      simpl tc_chn_rep. simpl tcs_head_Z_default. Intros.
      unfold node_rep, node_payload. 
      forward. forward.
      rewrite_sem_add_ptr_int. forward.

      rewrite ! tc_chn_rep_segment.
      simpl tc_chn_rep. simpl tcs_head_Z.
      unfold tc_subroot_rep, node_rep, node_payload.
      rewrite -> ! tcs_head_Z_default_notnil with (tcs:=(pre' ++ [t'])).
      2-3: try solve [ now destruct pre' ].
      rewrite -> tcs_head_Z_default_rev_last'.
      do 3 EExists.
      entailer!.
    }
    {
      assert_PROP (suf = nil).
      {
        destruct suf as [ | t suf ]. 1: entailer.
        simpl tc_chn_rep. Intros.
        repable_signed_gen (Z.of_nat (tr_rootid t) :: nil).
        match goal with HH : Int.repr _ = _ |- _ => rename HH into Heq end.
        cbn in Heq. rewrite -> neg_repr in Heq. apply repr_inj_signed in Heq; auto. lia.
      }
      subst suf.
      forward.

      rewrite app_nil_r. rewrite ! tc_chn_rep_segment.
      simpl tc_chn_rep. simpl tcs_head_Z.
      unfold tc_subroot_rep, node_rep, node_payload.
      rewrite -> ! tcs_head_Z_default_notnil with (tcs:=(pre' ++ [t'])).
      2: try solve [ now destruct pre' ].
      do 3 EExists.
      entailer!.
    }
  }
Qed.

Lemma subsume_detach_from_neighbors : funspec_sub (snd detach_from_neighbors_spec_local) (snd detach_from_neighbors_spec).
Proof.
  saturate_lemmas.

  do_funspec_sub.
  destruct w as (((((((((dim, v1), plclk), plnode), v2), v3), p), tc), l), sub).
  Intros.
  (* first do subtree split *)
  unfold tc_rep at 1, tc_root_rep at 1.
  (* TODO streamline this? *)
  fold (tc_subroot_rep dim plnode plclk tc default_nodefield default_nodefield default_nodefield).
  match goal with HH : context[subtr_witness] |- _ => rename HH into Hsub end.
  match goal with HH : l <> [] |- _ => rename HH into Hnotnil end.
  pose proof Hnotnil as (l' & x & El)%exists_last.
  pose proof Hsub as Hsub'. hnf in Hsub'. rewrite El, tr_locate_pos_app in Hsub'.
  destruct (tr_locate tc l') as [ [ni chn] | ] eqn:Etc_par; try discriminate. simpl in Hsub'.
  destruct (nth_error chn x) as [ ? | ] eqn:Enth; [ injection Hsub' as -> | discriminate ].
  pose proof Enth as (Hle & Elen & Echn & Esuf)%nth_error_mixin.
  rewrite TT_andp.
  sep_apply (tc_rep_subtree_frame _ _ _ Etc_par).
  Intros z1 z2 z3.
  unfold tc_subroot_rep at 1, node_rep at 1. Intros.
  unfold tc_rep_noroot at 1. fold tc_rep_noroot.
  (* match goal with HH : context[pre ++ sub :: suf] |- _ => rename HH into Echn end. *)
  (* simpl in Echn. subst chn. *)
  unfold tc_headch_Z at 1, tcs_head_Z at 1.
  rewrite Echn.
  cbn delta [tr_rootchn tr_rootid tc_rootclk tc_rootaclk tr_rootinfo] beta iota in *.
  change info_id with (@info_tid nat) in *.

  Exists (((((((((((((dim, v1), plclk), plnode), v2), v3), p), info_tid ni), firstn x chn), sub), skipn (S x) chn), z1), z2), z3).
  match goal with |- (?a * _ * (_ * ?b) * ?c * _)%logic |-- _ => Exists (a * b * c)%logic end.
  entailer!.
  split.
  2:{
    apply subtr_witness_subtr, id_nodup_subtr, id_nodup_tr_chn in Etc_par; eauto.
    rewrite Echn in Etc_par. simpl in Etc_par. 
    now apply id_nodup_root_chn_split.
  }
  intros. Intros z1' z2' z3'. Exists z1' z2' z3'. entailer!.
  allp_left (firstn x chn ++ skipn (S x) chn).
  fold fold_right_sepcon.
  rewrite -> map_app, -> fold_right_sepcon_app.
  cbn delta [fold_right_sepcon map] beta iota.
  entailer!.
  match goal with |- (_ * ?a * ?b * ?c * ?d * ?e)%logic |-- _ => 
    sep_apply (wand_frame_elim' (a * b * c * d * e)%logic) end.
  1:{
    unfold tc_subroot_rep, tc_rep_noroot.
    fold tc_rep_noroot.
    rewrite -> map_app, -> fold_right_sepcon_app.
    cbn delta [tr_rootchn tr_rootid tc_rootclk tc_rootaclk tr_rootinfo] beta iota.
    change info_id with (@info_tid nat) in *.
    entailer!.
  }
  unfold tr_remove_node, tr_locate_apply.
  rewrite list.last_snoc, removelast_last, Etc_par.
  now unfold tc_rep.
Qed.

Corollary body_detach_from_neighbors: 
  semax_body Vprog Gprog f_detach_from_neighbors detach_from_neighbors_spec.
Proof.
  eapply semax_body_funspec_sub.
  1: apply body_detach_from_neighbors_pre.
  1: apply subsume_detach_from_neighbors.
  compute. (* ? *)
  repeat constructor; simpl; lia.
Qed.

(* FIXME: this is way too long. need revise.
    for example, consider induction on tc or l? *)

Fact nodearray_proj_read_correct_pre sub pre tc : forall suf
  (Echn : tr_rootchn tc = pre ++ sub :: suf) (Hin : In sub (tr_rootchn tc))
  lnode prev (Hproj : is_tc_nodearray_proj_chnaux (tr_rootid tc) lnode prev (tr_rootchn tc)),
  Znth (Z.of_nat (tr_rootid sub)) lnode = node_payload 
    (tcs_head_Z suf) 
    (match (rev pre) with nil => prev | ch :: _ => Z.of_nat (tr_rootid ch) end) 
    (Z.of_nat (tr_rootid tc))
    (tc_headch_Z sub).
Proof.
  destruct tc as [(u, ?, ?) chn]. simpl. revert chn.
  induction pre as [ | q pre IH ]; intros.
  2: destruct pre eqn:E.
  1-2: simpl in Echn; subst chn; simpl in *; now apply nth_error_Znth_result.
  rewrite <- ! E in *. assert (pre <> nil) as Htmp by eqsolve. clear E.
  subst chn. simpl in Hproj. destruct Hproj as (_ & Hproj).
  erewrite -> IH with (suf:=suf). 2: reflexivity.
  2: simpl; rewrite -> in_app; simpl; tauto.
  2: apply Hproj.
  f_equal. apply exists_last in Htmp. destruct Htmp as (pre' & prev' & E).
  simpl. rewrite -> E, -> rev_app_distr. now simpl.
Qed. 

Fact nodearray_proj_read_correct sub pre tc : forall suf
  (Echn : tr_rootchn tc = pre ++ sub :: suf) (Hin : In sub (tr_rootchn tc))
  lnode (Hproj : is_tc_nodearray_proj_chnaux (tr_rootid tc) lnode default_nodefield (tr_rootchn tc)),
  Znth (Z.of_nat (tr_rootid sub)) lnode = node_payload 
    (tcs_head_Z suf) (tcs_head_Z (rev pre)) (Z.of_nat (tr_rootid tc)) (tc_headch_Z sub).
Proof. intros. now apply nodearray_proj_read_correct_pre. Qed.

Theorem body_join: 
  semax_body Vprog Gprog f_join join_spec.
Proof.
  saturate_lemmas.

  start_function.
  (* prepare *)
  unfold treeclock_rep.
  Intros. Intros lclk lnode lstk.
  Intros. Intros lclk' lnode' lstk'.
  unfold treeclock_payload.
  match goal with HH : tc_shape_inv tc |- _ => rename HH into Hshape end.
  match goal with HH : tc_shape_inv tc' |- _ => rename HH into Hshape' end.
  match goal with HH : tc_respect tc' tc |- _ => rename HH into Hrespect end.
  match goal with HH : is_tc_nodearray_proj_full lnode _ |- _ => rename HH into Hprojn1 end.
  match goal with HH : is_tc_nodearray_proj_full lnode' _ |- _ => rename HH into Hprojn1' end.
  match goal with HH : nodearray_emptypart lnode _ |- _ => rename HH into Hprojn2 end.
  match goal with HH : nodearray_emptypart lnode' _ |- _ => rename HH into Hprojn2' end.
  match goal with HH : is_tc_clockarray_proj lclk _ |- _ => rename HH into Hprojc1 end.
  match goal with HH : is_tc_clockarray_proj lclk' _ |- _ => rename HH into Hprojc1' end.
  match goal with HH : clockarray_emptypart lclk _ |- _ => rename HH into Hprojc2 end.
  match goal with HH : clockarray_emptypart lclk' _ |- _ => rename HH into Hprojc2' end.
  match goal with HH : Zlength lstk = _ |- _ => rename HH into Hlen_lstk end.
  match goal with HH : Zlength lclk = _ |- _ => rename HH into Hlen_lclk end.
  match goal with HH : Zlength lnode = _ |- _ => rename HH into Hlen_lnode end.
  match goal with HH : Zlength lstk' = _ |- _ => rename HH into Hlen_lstk' end.
  match goal with HH : Zlength lclk' = _ |- _ => rename HH into Hlen_lclk' end.
  match goal with HH : Zlength lnode' = _ |- _ => rename HH into Hlen_lnode' end.
  match goal with HH : Z.of_nat (tr_rootid tc) < dim |- _ => rename HH into Hlt end.
  match goal with HH : Z.of_nat (tr_rootid tc') < dim |- _ => rename HH into Hlt' end.
  match goal with HH : context [Foralltr ?a tc] |- _ => 
    match a with context[tc_rootclk] => rename HH into Hcb_tc end end.
  match goal with HH : context [Foralltr ?a tc'] |- _ => 
    match a with context[tc_rootclk] => rename HH into Hcb_tc' end end.
  epose proof (is_tc_nodearray_proj_tid_bounded _ _ (proj2 Hprojn1) ?[Goalq]) as Htid.
  [Goalq]: congruence.
  epose proof (is_tc_nodearray_proj_tid_bounded _ _ (proj2 Hprojn1') ?[Goalq]) as Htid'.
  [Goalq]: congruence.
  rewrite -> Hlen_lnode in Htid.
  rewrite -> Hlen_lnode' in Htid'.
  (* "ca" stands for "clock array" *)
  pose proof (is_tc_clockarray_proj_nth _ _ Hprojc1) as Hca_tc.
  pose proof (is_tc_clockarray_proj_nth _ _ Hprojc1') as Hca_tc'.
  assert (0 < dim) as Hdim by lia.
  pose proof (tid_nodup Hshape) as Hnodup.
  pose proof (tid_nodup Hshape') as Hnodup'.
  (* the actual join operand is the prefix *)
  pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
  remember (tc_get_updated_nodes_join tc tc') as pf eqn:Epf.
  pose proof (id_nodup_prefix_preserve Hprefix Hnodup') as Hnodup_pf.
  pose proof (prefixtr_rootid_same Hprefix) as Epf_id.
  pose proof (prefixtr_rootinfo_same Hprefix) as Epf_info.
  pose proof (fun (tr1 tr2 : treeclock) (H : prefixtr tr1 tr2) t => ssrbool.contra_not (prefixtr_flatten_id_incl H t)) as Hnotin_prefix.

  forward. forward. 
  forward_if.
  {
    match goal with H : _ |- _ => apply Nat2Z.inj in H; rename H into Erootid end.
    apply tc_join_roottid_same_trivial in Erootid; try assumption.
    forward. 
    (* EExists does not work well here *)
    unfold treeclock_rep at 1. Exists lclk lnode lstk.
    unfold treeclock_rep at 1. Exists lclk' lnode' lstk'.
    rewrite -> ! Erootid.
    entailer!.
  }

  match goal with H : _ |- _ => rewrite -> Nat2Z.inj_iff in H; rename H into Hrootid end.

  forward. forward. forward.

  array_focus (Z.of_nat (tr_rootid tc')) plclk' witheqn Etmp.
  rewrite_sem_add_ptr_int.
  pose proof (Foralltr_self Hca_tc') as Etmp2. cbn in Etmp2.
  rewrite -> Etmp.
  read_clock witheqn Etmp2. clear Etmp2.
  array_unfocus witheqn Etmp.

  forward. forward. forward. forward.
  rewrite_sem_add_ptr_int. 
  array_focus (Z.of_nat (tr_rootid tc')) plclk witheqn Etmp.
  rewrite -> Etmp.
  assert (Z.of_nat (tr_rootid tc') < Zlength lclk) as Eclk by congruence.
  apply clockarray_proj_tc_getinfo' with (tc:=tc) in Eclk; try assumption.
  read_clock' witheqn Eclk. clear Eclk.
  array_unfocus witheqn Etmp.

  (* range guarantee *)
  pose proof Hcb_tc' as Hcb_tc'root. apply Foralltr_self, proj1 in Hcb_tc'root.
  pose proof (tc_getclk_in_int_range _ Hcb_tc (tr_rootid tc')) as Hcb_tc'root_getclk.

  forward_if.
  {
    match goal with HH : (Z.of_nat ?a >= Z.of_nat ?b) |- _ => assert (b <= a)%nat as Hle by lia end.
    forward.
    rewrite tc_join_trivial by assumption.
    unfold treeclock_rep at 1. Exists lclk lnode lstk.
    unfold treeclock_rep at 1. Exists lclk' lnode' lstk'.
    entailer!.
  }

  match goal with HH : (Z.of_nat (tc_getclk (tr_rootid tc') tc) < _) |- _ => 
    rewrite <- Nat2Z.inj_lt in HH; rename HH into Hlt_getclk end.

  (* can conclude this only after the first if check *)
  (* ... but cannot conclude that the rootid of tc is not in tc'! *)
  assert (~ In (tr_rootid tc) (map tr_rootid (tr_flatten pf))) as Hrootid'.
  { subst pf. intros Hin%tr_getnode_in_iff%tc_get_updated_nodes_join_sound; auto. 
    rewrite tc_getclk_as_fmap, tr_getnode_self in Hin. simpl in Hin. lia.
  }

  forward_call.
  (* retract *)
  (* TODO extract this to be a lemma? need to revise the parts related with "node_is_null_as_bool" *)
  pose (vret:=match tr_getnode (tr_rootid tc') tc with None => true | _ => false end).
  replace (node_is_null_as_bool tc (tr_rootid tc')) with vret.
  2:{
    subst vret. unfold node_is_null_as_bool. destruct tc as [(u, ?, ?) [ | ]]; simpl; auto.
    simpl in Hrootid. apply Nat.eqb_neq in Hrootid. now rewrite -> Nat.eqb_sym, -> Hrootid.
  }

  (* before going forward, prepare for the node to be detached and change the representation format *)
  pose proof (tc_join_partial_iterative_init Hnodup Hrootid') as Ejoin0.
  destruct (tc_detach_nodes (pf :: nil) tc) as (pivot0, forest0) eqn:E0.
  pose (sub:=hd (Node (mkInfo (tr_rootid tc') 0%nat 0%nat) nil) forest0).
  replace (option.from_option _ _ _) with (tr_rootchn sub) in Ejoin0
    by (subst sub; now destruct forest0).
  rewrite Epf_id, (tc_rootinfo_clk_inj Epf_info) in Ejoin0.
  unfold tr_prepend_nodes, tr_locate_apply in Ejoin0. 
  rewrite (tree_recons pivot0) in Ejoin0. simpl in Ejoin0.

  sep_apply (tc_array2rep_and_bag plclk plnode _ _ _ tc Hlen_lclk Hlen_lnode).
  Intros.
  deadvars.
  freeze (map Z.of_nat (seq 3%nat 5%nat)) Fr.

  (* lightweight postcondition declaration *)
  (* proving forest at the same time may be convenient *)
  match goal with |- context[PROPx _ (LOCALx ?b (SEPx ?c))] =>
    match c with (?preserved :: _) => 
    forward_if (EX z1 z2 z3 : Z, PROPx 
      ((tr_rootid sub = tr_rootid tc') :: nil) (* TODO well ... this might be derived from the pure reasoning? *)
      (LOCALx b (SEPx [preserved; 
      tc_subroot_rep dim plnode plclk sub z1 z2 z3;
      tc_rep_noroot dim plnode plclk sub; 
      tc_rep dim plnode plclk pivot0; 
      (* dealing with bag here should be better *)
      unused_bag_rep dim plnode plclk (tr_flatten (tc_join_partial tc (Node (tr_rootinfo pf) nil))); 
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tr_rootid tc))), (plclk, (plnode, (plstk, Vint (Int.repr (-1))))))) p])))%assert end end.
  {
    (* (tr_rootid tc') exists in tc *)
    subst vret.
    destruct (tr_getnode (tr_rootid tc') tc) as [ res | ] eqn:Eres.
    (* TODO why is this not streamlined? *)
    2:{ 
      match goal with HH : context[typed_true] |- _ => rename HH into Htmp end.
      unfold eval_unop in Htmp. simpl in Htmp. now apply typed_true_tint_Vint in Htmp.
    }
    apply trs_find_has_id in Eres. destruct Eres as ((l & Eres)%subtr_subtr_witness & Eid).
    destruct (list_ifnil_destruct l) as [ -> | Hnotnil ].
    1: injection Eres as ->; contradiction.
    (* use detach single and transform into remove node *)
    pose proof (tc_detach_nodes_single Eres Hnodup Hnotnil) as Htmp.
    erewrite -> tc_detach_nodes_tcs_congr with (tcs2:=(pf :: nil)) in Htmp.
    2: intros; simpl; rewrite Eid, Epf_id; auto.
    rewrite Htmp in E0. apply pair_equal_split in E0. destruct E0 as (<- & <-). 
    simpl in sub. subst sub. 

    forward_call (dim, Vint (Int.repr (Z.of_nat (tr_rootid tc))), plclk, plnode, plstk, Vint (Int.repr (-1)), p, 
      tc, l, res).
    1:{ entailer!. simpl. now rewrite Eid. }
    Intros vret. destruct vret as ((z1, z2), z3). Exists z1 z2 z3.
    entailer!.
    entailer!. (* ? *)
    (* change bag *)
    (* TODO put this to pure part? *)
    simpl in Ejoin0.
    erewrite -> unused_bag_rep_perm. 
    1: apply derives_refl.
    epose proof (tc_detach_nodes_dom_partition _ _) as Hperm%Permutation_rootinfo2rootid.
    rewrite Htmp in Hperm. simpl in Hperm. rewrite Hperm, <- Ejoin0, map_app, app_nil_r.
    rewrite (tree_recons (tr_remove_node tc l)). simpl.
    destruct res. simpl in Eid |- *. rewrite Eid, map_app. 
    list.solve_Permutation.
  }
  {
    subst vret.
    destruct (tr_getnode (tr_rootid tc') tc) as [ res | ] eqn:Eres.
    1:{ 
      match goal with HH : context[typed_false] |- _ => rename HH into Htmp end.
      unfold eval_unop in Htmp. simpl in Htmp. now apply typed_false_tint_Vint in Htmp.
    }
    pose proof Eres as Eres'%trs_find_in_iff_neg.
    (* use intact *)
    rewrite tc_detach_nodes_intact' in E0.
    2: simpl; intros ?? [ <- | [] ]; congruence.
    apply pair_equal_split in E0. destruct E0 as (<- & <-).
    simpl in sub.
    (* get one from the bag *)
    rewrite -> unused_bag_rep_alloc with (tc:=sub); auto.
    subst sub. forward. simpl tr_rootid.
    do 3 Exists default_nodefield.
    unfold tc_subroot_rep, clock_rep, node_rep, default_clockstruct, default_nodestruct.
    entailer!.
    1: simpl; lia. (* ... *)
    simpl. normalize.
    (* change bag *)
    simpl in Ejoin0.
    erewrite -> unused_bag_rep_perm. 
    1: apply derives_refl.
    rewrite <- Ejoin0. simpl.
    rewrite (tree_recons tc). simpl.
    list.solve_Permutation.
  }

  Intros z1 z2 z3.
  match goal with HH : tr_rootid sub = tr_rootid tc' |- _ => rename HH into Eid end.
  thaw Fr. rewrite -> ! Nat2Z.id. deadvars. clear vret.
  unfold tc_subroot_rep, clock_rep, clock_payload. rewrite -> ! Eid. Intros.

  forward. forward. forward.
  rewrite_sem_add_ptr_int.
  (* since the representation format is not array, it is not very easy to read (tc_rootclk tc) ... *)
  unfold tc_rep, tc_root_rep, clock_rep, clock_payload.
  (* FIXME: this is bad ... we need to maintain equalities here *)
  Intros.
  pose proof (tc_detach_nodes_fst_rootinfo_same (pf :: nil) tc) as Htmp.
  rewrite E0 in Htmp. simpl in Htmp.
  pose proof (tr_rootinfo_id_inj Htmp) as Htmp_tid.
  pose proof (tc_rootinfo_clk_inj Htmp) as Htmp_clk.
  (* pose proof (tc_rootinfo_aclk_inj Htmp) as Htmp_aclk. *)
  rewrite Htmp_tid. forward. rewrite Htmp_clk. forward.
  rewrite <- Htmp_tid.

  (* we may possibly use the local spec here, but anyway *)
  (* have to change clk & aclk of sub before pushing child *)
  set (sub':=Node _ (tr_rootchn _)) in Ejoin0.
  freeze (0 :: 1 :: 2 :: 3 :: 4 :: 11 :: nil) Fr.
  forward_call (dim, Vint (Int.repr (Z.of_nat (tr_rootid tc))), plclk, plnode, plstk, Vint (Int.repr (-1)), p, 
    pivot0, pivot0, sub', @nil nat, z1, z2, z3).
  1:{
    subst sub'.
    unfold tc_subroot_rep, tc_rep, tc_root_rep, clock_rep, clock_payload.
    simpl.
    rewrite <- Htmp_tid, <- Htmp_clk.
    entailer!.
    unfold tc_headch_Z. simpl. entailer!. 
    rewrite <- Eid, (tree_recons sub).
    simpl.
    change info_id with (@info_tid nat).
    entailer!.
  }

  (* turn to the initial partial join *)
  thaw Fr. 
  cbv delta [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] beta iota.
  deadvars.
  subst sub'.
  rewrite (tree_recons pivot0).
  unfold tr_prepend_nodes, tr_locate_apply.
  simpl. rewrite Ejoin0.
  clear dependent pivot0. clear dependent forest0. 

  (* congruence ... *)
  pose proof (tc_get_updated_nodes_join_aux_tc_congr_partialjoin Hnodup Hnodup' (pos':=nil) eq_refl) as Egj.
  rewrite <- Epf in Egj.
  specialize (Egj ltac:(assumption) _ ltac:(reflexivity) Epf (tc_getclk (tr_rootid tc') tc)).
  unfold post_iter_visited_prefix in Egj. simpl tr_vsplitr in Egj.

  (* length ... *)
  match type of Egj with map ?ff ?al = map ?ff ?bl => assert (length al = length bl) as Elen
    by (rewrite <- ! map_length with (f:=ff), -> Egj; reflexivity) end.
  (* TODO streamline this? seems like map_map does not work well here *)
  apply f_equal with (f:=map info_id) in Egj.
  rewrite -> ! map_map in Egj.
  do 2 rewrite -> map_ext with (f:=(fun x : treeclock => info_id (tr_rootinfo x))) (g:=tr_rootid) in Egj; auto.

  (* fold *)
  unfold tc_rep. sep_apply tc_rep_and_bag2array.
  1:{
    apply tc_join_partial_id_nodup; simpl; try assumption.
    1: constructor; auto; constructor.
    rewrite Epf_info. intuition.
  }
  Intros lnode0 lclk0.
  clear dependent lnode.
  clear dependent lclk.
  forward_call (dim, tc_join_partial tc (Node (tr_rootinfo pf) nil), plclk, plnode, plstk, 0%nat, p, 
    Vint (Int.repr (Z.of_nat (tr_rootid tc'))), plclk', plnode', plstk', Vint (Int.repr (-1)), p', 
    tc_getclk (tr_rootid tc') tc, tr_rootid tc', tr_rootchn tc', lclk0, lstk, lclk', lnode').
  1: rewrite (tr_rootinfo_id_inj (tc_join_partial_rootinfo_same _ _)); entailer!.
  1:{
    split.
      (* this is interesting. originally I think I have to use tc_join_partial_getclk_in_int_range, 
          but it turns out that the post-condition already gives what I want. 
        is this just coincidence? *)
    1: match goal with HH : Foralltr _ (tc_join_partial _ _) |- _ => revert HH; now apply Foralltr_impl end.
    split.
    1: now apply Foralltr_chn_selves.
    split.
    1:{ 
      destruct Hprojn1' as (Hroot' & _). 
      apply nth_error_Znth_result in Hroot'. 
      rewrite Hroot'. now simpl.
    }
    split.
    1:{ apply Foralltr_chn_selves. now apply Foralltr_idempotent in Hprojc1'. }
    split.
    1: now apply proj2, Foralltr_self in Hprojn1'.

    simpl. rewrite -> Elen.
    (* play with inequality *)
    (* TODO (1) need to revise the spec for get_..._chn (2) put these into the pure part? they should be reusable *)
    transitivity (Z.of_nat (length (tr_rootchn tc'))).
    1:{
      pose proof (tc_get_updated_nodes_join_aux_result_submap 
        tc (tc_getclk (tr_rootid tc') tc) (tr_rootchn tc')) as (chn' & Hsl & E).
      rewrite E, map_length. 
      apply list.sublist_length in Hsl.
      lia.
    }
    transitivity (Z.of_nat (tr_size tc')).
    1: pose proof (tr_size_chn_lt_full tc'); lia.
    now apply tr_size_bounded_by_dim.
  }
  (* go back to tc *)
  simpl. rewrite -> ! Elen, -> ! Egj. clear Elen Egj.

  (* now prepare for the loop invariant *)
  deadvars.
  forward_loop
  (EX lstk_pre : list nat, EX lstk_suf : list val, EX pfi : treeclock,
    EX lclk : list (reptype t_struct_clock), EX lnode : list (reptype t_struct_node),
    PROP ( (* seems like we do not need to specify the length? *)
      (* (Zlength lstk_pre + Zlength lstk_suf = dim)%Z; *)
      traversal_invariant (tc_get_updated_nodes_join tc tc') lstk_pre pfi;
      nodearray_emptypart lnode (tr_flatten (tc_join_partial tc pfi));
      is_tc_nodearray_proj_full lnode (tc_join_partial tc pfi);
      clockarray_emptypart lclk (tr_flatten (tc_join_partial tc pfi));
      is_tc_clockarray_proj lclk (tc_join_partial tc pfi);
      Zlength lclk = dim;
      Zlength lnode = dim;
      (* this could be useful *)
      Foralltr
        (fun sub : treeclock =>
         Z.of_nat (tr_rootid sub) < dim /\
         Z.of_nat (tc_rootclk sub) <= Int.max_signed /\
         Z.of_nat (tc_rootaclk sub) <= Int.max_signed) (tc_join_partial tc pfi); 
      (* interesting enough, this is actually required *)
      (* TODO this can be put into pure part ...? *)
      ~ In (tr_rootid tc') lstk_pre)
    LOCAL (temp _self p; temp _tc p')
    SEP (data_at Tsh (tarray t_struct_clock dim) lclk' plclk';
      data_at Tsh (tarray t_struct_node dim) lnode' plnode';
      data_at Tsh (tarray tint dim) lstk' plstk';
      data_at Tsh t_struct_treeclock (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tr_rootid tc'))),
        (plclk', (plnode', (plstk', Vint (Int.repr (-1))))))) p';
      data_at Tsh (tarray t_struct_clock dim) lclk plclk;
      data_at Tsh (tarray t_struct_node dim) lnode plnode;
      data_at Tsh (tarray tint dim) (map (fun x : nat => Vint (Int.repr (Z.of_nat x))) lstk_pre ++ lstk_suf) plstk;
      data_at Tsh t_struct_treeclock
        (* TODO need to rethink what id to fill in below *)
        (treeclock_payload dim (Z.of_nat (tr_rootid (tc_join_partial tc pfi))) plclk plnode plstk
          (Zlength lstk_pre - 1)) p))%assert.
  1:{ (* enter the loop *)
    do 2 EExists. Exists (Node (tr_rootinfo pf) nil) lclk0 lnode0.
    entailer!.
    - split.
      + pose proof (traversal_invariant_init (tc_get_updated_nodes_join tc tc')) as Hini.
        subst pf. destruct tc'. apply Hini.
      + (* TODO streamline this? like ~ In (map rootid (rootchn ...)) *)
        rewrite (tree_recons pf), Epf, tc_get_updated_nodes_join_eta, (tree_recons tc') in Hnodup_pf.
        simpl in Hnodup_pf.
        apply id_nodup_rootid_neq, Foralltr_Forall_chn_comm, Foralltr_self in Hnodup_pf.
        simpl in Hnodup_pf.
        intros (ch' & Eid'%eq_sym & Hin)%in_map_iff.
        revert ch' Hin Eid'.
        now rewrite <- Forall_forall.
    - rewrite -> Zlength_map, <- Zlength_correct.
      apply derives_refl.
  }

  Intros lstk_pre lstk_suf pfi lclk lnode.
  assert_PROP (Zlength ((map (fun x : nat => Vint (Int.repr (Z.of_nat x))) lstk_pre ++ lstk_suf)) = dim)%Z 
    as Hlensum by entailer!.
  rewrite -> Zlength_app, -> Zlength_map in Hlensum.
  match goal with HH : traversal_invariant _ _ _ |- _ => rename HH into Htts end.
  unfold treeclock_payload.
  match goal with HH : Foralltr _ (tc_join_partial _ _) |- _ => 
    rewrite Foralltr_and in HH; destruct HH as (Htid_parjoin & Hcb_parjoin) end.
  match goal with HH : ~ In _ lstk_pre |- _ => rename HH into Hnotin_tc' end.

  forward. forward_if.
  2:{ (* end of traversal *)
    match goal with HH : Zlength lstk_pre - 1 < 0 |- _ => rename HH into Hl0; rewrite Zlength_correct in Hl0 end.
    destruct lstk_pre; [ | simpl in Hl0; lia ].
    simpl. replace (Zlength _ - 1) with (-1) by list_solve.
    apply traversal_invariant_stacknil in Htts.
    rewrite <- Epf in Htts. subst pfi pf.
    (* now we get actual join *)
    assert (tc_join_partial tc (tc_get_updated_nodes_join tc tc') = tc_join tc tc') as Ejoin.
    { rewrite -> tc_join_go; try reflexivity. lia. }
    rewrite -> Ejoin in *.
    forward. entailer!.
    unfold treeclock_rep at 1. Exists lclk lnode lstk_suf.
    unfold treeclock_rep at 1. Exists lclk' lnode' lstk'.
    entailer!.
    unfold tr_rootid.
    rewrite <- Ejoin, -> tc_join_partial_rootinfo_same.
    fold (tr_rootid tc).
    congruence.
  }

  clear z1 z2 z3.
  assert (lstk_pre <> nil) as Hnotnil by (intros ->; list_solve).
  match goal with HH : Zlength lstk_pre - 1 >= 0 |- _ => rename HH into Hlen_lstk_pre_ge0 end.
  apply traversal_invariant_stacknotnil in Htts; try assumption. 
  rewrite <- Epf in Htts.
  destruct Htts as (l & sub & Hnotnil_l & Hprefix_sub & Elstk_pre & Epfi).
  pose proof (pre_iter_visited_is_prefix pf l) as Hprefix_pfi. 
  rewrite <- Epfi in Hprefix_pfi.
  (* similar preparation as above *)
  pose proof (id_nodup_prefix_preserve Hprefix_pfi Hnodup_pf) as Hnodup_pfi.
  pose proof (prefixtr_rootid_same Hprefix_pfi) as Epfi_id.
  pose proof (prefixtr_rootinfo_same Hprefix_pfi) as Epfi_info.
  rewrite -> map_app in Elstk_pre.
  simpl in Elstk_pre.

  (* more preparation *)
  pose proof (stack_top_not_visited Hprefix_sub Hnotnil_l Hnodup_pf) as H_sub_notin_pfi.
  rewrite <- Epfi in H_sub_notin_pfi.
  assert (tr_rootid sub <> tr_rootid tc') as Hrootid_sub'.
  { 
    rewrite <- Epf_id.
    eapply id_nodup_diff_by_pos with (tr:=pf); eauto. reflexivity.
  }
  assert (~ In (tr_rootid tc) (map tr_rootid (tr_flatten pfi))) as Hrootid''
    by (subst pfi; eapply Hnotin_prefix; eauto).
  pose proof (tc_join_partial_rootinfo_same tc pfi) as Eparjoin_info.
  assert (tr_NoDupId (tc_join_partial tc pfi)) as Hnodup_parjoin
    by now apply tc_join_partial_id_nodup.
  (* prepare bound and lt conditions *)
  pose proof (prefixtr_flatten_info_incl Hprefix) as Hprefix_all_info.
  assert (In (tr_rootinfo sub) (map tr_rootinfo (tr_flatten tc'))) as (subo & Esub_info & Hsubo)%in_map_iff
    by (eapply Hprefix_all_info, in_map, subtr_witness_subtr; eauto).
  pose proof Hsubo as Hsub_tid.
  eapply Foralltr_subtr in Hsub_tid. 2: apply Htid'.
  pose proof Hsubo as Hcb_sub_clk.
  eapply Foralltr_subtr in Hcb_sub_clk. 2: apply Hcb_tc'.
  pose proof Hsubo as Es_sub_clk.
  eapply Foralltr_subtr in Es_sub_clk. 2: apply Hca_tc'.
  simpl in Hsub_tid, Hcb_sub_clk, Es_sub_clk.
  rewrite (tr_rootinfo_id_inj Esub_info) in Hsub_tid, Es_sub_clk.
  rewrite (tc_rootinfo_clk_inj Esub_info), (tc_rootinfo_aclk_inj Esub_info) in Hcb_sub_clk, Es_sub_clk.
  clear dependent subo.
  destruct Hcb_sub_clk as (Hcb_sub_clk & Hcb_sub_aclk).

  (* read stack top *)
  forward. forward. forward. 
  rewrite sub_repr.
  (* TODO why even reading stack is so difficult ... *)
  match goal with |- context[map ?ff lstk_pre] => rewrite -> (f_equal (map ff) Elstk_pre), -> ! map_app end.
  simpl map.
  rewrite <- app_cons_assoc.
  match type of Elstk_pre with _ = ?ll ++ _ => 
    assert (Zlength (map (fun x : nat => Vint (Int.repr (Z.of_nat x))) ll) = Zlength lstk_pre - 1) 
    as Hlen_lstk_pre_pre by (subst lstk_pre; list_solve) end.
  rewrite <- Hlen_lstk_pre_pre.
  forward.
  1: entailer!.
  1:{
    rewrite -> sublist.Znth_app1; auto. 
    entailer!.
  }
  rewrite -> sublist.Znth_app1; auto.
  deadvars. rewrite Hlen_lstk_pre_pre. clear Hlen_lstk_pre_pre.

  (* from now on, mainly repeating the proof above *)

  forward. forward. forward. forward. forward. forward.
  deadvars.
  rewrite_sem_add_ptr_int.
  array_focus (Z.of_nat (tr_rootid sub)) plclk witheqn Etmp.
  rewrite -> Etmp.
  assert (Z.of_nat (tr_rootid sub) < Zlength lclk) as Eclk by congruence.
  apply clockarray_proj_tc_getinfo' with (tc:=tc_join_partial tc pfi) in Eclk; try assumption.
  rewrite tc_join_partial_getclk in Eclk; try assumption.
  rewrite (proj1 (tr_getnode_in_iff_neg _ _) H_sub_notin_pfi) in Eclk.
  read_clock' witheqn Eclk. clear Eclk.
  array_unfocus witheqn Etmp.

  forward_call.
  1: now rewrite (tr_rootinfo_id_inj Eparjoin_info).
  (* retract *)
  (* write tr_getnode (tr_rootid sub) (tc_join_partial tc pf) here to align with the code *)
  pose (vret:=match tr_getnode (tr_rootid sub) (tc_join_partial tc pfi) with None => true | _ => false end).
  replace (node_is_null_as_bool (tc_join_partial tc pfi) (tr_rootid sub)) with vret.
  2:{
    subst vret. unfold node_is_null_as_bool.
    match goal with |- _ = (?a || _)%bool => enough (a = false) as -> by reflexivity end.
    unfold tc_join_partial. 
    now destruct (tc_detach_nodes (tr_flatten pfi) tc) as ([ [] ] & qq), (tc_attach_nodes qq pfi) as [ [] ] in |- *.
  }

  (* before going forward, prepare for the node to be detached and change the representation format *)
  pose proof (tc_join_partial_iterative_trans Hnodup Hrootid' Hnodup_pf Hprefix_sub Hnotnil_l) as Ejoin.
  rewrite <- Epfi in Ejoin.
  destruct (tc_detach_nodes (sub :: nil) (tc_join_partial tc pfi)) as (pivot, forest) eqn:E.
  pose (subi:=hd (Node (mkInfo (tr_rootid sub) 0%nat 0%nat) nil) forest).
  replace (option.from_option _ _ _) with (tr_rootchn subi) in Ejoin
    by (subst subi; destruct forest; auto).
  destruct Ejoin as (H_colocate & Ejoin).
  pose proof (tr_locate_parent Hprefix_sub ltac:(assumption)) as (tc_par & Etc_par & Hch_par).
  rewrite Etc_par in H_colocate.
  simpl in H_colocate.
  pose proof H_colocate as H_prepend_ok%isSome_by_fmap.

  sep_apply (tc_array2rep_and_bag plclk plnode lclk lnode dim (tc_join_partial tc pfi)).
  Intros.
  freeze (map Z.of_nat (seq 3%nat 5%nat)) Fr.

  (* lightweight postcondition declaration *)
  (* proving forest at the same time may be convenient *)
  match goal with |- context[PROPx _ (LOCALx ?b (SEPx ?c))] =>
    match c with (?preserved :: _) => 
    forward_if (EX z1 z2 z3 : Z, PROPx 
      ((tr_rootid subi = tr_rootid sub) :: nil) (* TODO well ... this might be derived from the pure reasoning? *)
      (LOCALx b (SEPx [preserved; 
      tc_subroot_rep dim plnode plclk subi z1 z2 z3;
      tc_rep_noroot dim plnode plclk subi; 
      tc_rep dim plnode plclk pivot; 
      (* dealing with bag here should be better *)
      unused_bag_rep dim plnode plclk (tr_flatten (tc_join_partial tc (post_iter_visited_prefix pf l))); 
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tr_rootid (tc_join_partial tc pfi)))), 
          (plclk, (plnode, (plstk, Vint (Int.repr (Zlength lstk_pre - 1 - 1))))))) p])))%assert end end.
  {
    (* (tr_rootid sub) exists in tc *)
    subst vret.
    destruct (tr_getnode (tr_rootid sub) (tc_join_partial tc pfi)) as [ res | ] eqn:Eres.
    2:{ 
      match goal with HH : context[typed_true] |- _ => rename HH into Htmp end.
      unfold eval_unop in Htmp. simpl in Htmp. now apply typed_true_tint_Vint in Htmp.
    }
    subst subi.
    apply trs_find_has_id in Eres. destruct Eres as ((l' & Eres)%subtr_subtr_witness & Eid).
    destruct (list_ifnil_destruct l') as [ -> | Hnotnil_l' ].
    1:{
      injection Eres as <-. rewrite (tr_rootinfo_id_inj (tc_join_partial_rootinfo_same tc pfi)) in Eid.
      (* use the sound property of pf here *)
      apply subtr_witness_subtr, (in_map tr_rootid) in Hprefix_sub.
      rewrite <- Eid, Epf in Hprefix_sub. 
      eapply tr_getnode_in_iff, tc_get_updated_nodes_join_sound in Hprefix_sub; try assumption.
      replace (tc_getclk (tr_rootid tc) tc) with (tc_rootclk tc) in Hprefix_sub.
      2: unfold tc_getclk; now rewrite tr_getnode_self.
      lia.
    }
    (* use detach single and transform into remove node *)
    pose proof (tc_detach_nodes_single Eres Hnodup_parjoin Hnotnil_l') as Htmp.
    erewrite -> tc_detach_nodes_tcs_congr with (tcs2:=(sub :: nil)) in Htmp.
    2: intros; simpl; rewrite Eid; auto.
    rewrite Htmp in E. apply pair_equal_split in E. destruct E as (<- & <-).

    forward_call (dim, Vint (Int.repr (Z.of_nat (tr_rootid (tc_join_partial tc pfi)))), plclk, plnode, plstk, 
      Vint (Int.repr (Zlength lstk_pre - 1 - 1)), p, tc_join_partial tc pfi, l', res).
    1:{ entailer!. simpl. now rewrite Eid. }
    Intros vret. destruct vret as ((z1, z2), z3). Exists z1 z2 z3.
    simpl hd in Ejoin |- *.
    entailer!.
    entailer!. (* ? *)
    (* change bag *)
    (* TODO put this to pure part? *)
    erewrite -> unused_bag_rep_perm. 
    1: apply derives_refl.
    epose proof (tc_detach_nodes_dom_partition _ _) as Hperm%Permutation_rootinfo2rootid.
    rewrite Htmp in Hperm. simpl in Hperm. rewrite Hperm, <- Ejoin, map_app, app_nil_r.
    etransitivity.
    2: apply Permutation_rootinfo2rootid; etransitivity; [ | symmetry; apply tr_prepend_nodes_dom_addition; try assumption ].
    2: rewrite <- map_app; reflexivity.
    simpl. rewrite app_nil_r, ! map_app, (tree_recons res). simpl. 
    fold (tr_rootid res). rewrite Eid. reflexivity.
  }
  {
    subst vret.
    destruct (tr_getnode (tr_rootid sub) (tc_join_partial tc pfi)) as [ res | ] eqn:Eres.
    1:{ 
      match goal with HH : context[typed_false] |- _ => rename HH into Htmp end.
      unfold eval_unop in Htmp. simpl in Htmp. now apply typed_false_tint_Vint in Htmp.
    }
    pose proof Eres as Eres'%trs_find_in_iff_neg.
    (* use intact *)
    rewrite tc_detach_nodes_intact' in E.
    2: simpl; intros ?? [ <- | [] ]; auto.
    apply pair_equal_split in E. destruct E as (<- & <-).
    (* get one from the bag *)
    rewrite -> unused_bag_rep_alloc with (tc:=subi); auto.
    simpl hd in (value of subi).
    subst subi. forward. 
    do 3 Exists default_nodefield.
    unfold tc_subroot_rep, clock_rep, node_rep, default_clockstruct, default_nodestruct.
    entailer!.
    1: simpl; lia. (* ... *)
    simpl. normalize.
    (* change bag *)
    (* TODO put this to pure part? *)
    simpl in Ejoin.
    erewrite -> unused_bag_rep_perm. 
    1: apply derives_refl.
    rewrite <- Ejoin. simpl.
    etransitivity.
    2: apply Permutation_rootinfo2rootid; etransitivity; [ | symmetry; apply tr_prepend_nodes_dom_addition; try assumption ].
    2: rewrite <- map_app; reflexivity.
    simpl. rewrite map_app. simpl.
    fold (tr_rootid sub). 
    list.solve_Permutation.
  }

  Intros z1 z2 z3.
  match goal with HH : tr_rootid subi = tr_rootid sub |- _ => rename HH into Eid end.

  (* update clk and aclk *)
  thaw Fr. rewrite -> ! Nat2Z.id. deadvars. clear vret.
  unfold tc_subroot_rep, clock_rep, clock_payload. rewrite -> ! Eid. Intros.

  array_focus (Z.of_nat (tr_rootid sub)) plclk' witheqn Etmp.
  rewrite -> Etmp.
  read_clock witheqn Es_sub_clk.
  forward.
  read_clock witheqn Es_sub_clk.
  forward.
  array_unfocus witheqn Etmp.
  deadvars.
  forward. forward.
  rewrite_sem_add_ptr_int.
  deadvars.

  (* read par *)
  pose proof (is_tc_nodearray_proj_onlypar_derived _ _ (proj2 Hprojn1')) as Hop_d.
  pose proof (is_tc_nodearray_proj_onlypar_prefix_preserve _ _ _ Hprefix Hop_d) as Hop_prefix.
  pose proof (is_tc_nodearray_proj_onlypar_read_parent lnode' _ Hop_prefix _ Hnotnil_l _ Hprefix_sub) as Hreadpar.
  rewrite Etc_par in Hreadpar.
  simpl in Hreadpar.

  (* real reading *)
  array_focus (Z.of_nat (tr_rootid sub)) plnode' witheqn Etmp.
  rewrite Etmp.
  (* huge! *)
  destruct (Znth (Z.of_nat (tr_rootid sub)) lnode') as (zz1, (zz2, (zz3, zz4))) eqn:Es.
  simpl in zz1, zz2, zz3, zz4, Es, Hreadpar.
  injection Hreadpar as <-.
  forward.
  array_unfocus witheqn Etmp. clear Es.
  deadvars.

  (* go push child; but we need to use the real par on pivot *)
  destruct (tr_locate _ _) as [ tc_par_real | ] eqn:Etc_par_real in H_colocate; try discriminate.
  simpl in H_colocate. injection H_colocate as H_colocate.
  freeze (0 :: 1 :: 2 :: 3 :: 4 :: 9 :: nil) Fr.
  forward_call (dim, Vint (Int.repr (Z.of_nat (tr_rootid (tc_join_partial tc pfi)))), plclk, plnode, plstk, Vint (Int.repr (Zlength lstk_pre - 1 - 1)), p, 
    pivot, tc_par_real, Node (tr_rootinfo sub) (tr_rootchn subi), (repeat 0%nat (length l)), z1, z2, z3).
  1:{ entailer!. simpl. now rewrite H_colocate. }
  1:{
    unfold tc_subroot_rep, clock_rep, clock_payload.
    simpl.
    fold (tr_rootid sub). fold (tc_rootclk sub). fold (tc_rootaclk sub).
    rewrite (tree_recons subi).
    simpl. unfold tc_headch_Z. simpl. 
    setoid_rewrite Eid. 
    change (info_tid (tr_rootinfo sub)) with (tr_rootid sub).
    entailer!.
  }
  1:{
    eapply subtr_witness_subtr, (in_map tr_rootid), prefixtr_flatten_id_incl, in_map_iff in Etc_par.
    2: apply Hprefix.
    destruct Etc_par as (tc_par_real' & Eid' & Htmp).
    eapply Foralltr_subtr in Htmp. 2: apply Htid'.
    simpl in Htmp. congruence.
  }
  (* cbn delta [tr_rootinfo tr_rootchn] beta iota.
  rewrite -> Efinal2. *)
  thaw Fr.
  cbv delta [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] beta iota.
  deadvars.
  rewrite Ejoin.

  (* trace back to the original tree *)
  pose proof (tc_get_updated_nodes_join_trace ltac:(subst pf; apply subtr_witness_subtr in Hprefix_sub; exact Hprefix_sub)) 
    as (sub' & Hsub' & Esub).
  pose proof (prefixtr_rootinfo_same (tc_get_updated_nodes_join_is_prefix tc sub')) as Erooinfo_sub'.
  rewrite <- Esub in Erooinfo_sub'.

  (* congruence ... *)
  pose proof (tc_get_updated_nodes_join_aux_tc_congr_partialjoin Hnodup Hnodup') as Egj.
  rewrite <- Epf in Egj.
  specialize (Egj _ _ Hprefix_sub ltac:(assumption) _ Hsub' Esub (tc_getclk (tr_rootid sub) tc)).
  
  (* length ... *)
  match type of Egj with map ?ff ?al = map ?ff ?bl => assert (length al = length bl) as Elen
    by (rewrite <- ! map_length with (f:=ff), -> Egj; reflexivity) end.
  apply f_equal with (f:=map info_id) in Egj.
  rewrite -> ! map_map in Egj.
  do 2 rewrite -> map_ext with (f:=(fun x : treeclock => info_id (tr_rootinfo x))) (g:=tr_rootid) in Egj; auto.

  (* fold *)
  unfold tc_rep. sep_apply tc_rep_and_bag2array.
  1:{
    apply tc_join_partial_id_nodup; try assumption.
    - eapply id_nodup_prefix_preserve. apply post_iter_visited_is_prefix. assumption.
    - eapply Hnotin_prefix. apply post_iter_visited_is_prefix. assumption. 
  }
  Intros lnode1 lclk1.
  clear dependent lnode.
  clear dependent lclk.

  (* more preparation *)
  remember (removelast lstk_pre) as lstk_pre' eqn:Elstk_pre'.
  rewrite Elstk_pre, removelast_last in Elstk_pre'.
  assert (traversal_invariant pf
    (lstk_pre' ++ (map tr_rootid (tc_get_updated_nodes_join_aux (tc_join_partial tc (post_iter_visited_prefix pf l)) 
      (tc_getclk (tr_rootid sub) tc) (tr_rootchn sub'))))
    (post_iter_visited_prefix pf l)) as Htts_goal.
  {
    subst lstk_pre' sub.
    rewrite Egj, (tr_rootinfo_id_inj Erooinfo_sub').
    eapply eq_ind_r with (y:=map tr_rootid (tc_get_updated_nodes_join_aux _ _ _)).
    1: rewrite <- map_app; apply traversal_invariant_trans, Hprefix_sub.
    destruct sub'.
    rewrite tc_get_updated_nodes_join_eta.
    reflexivity.
  }

  pose proof (is_tc_nodearray_proj_onlyheadch_derived_full _ _ Hprojn1') as Hreadheadch.
  eapply Foralltr_subtr in Hreadheadch. 2: apply Hsub'.
  hnf in Hreadheadch.
  match goal with |- context[data_at Tsh (tarray tint dim) ?lstkstk plstk] =>
    forward_call (dim, tc_join_partial tc (post_iter_visited_prefix pf l), plclk, plnode, plstk, (length lstk_pre - 1)%nat, p, 
      Vint (Int.repr (Z.of_nat (tr_rootid tc'))), plclk', plnode', plstk', Vint (Int.repr (-1)), p', 
      tc_getclk (tr_rootid sub) tc, tr_rootid sub', tr_rootchn sub', lclk1, lstkstk, lclk', lnode') end.
  1:{ 
    entailer!. simpl. now rewrite (tr_rootinfo_id_inj Erooinfo_sub').
  }
  1:{
    unfold treeclock_payload, tr_rootid.
    rewrite ! tc_join_partial_rootinfo_same.
    rewrite Zlength_correct in Hlen_lstk_pre_ge0 |- *.
    replace (Z.of_nat (length lstk_pre) - 1 - 1) with (Z.of_nat (length lstk_pre - 1) - 1) by lia.
    entailer!.
  }
  1:{
    split.
    1: rewrite <- (tr_rootinfo_id_inj Erooinfo_sub'); assumption.
    split.
    1:{
      match goal with HH : Foralltr _ (tc_join_partial tc (post_iter_visited_prefix _ _)) |- _ => revert HH; apply Foralltr_impl end.
      intros; tauto.
    }
    split.
    1:{
      eapply Foralltr_subtr in Hsub'. 2: rewrite -> Foralltr_idempotent; apply Hcb_tc'.
      apply Foralltr_chn_selves.
      assumption.
    }
    split.
    1: split; [ lia | now apply tc_getclk_in_int_range ].
    split.
    1:{ 
      subst lstk_pre. rewrite -> Zlength_app, Zlength_map in Hlensum |- *.
      rewrite Zlength_map, Zlength_cons. rewrite <- Hlensum. clear. list_solve.
    }
    split.
    1:{
      eapply Foralltr_subtr in Hsub'. 2: rewrite -> Foralltr_idempotent; apply Hprojc1'.
      apply Foralltr_chn.
      assumption.
    }
    split.
    1:{
      eapply Foralltr_subtr in Hsub'. 2: apply Hprojn1'. assumption.
    } 
    1:{
      (* stack property *)
      (* TODO move to pure part? *)
      replace (length lstk_pre - 1)%nat with (length lstk_pre')%nat by (subst; rewrite app_length; simpl; lia).
      match goal with |- context[(_ + length ?ll)%nat] => replace (length ll) with (length (map tr_rootid ll)) end.
      2: now rewrite map_length.
      subst lstk_pre'.
      rewrite <- app_length.
      inversion Htts_goal.
      1: simpl; lia.
      match goal with HH : ?ll = _ |- context[length ?ll] => rewrite HH end.
      rewrite map_length, app_length.
      match goal with |- context[length (snd (_ ?tcc ?ll))] => 
        pose proof (tr_trav_waitlist_length_lt_tr_size tcc ll) as Htmp end.
      simpl.
      pose proof (prefixtr_size_le Hprefix).
      pose proof (tr_size_bounded_by_dim tc' dim Hdim Htid' (tid_nodup Hshape')).
      unfold tr_size in *.
      lia.
    }
  }

  (* final! *)
  (* first, deal with length *)
  (* TODO why? *)
  pose proof Elstk_pre as Elstk_pre_len.
  apply f_equal with (f:=@Zlength nat) in Elstk_pre_len.
  rewrite -> Zlength_app in Elstk_pre_len.
  rewrite <- Zlength_map with (f:=(fun x : nat => Vint (Int.repr (Z.of_nat x)))) (l:=map _ _) in Elstk_pre_len.
  replace (Zlength (_ :: nil)) with 1 in Elstk_pre_len by list_solve.
  match type of Elstk_pre_len with _ = Zlength ?zb + 1 => 
    assert ((length lstk_pre - 1)%nat = length zb) as Elstk_pre_len' end.
  {
    rewrite <- Nat2Z.inj_iff, <- Zlength_correct.
    rewrite Zlength_correct in Hlen_lstk_pre_ge0.
    replace (Z.of_nat (_ - 1)%nat) with (Zlength lstk_pre - 1) by (rewrite Zlength_correct; lia).
    lia.
  }
  rewrite list.take_app_alt; try assumption.
  rewrite list.drop_add_app. 2: rewrite Elstk_pre_len'; reflexivity.

  rewrite -> app_assoc, <- ! map_app.
  match goal with |- context[data_at Tsh (tarray tint dim) (map _ ?lpre ++ ?lsuf) plstk] =>
    Exists lpre lsuf end.
  Exists (post_iter_visited_prefix pf l) lclk1 lnode1.
  rewrite ! map_length in Elstk_pre_len'.
  rewrite 1 Elstk_pre_len'.
  rewrite <- app_length, <- Zlength_correct, -> Zlength_map.
  entailer!.
  {
    split.
    - rewrite map_app, Egj. 
      eapply eq_ind_r with (y:=map tr_rootid (tc_get_updated_nodes_join_aux _ _ _)).
      1: rewrite <- map_app; apply traversal_invariant_trans, Hprefix_sub.
      destruct sub'.
      rewrite tc_get_updated_nodes_join_eta.
      reflexivity.
    - rewrite map_app, in_app_iff.
      rewrite in_app_iff in Hnotin_tc'.
      intros [ Hin | Hin ]. 1: apply Hnotin_tc'; tauto.
      (* TODO cumbersome ... *)
      rewrite Egj, (tr_rootinfo_id_inj Erooinfo_sub') in Hin.
      pose proof (tc_get_updated_nodes_join_aux_result_submap tc (tc_getclk (tr_rootid sub') tc) (tr_rootchn sub'))
        as (chn' & Hsl & EE).
      erewrite EE, prefixtr_rootid_same_map in Hin.
      2: apply Forall2_mapself_l, list.Forall_true, tc_get_updated_nodes_join_is_prefix.
      apply (sublist_map tr_rootid) in Hsl.
      apply (sublist_In Hsl) in Hin. 
      apply id_nodup_rootid_neq, Foralltr_Forall_chn_comm in Hnodup'.
      eapply Foralltr_subtr in Hsub'. 2: apply Hnodup'.
      pose proof Hin as (ch' & Eid'%eq_sym & Hin')%in_map_iff.
      revert ch' Hin' Eid'.
      now rewrite <- Forall_forall.
  }

(* require around 45 seconds to check this Qed *)
Qed.

End Main_Proof.
