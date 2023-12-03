Require Import VST.floyd.proofauto.
Require Import arboreta.clocks.treeclock.
From arboreta.vst Require Import treeclock_clight util_vst array_support util_treeclock.
From arboreta.utils Require Import libtac.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* From stdpp Require list. *)

(*
node id: all use Z when possible
TODO change tid to be Z, and use Znth? this may be troublesome since id should >= 0

*)

Definition t_struct_clock := Tstruct _Clock noattr.
Definition t_struct_node := Tstruct _Node noattr.
Definition t_struct_treeclock := Tstruct _TreeClock noattr.

(* TODO this is hard to use since it needs to be unfolded every time *)
Definition is_pos_tint z : Prop := 0 <= z <= Int.max_signed.
(* planned not to use *)
(* Definition is_pos_tshort z : Prop := 0 <= z <= short_max_signed. *)

Definition clock_payload (clk aclk : Z) : reptype t_struct_clock :=
  (Vint (Int.repr clk), Vint (Int.repr aclk)).

Definition clock_rep (clk aclk : Z) (p : val) : mpred :=
  (* !! (is_pos_tint clk) && !! (is_pos_tint aclk) && *)
  !! (0 <= clk <= Int.max_signed) && !! (0 <= aclk <= Int.max_signed) &&
  data_at Tsh t_struct_clock (clock_payload clk aclk) p.

Definition node_payload (next prev par headch : Z) : reptype t_struct_node :=
  (Vint (Int.repr next), 
    (Vint (Int.repr prev), 
      (Vint (Int.repr par), Vint (Int.repr headch)))).

Definition node_rep (next prev par headch : Z) (p : val) : mpred :=
  (* !! (is_pos_tshort next) && !! (is_pos_tshort prev) &&
  !! (is_pos_tshort par) && !! (is_pos_tshort headch) && *)
  (* !! (is_pos_tint next) && !! (is_pos_tint prev) &&
  !! (is_pos_tint par) && !! (is_pos_tint headch) && *)
  data_at Tsh t_struct_node (node_payload next prev par headch) p.

(* from tree to its array presentation *)
(* Fixpoint tc_clockarray_proj (tc : treeclock)  *)

(* descriptive? *)

(* using Z as the thread type is difficult, since we cannot guarantee the positiveness ... *)
(*
#[export] Instance Z_EqDec : EqDec Z.
Proof. constructor. apply Z.eq_dec. Qed.
*)

(* here, there is a choice between nth_error and Znth. 
  for now, the choice is to make more use of nth_error, since there is no counterpart 
  like Znth_error;
  but for the array part, we will switch to Znth since Znth is more commonly used there

  for length, we try consistently using Zlength
*)

Definition tc_rootclk_proj (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  nth_error l (tc_roottid tc) = Some (clock_payload (Z.of_nat (tc_rootclk tc)) (Z.of_nat (tc_rootaclk tc))).

Definition is_tc_clockarray_proj (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  Eval unfold tc_rootclk_proj in Foralltc (tc_rootclk_proj l) tc.

(*
Definition is_tc_clockarray_proj (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  Foralltc (fun t => nth_error l (tc_roottid t) = 
    Some (clock_payload (Z.of_nat (tc_rootclk t)) (Z.of_nat (tc_rootaclk t)))) tc.
*)

Definition default_clockstruct := clock_payload 0%Z 0%Z.

Definition clockarray_emptypart (l : list (reptype t_struct_clock)) (tcs : list treeclock) : Prop :=
  forall n np, find (has_same_tid n) tcs = None -> nth_error l n = Some np -> 
    np = default_clockstruct.

(* TODO could also be per-field description so that there will be only one branch *)

(* typically requires that default_nodefield <= 0 *)
Definition default_nodefield := (-1)%Z.

Definition default_nodestruct := node_payload default_nodefield default_nodefield default_nodefield default_nodefield.

Definition tcs_head_Z_default (dft : Z) (tcs : list (@treeclock nat)) : Z := 
  match tcs with nil => dft | ch :: _ => Z.of_nat (tc_roottid ch) end.

Definition tcs_head_Z := tcs_head_Z_default default_nodefield.

Definition tc_headch_Z (tc : @treeclock nat) : Z := tcs_head_Z (tc_rootchn tc).

Global Arguments tcs_head_Z_default dft tcs : simpl nomatch.
(* Global Arguments tcs_head_Z tcs : simpl nomatch. *)
Global Arguments tcs_head_Z _ /.
Global Arguments tc_headch_Z !tc.

Fact tcs_head_Z_default_rev_last dft tcs :
  tcs_head_Z_default dft (rev tcs) = 
  match list.last tcs with Some ch => Z.of_nat (tc_roottid ch) | None => dft end.
Proof.
  destruct (list.last tcs) as [ ch | ] eqn:E.
  - apply list.last_Some in E. destruct E as (l' & ->).
    rewrite -> rev_app_distr. now simpl.
  - apply list.last_None in E. now subst.
Qed.

Fact tcs_head_Z_default_rev_last' dft ch tcs :
  tcs_head_Z_default dft (rev (tcs ++ (ch :: nil))) = Z.of_nat (tc_roottid ch).
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
    nth_error l (tc_roottid ch) = 
    Some (node_payload (match chn' with nil => default_nodefield | ch' :: _ => (Z.of_nat (tc_roottid ch')) end) 
      prev (Z.of_nat par) (tc_headch_Z ch)) /\
    aux (Z.of_nat (tc_roottid ch)) chn'
  end.

Definition is_tc_nodearray_proj_aux (l : list (reptype t_struct_node)) (tc : @treeclock nat): Prop :=
  is_tc_nodearray_proj_chnaux (tc_roottid tc) l default_nodefield (tc_rootchn tc).

Global Arguments is_tc_nodearray_proj_aux _ _/.

Definition is_tc_nodearray_proj_root (l : list (reptype t_struct_node)) (tc : @treeclock nat): Prop :=
  nth_error l (tc_roottid tc) = 
  Some (node_payload default_nodefield default_nodefield default_nodefield (tc_headch_Z tc)).

Definition is_tc_nodearray_proj (l : list (reptype t_struct_node)) (tc : @treeclock nat) : Prop :=
  Foralltc (is_tc_nodearray_proj_aux l) tc.

(* for the whole tree *)
Definition is_tc_nodearray_proj_full (l : list (reptype t_struct_node)) (tc : @treeclock nat) : Prop :=
  is_tc_nodearray_proj_root l tc /\ is_tc_nodearray_proj l tc.

Definition nodearray_emptypart (l : list (reptype t_struct_node)) (tcs : list (@treeclock nat)) : Prop :=
  forall n np, find (has_same_tid n) tcs = None -> nth_error l n = Some np -> np = default_nodestruct.

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
    !! (0 <= Z.of_nat (tc_roottid ch) < dim) &&
    (* by design, this should be bundled with clock_rep *)
    (*     
    !! (0 <= Z.of_nat (tc_rootclk ch) <= Int.max_signed) &&
    !! (0 <= Z.of_nat (tc_rootaclk ch) <= Int.max_signed) && 
    *)
    (clock_rep (Z.of_nat (tc_rootclk ch)) (Z.of_nat (tc_rootaclk ch)) 
      (offset_val (sizeof t_struct_clock * Z.of_nat (tc_roottid ch)) plclk) *
    node_rep 
      (tcs_head_Z_default lst chn')
      (* (match chn' with nil => lst | ch' :: _ => (Z.of_nat (tc_roottid ch')) end)  *)
      prev (Z.of_nat par) (tc_headch_Z ch)
      (offset_val (sizeof t_struct_node * Z.of_nat (tc_roottid ch)) plnode) *
    aux (Z.of_nat (tc_roottid ch)) chn')%logic
  end.

Fixpoint tc_rep_noroot (dim : Z) (plnode plclk : val) (tc : @treeclock nat) : mpred :=
  let 'Node ni chn := tc in
  (tc_chn_rep dim plnode plclk (info_tid ni) default_nodefield default_nodefield chn *
  (* TODO is fold proper here? or use allp? *)
  fold_right_sepcon (map (tc_rep_noroot dim plnode plclk) chn))%logic.

Definition tc_root_rep (dim : Z) (plnode plclk : val) (tc : @treeclock nat) : mpred :=
  (* may be redundant? *)
    (* TODO 0 <= may be redundant? *)
  !! (0 <= Z.of_nat (tc_roottid tc) < dim) &&
  (clock_rep (Z.of_nat (tc_rootclk tc)) (Z.of_nat (tc_rootaclk tc)) 
    (offset_val (sizeof t_struct_clock * Z.of_nat (tc_roottid tc)) plclk) *
  node_rep default_nodefield default_nodefield default_nodefield (tc_headch_Z tc)
    (offset_val (sizeof t_struct_node * Z.of_nat (tc_roottid tc)) plnode))%logic.

Definition tc_subroot_rep (dim : Z) (plnode plclk : val) (tc : @treeclock nat) z1 z2 z3 : mpred :=
  (* may be redundant? *)
    (* TODO 0 <= may be redundant? *)
  !! (0 <= Z.of_nat (tc_roottid tc) < dim) &&
  (clock_rep (Z.of_nat (tc_rootclk tc)) (Z.of_nat (tc_rootaclk tc)) 
    (offset_val (sizeof t_struct_clock * Z.of_nat (tc_roottid tc)) plclk) *
  node_rep z1 z2 z3 (tc_headch_Z tc)
    (offset_val (sizeof t_struct_node * Z.of_nat (tc_roottid tc)) plnode))%logic.

Definition tc_rep (dim : Z) (plnode plclk : val) (tc : @treeclock nat) : mpred :=
  (tc_root_rep dim plnode plclk tc * tc_rep_noroot dim plnode plclk tc)%logic.

(* TODO the representation of unused_bag_rep is debatable *)

(* Definition unused_bag_rep (dim : Z) (plnode plclk : val) (l : list nat) : mpred := *)
Definition unused_bag_rep (dim : Z) (plnode plclk : val) (tcs : list (@treeclock nat)) : mpred :=
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock default_clockstruct (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node default_nodestruct (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic
    (* (filter (fun i => negb (ssrbool.isSome (find (has_same_tid (Z.to_nat i)) tcs))) (upto (Z.to_nat dim)))). *)
    (filter (fun t => negb (ssrbool.isSome (find (has_same_tid t) tcs))) 
      (map Z.to_nat (upto (Z.to_nat dim))))).
    (* (ListSet.set_diff Z.eq_dec (upto (Z.to_nat dim)) (map Z.of_nat l))). *)

(* sometimes the treeclock corresponds to an empty tree, but do not consider it for now *)

(* factor the dim out; it should not change during the operation? *)
(* seems like top should be consistently -1 *)
Definition treeclock_rep (dim : Z) (tc : @treeclock nat) (plclk plnode : val) 
  (plstk : val) p : mpred :=
  (* EX dim : Z,  *)
  (* EX lclk_ptrs : list val,  *)
  (* EX lnode_ptrs : list val,  *)
  (* TODO should this be raw (reptype t_struct_clock) or the result of some (map list)? *)
  EX lclk : list (reptype t_struct_clock), 
  EX lnode : list (reptype t_struct_node), 

  EX lstk : list val, 

  (* TODO the clk and aclk must become bounded somewhere.
      if they are bounded with a Foralltc, then we may simply bound tid as well 
        so that we do not need the tid_bounded lemmas and nth_error 
    but for now, we only bound clk and aclk to avoid premature optimization
  *)
  !! (Foralltc (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) &&
  (* this is necessary in the current setting, since the root may not appear in the node array *)
  !! (Z.of_nat (tc_roottid tc) < dim) &&
  (* !! (Zlength lclk_ptrs = dim) &&  *)
  !! (Zlength lclk = dim) &&
  (* !! (Zlength lnode_ptrs = dim) &&  *)
  !! (Zlength lnode = dim) &&
  !! (Zlength lstk = dim) &&
  !! (is_tc_clockarray_proj lclk tc) && !! (clockarray_emptypart lclk (tc_flatten tc)) &&
  !! (is_tc_nodearray_proj_full lnode tc) && !! (nodearray_emptypart lnode (tc_flatten tc)) &&
  (* TODO this should be subsumed? *)
  (* !! (Foralltc (fun t => Z.of_nat (tc_roottid t) < dim) tc) && *)
  data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tc_roottid tc)) 
    plclk plnode plstk (-1)) p * 
  data_at Tsh (tarray t_struct_clock dim) lclk plclk *
  data_at Tsh (tarray t_struct_node dim) lnode plnode *
  (* data_at Tsh (tarray tshort dim) lstk plstk. *)
  data_at Tsh (tarray tint dim) lstk plstk.

(* simple bounded properties *)
(* TODO should I use Z.< instead? *)

Fact is_tc_nodearray_proj_chnaux_tid_bounded lnode par prev chn (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn) :
  Forall (fun tc' => Z.of_nat (tc_roottid tc') < Zlength lnode) chn.
Proof.
  revert lnode prev Hproj.
  induction chn as [ | ch chn IH ]; intros; constructor; simpl in Hproj.
  - now apply proj1, nth_error_some_inrange_Z in Hproj.
  - eapply IH. apply (proj2 Hproj).
Qed.

Fact is_tc_nodearray_proj_tid_bounded lnode tc (Hproj : is_tc_nodearray_proj lnode tc)
  (HH : Z.of_nat (tc_roottid tc) < Zlength lnode) :
  Foralltc (fun tc' => Z.of_nat (tc_roottid tc') < Zlength lnode) tc.
Proof.
  destruct tc as [(u, clk, aclk) chn].
  simpl in HH.
  rewrite Foralltc_cons_iff'. split. 1: simpl; auto.
  rewrite <- Foralltc_Forall_chn_comm.
  eapply Foralltc_impl. 2: apply Hproj.
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
  Forall (fun tc' => node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tc_roottid tc')) lnode)) chn.
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
    apply IH with (prev:=(Z.of_nat (tc_roottid ch))); auto; unfold default_nodefield; try lia; try tauto.
Qed. 

Fact is_tc_nodearray_proj_headch_inrange lnode tc (Hproj : is_tc_nodearray_proj lnode tc) :
  default_nodefield <= tc_headch_Z tc < Zlength lnode.
Proof.
  pose proof (Zlength_nonneg lnode).
  destruct tc as [ ? [ | ] ]; cbn; unfold default_nodefield; simpl; try lia.
  apply Foralltc_self in Hproj. 
  apply is_tc_nodearray_proj_chnaux_tid_bounded in Hproj; auto.
  inversion_clear Hproj. lia.
Qed.

(* leave out the root is more convenient for this proof *)
Fact is_tc_nodearray_proj_regular_chn lnode tc (Hproj : is_tc_nodearray_proj lnode tc)
  (Hu : Z.of_nat (tc_roottid tc) < (Zlength lnode)) :
  Forall (Foralltc (fun tc' => node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tc_roottid tc')) lnode))) (tc_rootchn tc).
Proof.
  revert lnode Hproj Hu.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in Hu.
  apply Foralltc_cons_iff in Hproj. destruct Hproj as (Hchn & Hproj). simpl in Hchn. 
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
  replace chn_ch with (tc_rootchn ch) by now rewrite Ech.
  apply IH; rewrite Ech; auto.
Qed.

Fact is_tc_nodearray_proj_regular lnode tc (Hproj : is_tc_nodearray_proj lnode tc)
  (* dim (Hlen : Zlength lnode = dim)  *)
  (Hu : Z.of_nat (tc_roottid tc) < (Zlength lnode))
  (HH : node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tc_roottid tc)) lnode)) :
  Foralltc (fun tc' => node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tc_roottid tc')) lnode)) tc.
Proof.
  destruct tc as [(u, ?, ?) chn] eqn:Etc. simpl in *.
  constructor; simpl; auto.
  replace chn with (tc_rootchn tc) by now rewrite Etc.
  apply is_tc_nodearray_proj_regular_chn; rewrite Etc; auto.
Qed.

Fact is_tc_nodearray_proj_full_regular_wk lnode tc (Hproj : is_tc_nodearray_proj_full lnode tc) :
  (* dim (Hlen : Zlength lnode = dim)  *)
  (* (Hu : Z.of_nat (tc_roottid tc) < (Zlength lnode))  *)
  Foralltc (fun tc' => node_struct_regular_wk (Zlength lnode) (Znth (Z.of_nat (tc_roottid tc')) lnode)) tc.
Proof.
  (* eapply Foralltc_impl. 1: intros ?; apply node_struct_regular_weaken. *)
  destruct Hproj as (Hroot & Hproj). hnf in Hroot.
  destruct tc as [(u, ?, ?) chn] eqn:Etc. simpl in *.
  constructor.
  - simpl. apply nth_error_Znth_result in Hroot.
    hnf. do 4 eexists. rewrite -> Hroot. split; [ reflexivity | ].
    apply is_tc_nodearray_proj_headch_inrange in Hproj.
    pose proof (Zlength_nonneg lnode).
    unfold default_nodefield. intuition lia.
  - eapply Forall_impl.
    + intros ? HH; eapply Foralltc_impl.
      intros ?; apply node_struct_regular_weaken.
      apply HH.
    + replace chn with (tc_rootchn tc) by now rewrite Etc.
      apply is_tc_nodearray_proj_regular_chn.
      * now subst tc.
      * rewrite Etc. simpl. now apply nth_error_some_inrange_Z in Hroot.
Qed.

Fact nodearray_proj_regular lnode tc (Hproj1 : is_tc_nodearray_proj_full lnode tc) 
  (Hproj2 : nodearray_emptypart lnode (tc_flatten tc)) :
  (* dim (Hlen : Zlength lnode = dim)  *)
  Forall (node_struct_regular_wk (Zlength lnode)) lnode.
Proof.
  (* revert lnode Hproj1 Hproj2.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros. *)
  apply Forall_Znth.
  intros n Hr. destruct (tc_getnode (Z.to_nat n) tc) as [ res | ] eqn:E.
  - apply is_tc_nodearray_proj_full_regular_wk in Hproj1.
    apply (tc_getnode_res_Foralltc Hproj1) in E.
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
  node_struct_get_headch (Znth (Z.of_nat (tc_roottid tc)) lnode) = 
    Vint (Int.repr (tc_headch_Z tc)).

Definition is_tc_nodearray_proj_onlypar_aux par lnode chn :=
  Forall (fun tc0 => node_struct_get_par (Znth (Z.of_nat (tc_roottid tc0)) lnode) = 
    Vint (Int.repr (Z.of_nat par))) chn.

Definition is_tc_nodearray_proj_onlypar lnode tc :=
  Foralltc (fun tc' => is_tc_nodearray_proj_onlypar_aux (tc_roottid tc') lnode (tc_rootchn tc')) tc.

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
  Foralltc (is_tc_nodearray_proj_onlyheadch lnode) tc.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  hnf in Hproj |- *.
  rewrite Foralltc_cons_iff in Hproj |- *.
  constructor; try assumption.
  simpl in Hproj.
  destruct Hproj as (Hq%is_tc_nodearray_proj_onlyheadch_chn_derived & Hproj).
  eapply Forall_impl_impl in Hproj.
  2: apply IH.
  now apply Forall_impl_impl with (P:=is_tc_nodearray_proj_onlyheadch lnode) in Hproj.
Qed.

Fact is_tc_nodearray_proj_onlyheadch_derived_full lnode tc
  (Hproj : is_tc_nodearray_proj_full lnode tc) :
  Foralltc (is_tc_nodearray_proj_onlyheadch lnode) tc.
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
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  hnf in Hproj |- *.
  rewrite Foralltc_cons_iff in Hproj |- *.
  simpl in Hproj |- *.
  constructor.
  - eapply is_tc_nodearray_proj_onlypar_aux_derived, (proj1 Hproj).
  - eapply Forall_impl_impl. 
    1: apply IH.
    apply (proj2 Hproj).
Qed.

Fact is_tc_nodearray_proj_onlypar_prefix_preserve lnode tc tc'
  (Hprefix : prefixtc tc tc')
  (Hproj : is_tc_nodearray_proj_onlypar lnode tc') : is_tc_nodearray_proj_onlypar lnode tc.
Proof.
  revert tc Hprefix Hproj.
  induction tc' as [ni' chn' IH] using treeclock_ind_2; intros.
  destruct tc as [ni chn].
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  subst ni.
  hnf in Hproj |- *.
  rewrite -> Foralltc_cons_iff in Hproj |- *.
  simpl in Hproj |- *.
  destruct Hproj as (Hself & Hproj).
  split.
  - hnf in Hself |- *.
    (* TODO tedious ad hoc reasoning *)
    pose proof (List.Forall_map tc_roottid
      (fun t => node_struct_get_par (Znth (Z.of_nat t) lnode) = 
        Vint (Int.repr (Z.of_nat (info_tid ni'))))) as Htmp.
    simpl in Htmp.
    rewrite <- Htmp in Hself |- *.
    (* FIXME: replace this with some Forall2_?? *)
    replace (map tc_roottid chn) with (map tc_roottid chn_sub).
    2:{
      clear -Hcorr.
      induction Hcorr; simpl; try reflexivity.
      f_equal; try assumption.
      symmetry.
      now apply tc_rootinfo_tid_inj, prefixtc_rootinfo_same.
    }
    apply sublist_map with (f:=tc_roottid) in Hsub.
    revert Hself.
    now apply sublist_Forall.
  - eapply sublist_Forall in Hproj, IH.
    2-3: apply Hsub.
    pose proof (Forall2_forall_exists_l _ _ _ Hcorr) as Hcorr_in.
    rewrite -> List.Forall_forall in IH, Hproj |- *.
    intros ch Hin.
    destruct (Hcorr_in _ Hin) as (ch' & Hin' & Hprefix).
    specialize (IH _ Hin' _ Hprefix).
    specialize (Hproj _ Hin').
    eapply IH; eauto.
Qed.

Fact is_tc_nodearray_proj_onlypar_read_parent lnode tc (Hproj : is_tc_nodearray_proj_onlypar lnode tc) :
  forall l (Hnotnil : l <> nil) sub (H : tc_locate tc l = Some sub), 
  base.fmap (fun tc0 => Vint (Int.repr (Z.of_nat (tc_roottid tc0)))) (tc_locate tc (removelast l)) = 
    Some (node_struct_get_par (Znth (Z.of_nat (tc_roottid sub)) lnode)).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  destruct l as [ | x l ]; try contradiction.
  simpl in H.
  destruct (nth_error chn x) as [ ch | ] eqn:Enth; try discriminate.
  apply exists_last in Hnotnil.
  destruct Hnotnil as (l' & x' & E).
  rewrite E, removelast_last.
  destruct l' as [ | y' l' ].
  - simpl. simpl in E. destruct l; try discriminate. injection E as <-.
    simpl in H. injection H as <-.
    eapply Foralltc_self, Forall_forall in Hproj.
    2: simpl; eapply nth_error_In, Enth.
    rewrite Hproj. reflexivity.
  - rewrite <- app_comm_cons in E. injection E as <-.
    subst l. simpl.
    rewrite Enth.
    apply nth_error_In in Enth.
    apply Foralltc_chn in Hproj.
    simpl in Hproj.
    rewrite -> Forall_forall in Hproj, IH.
    replace l' with (removelast (l' ++ (x' :: nil))) in |- * by now rewrite removelast_last.
    apply IH; try assumption.
    2: now destruct l'.
    now apply Hproj.
Qed.

Fact is_tc_clockarray_proj_nth lclk tc (Hproj : is_tc_clockarray_proj lclk tc) :
  Foralltc (fun tc' => (Znth (Z.of_nat (tc_roottid tc')) lclk) = 
    clock_payload (Z.of_nat (tc_rootclk tc')) (Z.of_nat (tc_rootaclk tc'))) tc.
Proof.
  eapply Foralltc_impl. 2: apply Hproj. 
  simpl. intros tc' H.
  apply List.nth_error_nth with (d:=default) in H.
  rewrite <- nth_Znth', -> H.
  reflexivity.
Qed.

Fact clockarray_proj_tc_getinfo lclk tc (Hproj1 : is_tc_clockarray_proj lclk tc) 
  (Hproj2 : clockarray_emptypart lclk (tc_flatten tc)) 
  i (Hi : 0 <= i < Zlength lclk) :
  (* Vint (Int.repr (Z.of_nat (tc_getclk (Z.to_nat i) tc))) = fst (Znth i lclk). *)
  Znth i lclk = (Vint (Int.repr (Z.of_nat (tc_getclk (Z.to_nat i) tc))), 
    Vint (Int.repr (Z.of_nat (match tc_getnode (Z.to_nat i) tc with Some res => tc_rootaclk res | None => 0%nat end)))).
Proof.
  unfold tc_getclk, tc_getnode. 
  destruct (find (has_same_tid (Z.to_nat i)) (tc_flatten tc)) as [ res | ] eqn:E.
  - eapply tc_getnode_res_Foralltc in E. 2: apply Hproj1.
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

Fact unused_bag_rep_perm dim plnode plclk tcs1 tcs2
  (Hperm : Permutation (map tc_roottid tcs1) (map tc_roottid tcs2)) :
  unused_bag_rep dim plnode plclk tcs1 = unused_bag_rep dim plnode plclk tcs2.
Proof.
  unfold unused_bag_rep.
  erewrite -> filter_ext. 1: reflexivity.
  (* TODO awkward isSome and is_true *)
  simpl. intros a. f_equal.
  pose proof (tcs_find_in_iff a tcs1) as H1.
  pose proof (tcs_find_in_iff a tcs2) as H2.
  erewrite -> Permutation_in_mutual in H1. 2: apply Hperm.
  rewrite -> H1 in H2.
  destruct (find (has_same_tid a) tcs1), (find (has_same_tid a) tcs2);
    unfold Datatypes.is_true in *; simpl in *; intuition.
Qed.

Fact unused_bag_rep_alloc dim plnode plclk tcs 
  tc (H : Z.of_nat (tc_roottid tc) < dim) (Hnotin : find (has_same_tid (tc_roottid tc)) tcs = None) :
  unused_bag_rep dim plnode plclk tcs = 
  (* (unused_bag_rep dim plnode plclk (tc :: tcs) * tc_root_rep dim plnode plclk tc)%logic. *)
  (unused_bag_rep dim plnode plclk (tc :: tcs) *
    data_at Tsh t_struct_clock default_clockstruct (offset_val (sizeof t_struct_clock * Z.of_nat (tc_roottid tc)) plclk) *
    data_at Tsh t_struct_node default_nodestruct (offset_val (sizeof t_struct_node * Z.of_nat (tc_roottid tc)) plnode))%logic.
Proof.
  unfold unused_bag_rep.
  simpl.
  pose proof (Permutation_upto_pick (tc_roottid tc) (Z.to_nat dim)) as Hperm.
  removehead Hperm. 2: lia.
  rewrite -> seq_upto in Hperm.
  erewrite -> fold_right_sepcon_permutation at 1.
  2: apply Permutation_map, Permutation_filter, Hperm.
  match goal with |- _ = (fold_right_sepcon ?ll * _ * _)%logic => 
    erewrite -> fold_right_sepcon_permutation with (al:=ll) end.
  2: apply Permutation_map, Permutation_filter, Hperm.
  simpl. rewrite Hnotin. simpl.
  unfold has_same_tid at 2. 
  destruct (eqdec (tc_roottid tc) (tc_roottid tc)); simpl; try contradiction.
  rewrite -> sepcon_comm at 1. 
  rewrite -> sepcon_assoc at 1.
  f_equal. f_equal. f_equal.
  apply filter_ext_in_iff. intros x. rewrite -> ! in_app_iff, -> ! in_seq.
  intros HH. unfold has_same_tid. destruct (eqdec (tc_roottid tc) x); try lia.
  now simpl.
Qed.

Lemma tc_chn_rep_segment plclk plnode dim par pre :
  forall lst prev ch suf, 
  tc_chn_rep dim plnode plclk par lst prev (pre ++ ch :: suf) =
  (tc_chn_rep dim plnode plclk par (Z.of_nat (tc_roottid ch)) prev pre *
    tc_subroot_rep dim plnode plclk ch 
      (tcs_head_Z_default lst suf)
      (* (match suf with nil => lst | ch' :: _ => (Z.of_nat (tc_roottid ch')) end)  *)
      (tcs_head_Z_default prev (rev pre))
      (* (match (rev pre) with nil => prev | ch' :: _ => (Z.of_nat (tc_roottid ch')) end)  *)
      (Z.of_nat par) *
    tc_chn_rep dim plnode plclk par lst (Z.of_nat (tc_roottid ch)) suf)%logic.
Proof.
  induction pre as [ | p pre IH ] using list_ind_2; intros; cbn delta -[sizeof tc_headch_Z] iota beta zeta.
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
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic (map tc_roottid chn)) |--
  tc_chn_rep dim plnode plclk par default_nodefield prev chn.
Proof.
  intros chn. induction chn as [ | ch chn IH ]; intros.
  - simpl. entailer.
  - cbn delta [map fold_right_sepcon] iota beta.
    rewrite Forall_cons_iff in Hchn_clk, Hprojc. simpl in Hprojn.
    destruct Hchn_clk as ((Hc1 & Hc2) & Hchn_clk), Hprojc as (Hch_c & Hprojc), 
      Hprojn as (Hch_n & Hprojn).
    specialize (IH (Z.of_nat (tc_roottid ch)) Hchn_clk Hprojc Hprojn).
    sep_apply IH. cbn delta [tc_chn_rep] iota beta.
    unfold clock_rep, node_rep.
    entailer!.
    1: apply nth_error_some_inrange_Z in Hch_n; lia.
    hnf in Hch_c. apply Foralltc_self in Hch_c.
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
  forall chn prev (Hnodup : NoDup (map tc_roottid chn)), 
  tc_chn_rep dim plnode plclk par default_nodefield prev chn |--
  EX f g, 
  !! (Forall (fun sub => Z.of_nat (tc_roottid sub) < dim /\
    (Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed)) chn) &&
  !! (forall lclk, 
    Zlength lclk = dim ->
    Forall (fun i => Znth (Z.of_nat i) lclk = f (Z.of_nat i)) (map tc_roottid chn) ->
    Forall (tc_rootclk_proj lclk) chn) && (* hmm *)
  !! (forall lnode, 
    Zlength lnode = dim ->
    Forall (fun i => Znth (Z.of_nat i) lnode = g (Z.of_nat i)) (map tc_roottid chn) ->
    is_tc_nodearray_proj_chnaux par lnode prev chn) &&
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (f (Z.of_nat i)) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (g (Z.of_nat i)) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic (map tc_roottid chn)).
Proof.
  intros chn. induction chn as [ | ch chn IH ]; intros.
  1:{
    simpl. Exists (fun _ : Z => default_clockstruct) (fun _ : Z => default_nodestruct).
    entailer!.
  }
  cbn delta [map fold_right_sepcon tc_chn_rep] iota beta.
  simpl in Hnodup. rewrite -> NoDup_cons_iff in Hnodup. destruct Hnodup as (Hnotin & Hnodup).
  unfold clock_rep, node_rep.
  Intros. sep_apply IH. Intros f g.
  Exists (fun x : Z => if Z.eqb x (Z.of_nat (tc_roottid ch)) then
    (clock_payload (Z.of_nat (tc_rootclk ch)) (Z.of_nat (tc_rootaclk ch)))
    else f x)
  (fun x : Z => if Z.eqb x (Z.of_nat (tc_roottid ch)) then
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
        destruct (Z.of_nat x =? Z.of_nat (tc_roottid ch)) eqn:E; auto.
        apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. now apply Hnotin in Hin.
    + constructor.
      * apply Znth_nth_error_result; auto. rewrite -> Zlength_correct in Hlen; lia.
      * match goal with HH : context[tc_rootclk_proj] |- _ => apply HH; auto end.
        eapply Forall_impl_impl. 2: apply Hb.
        apply Forall_forall. intros x Hin. 
        destruct (Z.of_nat x =? Z.of_nat (tc_roottid ch)) eqn:E; auto.
        apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. now apply Hnotin in Hin.
    + constructor; auto with lia.
  - Intros. rewrite ! Z.eqb_refl. entailer!.
    erewrite -> map_ext_Forall at 1; [ apply derives_refl | simpl ].
    apply Forall_forall. intros x Hin.
    destruct (Z.eqb (Z.of_nat x) (Z.of_nat (tc_roottid ch))) eqn:E; try reflexivity.
    apply Z.eqb_eq in E. apply Nat2Z.inj in E. subst x. apply Hnotin in Hin. destruct Hin.
Qed.

Lemma tc_proj2rep_noroot plclk plnode lclk lnode dim   
  (Hlenc : Zlength lclk = dim) (Hlenn : Zlength lnode = dim) :
  (* is_tc_clockarray_proj here? *)
  forall tc (Htc_clk : Foralltc (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc)
  (Hprojc : is_tc_clockarray_proj lclk tc) (* hmm *)
  (Hprojn : is_tc_nodearray_proj lnode tc),
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (Znth (Z.of_nat i) lclk) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (Znth (Z.of_nat i) lnode) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (map tc_roottid (flat_map tc_flatten (tc_rootchn tc)))) 
    (* (flat_map (fun tc' => map tc_roottid (tc_flatten tc')) (tc_rootchn tc)))  *)
  |-- tc_rep_noroot dim plnode plclk tc.
Proof.
  intros tc.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  cbn delta -[sizeof] iota beta.
  hnf in Hprojc, Hprojn. rewrite -> Foralltc_cons_iff in Hprojc, Hprojn, Htc_clk.
  destruct Hprojc as (_ & Hprojc), Hprojn as (Hchn & Hprojn), Htc_clk as (_ & Hchn_clk).
  simpl in Hchn.
  apply tc_chn_proj2rep with (lclk:=lclk) (lnode:=lnode) (plclk:=plclk) 
    (plnode:=plnode) (dim:=dim) in Hchn; auto.
  2: eapply Forall_impl; [ | apply Hchn_clk ]; apply Foralltc_self.
  pose proof (tc_flatten_root_chn_split chn) as Hperm.
  apply Permutation_map with (f:=tc_roottid) in Hperm.
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
  forall tc (Hnodup : NoDup (map tc_roottid (tc_flatten tc))), 
  tc_rep_noroot dim plnode plclk tc |--
  EX f g, 
  !! (Forall (Foralltc (fun sub => Z.of_nat (tc_roottid sub) < dim /\
    Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed)) (tc_rootchn tc)) &&
  !! (forall lclk, 
    Zlength lclk = dim ->
    Forall (fun i => Znth (Z.of_nat i) lclk = f (Z.of_nat i))
        (* over all subch, or tc? *)
      (map tc_roottid (flat_map tc_flatten (tc_rootchn tc))) ->
    Forall (is_tc_clockarray_proj lclk) (tc_rootchn tc)) && (* hmm *)
  !! (forall lnode, 
    Zlength lnode = dim ->
    Forall (fun i => Znth (Z.of_nat i) lnode = g (Z.of_nat i)) 
      (map tc_roottid (flat_map tc_flatten (tc_rootchn tc))) ->
    is_tc_nodearray_proj lnode tc) &&
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (f (Z.of_nat i)) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (g (Z.of_nat i)) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (map tc_roottid (flat_map tc_flatten (tc_rootchn tc)))).
Proof.
  intros tc.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  cbn delta -[sizeof] iota beta.
  simpl in Hnodup. rewrite -> NoDup_cons_iff in Hnodup. destruct Hnodup as (Hnotin & Hnodup).
  (* prepare this *)
  pose proof (tc_flatten_root_chn_split chn) as Hperm.
  apply Permutation_map with (f:=tc_roottid) in Hperm. rewrite map_app in Hperm.
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
    !! (Forall (Foralltc (fun sub => Z.of_nat (tc_roottid sub) < dim /\
      Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
      Z.of_nat (tc_rootaclk sub) <= Int.max_signed)) (flat_map tc_rootchn chn)) &&
    !! (forall lclk, 
      Zlength lclk = dim ->
      Forall (fun i => (f0 (Z.of_nat i)) = Znth (Z.of_nat i) lclk) 
        (map tc_roottid (flat_map tc_flatten (flat_map tc_rootchn chn))) ->
      Forall (is_tc_clockarray_proj lclk) (flat_map tc_rootchn chn)) &&
    !! (forall lnode, 
      Zlength lnode = dim ->
      Forall (fun i => (g0 (Z.of_nat i)) = Znth (Z.of_nat i) lnode) 
        (map tc_roottid (flat_map tc_flatten (flat_map tc_rootchn chn))) ->
      Forall (is_tc_nodearray_proj lnode) chn) &&
    fold_right_sepcon (map (fun i => 
      data_at Tsh t_struct_clock (f0 (Z.of_nat i)) 
        (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
      data_at Tsh t_struct_node (g0 (Z.of_nat i)) 
        (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
      (map tc_roottid (flat_map tc_flatten (flat_map tc_rootchn chn))))) as Hgoal.
  - sep_apply Hgoal. Intros f0 g0. fold (fold_right_sepcon).
    rewrite sepcon_comm, sepcon_map_data_at_merge_app with (fdec:=Nat.eq_dec); auto.
    erewrite <- fold_right_sepcon_permutation.
    2: apply Permutation_map, Hperm.
    (* Z is really inconvenient here ... *)
    Exists 
      (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) (map tc_roottid chn) then f x else f0 x)
      (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) (map tc_roottid chn) then g x else g0 x).
    apply andp_right1.
    + entailer!. split; [ | split ].
      1,3: intros ll Hlen Htmp; eapply Permutation_Forall in Htmp; [ | apply Hperm ]; 
        rewrite Forall_app in Htmp; destruct Htmp as (Ha & Hb).
      * constructor.
        --match goal with HH : context[is_tc_nodearray_proj_chnaux] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Ha.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tc_roottid chn)).
        --match goal with HH : context[is_tc_nodearray_proj] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Hb.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. destruct (in_dec Nat.eq_dec x (map tc_roottid chn)) as [ Heq | ]; auto.
          specialize (Hdj x). tauto.
      * unfold is_tc_clockarray_proj.
        eapply Forall_impl. 1: intros ? HH; apply Foralltc_cons_iff'; apply HH.
        apply Forall_and.
        --match goal with HH : context[tc_rootclk_proj] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Ha.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tc_roottid chn)).
        --apply Forall_map, Forall_concat. rewrite <- flat_map_concat_map.
          match goal with HH : context[is_tc_clockarray_proj] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Hb.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. destruct (in_dec Nat.eq_dec x (map tc_roottid chn)) as [ Heq | ]; auto.
          specialize (Hdj x). tauto.
      * eapply Forall_impl. 1: intros ? HH; apply Foralltc_cons_iff'; apply HH.
        apply Forall_and; auto.
        (* TODO streamline this *)
        apply Forall_map, Forall_concat. rewrite <- flat_map_concat_map. auto.
    + Intros.
      erewrite map_ext with (l:=(map tc_roottid (flat_map tc_flatten chn))).
      1: apply derives_refl.
      intros x. simpl. rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tc_roottid chn)).
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
        (map tc_roottid (flat_map tc_flatten (tc_rootchn ch))) then f x else f0 x)
      (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) 
        (map tc_roottid (flat_map tc_flatten (tc_rootchn ch))) then g x else g0 x).
    apply andp_right1.
    + entailer!. split; [ | split ].
      1,3: intros ll Hlen Htmp; rewrite <- flat_map_app, -> map_app, -> Forall_app in Htmp; 
        destruct Htmp as (Ha & Hb).
      * constructor.
        --match goal with HH : context[is_tc_nodearray_proj] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Ha.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. 
          now destruct (in_dec Nat.eq_dec x (map tc_roottid (flat_map tc_flatten (tc_rootchn ch)))).
        --match goal with HH : context[Forall (is_tc_nodearray_proj _)] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Hb.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. 
          destruct (in_dec Nat.eq_dec x (map tc_roottid (flat_map tc_flatten (tc_rootchn ch)))) as [ Heq | ]; auto.
          specialize (Hdj x). tauto.
      * apply Forall_app. split.
        --match goal with HH : context[Forall (is_tc_clockarray_proj _) (tc_rootchn ch)] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Ha.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. 
          now destruct (in_dec Nat.eq_dec x (map tc_roottid (flat_map tc_flatten (tc_rootchn ch)))).
        --match goal with HH : context[Forall (is_tc_clockarray_proj _) (flat_map tc_rootchn chn)] |- _ => apply HH; auto end.
          eapply Forall_impl_impl. 2: apply Hb.
          apply Forall_forall. intros x Hin. rewrite Nat2Z.id. 
          destruct (in_dec Nat.eq_dec x (map tc_roottid (flat_map tc_flatten (tc_rootchn ch)))) as [ Heq | ]; auto.
          specialize (Hdj x). tauto.
      * now apply Forall_app.
    + Intros. 
      rewrite sepcon_comm, sepcon_map_data_at_merge_app with (fdec:=Nat.eq_dec); auto.
      rewrite <- map_app, -> flat_map_app.
      erewrite map_ext with (l:=(map tc_roottid
        (flat_map tc_flatten (tc_rootchn ch ++ flat_map tc_rootchn chn)))).
      1: apply derives_refl.
      intros x. simpl. rewrite Nat2Z.id. 
      now destruct (in_dec Nat.eq_dec x (map tc_roottid (flat_map tc_flatten (tc_rootchn ch)))).
Qed.

Lemma tc_proj2rep plclk plnode lclk lnode dim   
  (Hlenc : Zlength lclk = dim) (Hlenn : Zlength lnode = dim)
  tc (Htc_clk : Foralltc (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc)
  (Hprojc : is_tc_clockarray_proj lclk tc)
  (Hprojn : is_tc_nodearray_proj_full lnode tc) :
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (Znth (Z.of_nat i) lclk) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (Znth (Z.of_nat i) lnode) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (map tc_roottid (tc_flatten tc))) |-- 
  tc_rep dim plnode plclk tc.
Proof.
  destruct tc as [(u, ?, ?) chn] eqn:E.
  cbn delta -[sizeof] iota beta.
  replace chn with (tc_rootchn tc) by now rewrite E.
  subst tc. destruct Hprojn as (Hroot & Hprojn).
  sep_apply (tc_proj2rep_noroot plclk plnode lclk lnode dim); try tauto.
  unfold tc_rep. simpl tc_rootchn. 
  (* TODO why no cancel_right? *)
  match goal with |- _ |-- (?a * ?b) => rewrite (sepcon_comm a b) end.
  apply cancel_left.
  pose proof Hroot as Htmp. apply nth_error_some_inrange_Z in Htmp. simpl in Htmp.
  hnf in Hroot. apply nth_error_Znth_result in Hroot. simpl in Hroot. 
  apply Foralltc_self, nth_error_Znth_result in Hprojc. simpl in Hprojc. 
  rewrite Hroot, Hprojc.
  unfold tc_root_rep, clock_rep, node_rep. simpl.
  entailer!. 
  apply Foralltc_self in Htc_clk. simpl in Htc_clk. lia.
Qed.

Lemma tc_rep2proj plclk plnode dim tc (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  tc_root_rep dim plnode plclk tc * tc_rep_noroot dim plnode plclk tc |--
  EX f g, 
  !! (Foralltc (fun sub => Z.of_nat (tc_roottid sub) < dim /\
    Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) &&
  !! (forall lclk, 
    Zlength lclk = dim ->
    Forall (fun i => Znth (Z.of_nat i) lclk = f (Z.of_nat i)) (map tc_roottid (tc_flatten tc)) ->
    is_tc_clockarray_proj lclk tc) &&
  !! (forall lnode, 
    Zlength lnode = dim ->
    Forall (fun i => Znth (Z.of_nat i) lnode = g (Z.of_nat i)) (map tc_roottid (tc_flatten tc)) ->
    is_tc_nodearray_proj_full lnode tc) &&
  fold_right_sepcon (map (fun i => 
    data_at Tsh t_struct_clock (f (Z.of_nat i)) 
      (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node (g (Z.of_nat i)) 
      (offset_val (sizeof t_struct_node * Z.of_nat i) plnode))%logic 
    (map tc_roottid (tc_flatten tc))).
Proof.
  sep_apply tc_rep_noroot2proj. Intros f g.
  destruct tc as [(u, clk, aclk) chn]. 
  unfold tc_root_rep, clock_rep, node_rep. Intros. 
  unfold tc_headch_Z. cbn delta -[sizeof] beta iota in * |- *. 
  (* fold (tcs_head_Z chn).  *)
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
    (filter (fun t => negb (ssrbool.isSome (find (has_same_tid t) tcs))) 
      (map Z.to_nat (upto (Z.to_nat dim))))) |-- 
  unused_bag_rep dim plnode plclk tcs.
Proof.
  unfold unused_bag_rep.
  erewrite map_ext_Forall. 1: apply derives_refl.
  simpl. apply Forall_forall. intros t (Hin & Hnotin%negb_true_iff)%filter_In. 
  rewrite <- seq_upto, -> in_seq in Hin. simpl in Hin.
  assert (0 <= Z.of_nat t < dim) as Hin' by lia.
  destruct (find (has_same_tid t) tcs) eqn:E; try discriminate.
  hnf in Hprojc, Hprojn.
  rewrite Zlength_correct in Hlenc, Hlenn.
  (* ... *)
  f_equal; [ destruct (nth_error lclk t) eqn:EE | destruct (nth_error lnode t) eqn:EE ].
  all: try apply nth_error_None in EE; try lia.
  all: f_equal; apply nth_error_Znth_result.
  - pose proof EE as Etmp. apply Hprojc in Etmp; congruence.
  - pose proof EE as Etmp. apply Hprojn in Etmp; congruence.
Qed.

Fact tc_all_roottid_equal_to_range_filter tc (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) 
  dim (Hdim : Foralltc (fun tc' : treeclock => Z.of_nat (tc_roottid tc') < dim) tc) :
  Permutation (map tc_roottid (tc_flatten tc))
  (filter (fun t : nat => ssrbool.isSome (find (has_same_tid t) (tc_flatten tc)))
    (map Z.to_nat (upto (Z.to_nat dim)))).
Proof.
  apply NoDup_Permutation; auto.
  - apply NoDup_filter. rewrite <- seq_upto. apply seq_NoDup.
  - intros x. rewrite <- seq_upto, -> filter_In, -> in_seq, -> tcs_find_in_iff.
    split; try tauto. intros HH. split; auto.
    rewrite <- tcs_find_in_iff in HH.
    apply Foralltc_Forall_subtree in Hdim; auto.
    rewrite -> Forall_forall in Hdim. 
    rewrite in_map_iff in HH. destruct HH as (sub & <- & Hin).
    apply Hdim in Hin. lia.
Qed.

Lemma tc_array2rep_and_bag plclk plnode lclk lnode dim tc
  (Hlenc : Zlength lclk = dim) (Hlenn : Zlength lnode = dim) (Hdim : 0 < dim)
  (Htc_clk : Foralltc (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc)
  (* now this is required *)
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  (Hprojc : is_tc_clockarray_proj lclk tc)
  (Hprojn : is_tc_nodearray_proj_full lnode tc) 
  (Hprojce : clockarray_emptypart lclk (tc_flatten tc))
  (Hprojne : nodearray_emptypart lnode (tc_flatten tc)) :
  data_at Tsh (tarray t_struct_clock dim) lclk plclk *
    data_at Tsh (tarray t_struct_node dim) lnode plnode |--
  !! (field_compatible (tarray t_struct_clock dim) [] plclk) &&
  !! (field_compatible (tarray t_struct_node dim) [] plnode) &&
  tc_rep dim plnode plclk tc * 
    unused_bag_rep dim plnode plclk (tc_flatten tc).
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
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  tc_root_rep dim plnode plclk tc * tc_rep_noroot dim plnode plclk tc *
    unused_bag_rep dim plnode plclk (tc_flatten tc) |--
  EX f g, 
  !! (Foralltc (fun sub => Z.of_nat (tc_roottid sub) < dim /\
    Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) &&
  !! (forall lclk, 
    Zlength lclk = dim ->
    (forall i, 0 <= i < dim ->
      Znth i lclk = f i) ->
        (* (if in_dec Nat.eq_dec (Z.to_nat i) (map tc_roottid (tc_flatten tc)) 
        then f i else default_clockstruct)) -> *)
    is_tc_clockarray_proj lclk tc /\ clockarray_emptypart lclk (tc_flatten tc)) &&
  !! (forall lnode, 
    Zlength lnode = dim ->
    (forall i, 0 <= i < dim ->
      Znth i lnode = g i) ->
        (* (if in_dec Nat.eq_dec (Z.to_nat i) (map tc_roottid (tc_flatten tc)) 
        then g i else default_nodestruct)) -> *)
    is_tc_nodearray_proj_full lnode tc /\ nodearray_emptypart lnode (tc_flatten tc)) &&
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
  match goal with HH : Foralltc _ _ |- _ => rename HH into Hb end.
  assert (Forall (fun x => Z.of_nat x < dim) (map tc_roottid (tc_flatten tc))) as Htid.
  { apply List.Forall_map, Foralltc_Forall_subtree. now apply Foralltc_and in Hb. }
  epose proof (tc_all_roottid_equal_to_range_filter _ Hnodup dim ?[Goalq]) as Hperm.
  [Goalq]: now apply Foralltc_and in Hb.
  match type of Hperm with Permutation ?al ?bl => assert (forall x, In x al <-> In x bl) as Hinin end.
  { pose proof Hperm as Hperm'. symmetry in Hperm'. intros. split; intros. all: eapply Permutation_in; eauto. }

  erewrite -> fold_right_sepcon_permutation at 1.
  2: apply Permutation_map, Hperm.
  erewrite -> sepcon_map_data_at_merge_app with (fdec:=Nat.eq_dec).
  2:{ intros a. rewrite ! filter_In, negb_true_iff. eqsolve. }
  erewrite -> fold_right_sepcon_permutation.
  2: symmetry; apply Permutation_map, Permutation_split_combine.
  Exists (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) (map tc_roottid (tc_flatten tc)) 
    then f x else default_clockstruct)
  (fun x : Z => if in_dec Nat.eq_dec (Z.to_nat x) (map tc_roottid (tc_flatten tc)) 
    then g x else default_nodestruct).
  apply andp_right1.
  - entailer!. split.
    all: intros ll Hlen Hcorr.
    + split.
      * match goal with HH : context[is_tc_nodearray_proj_full] |- _ => apply HH; auto end.
        apply Forall_forall. intros x Hin.
        rewrite Hcorr. 2: rewrite Forall_forall in Htid; apply Htid in Hin; lia.
        rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tc_roottid (tc_flatten tc))).
      * hnf. intros x np Hn He.
        assert (0 <= Z.of_nat x < dim) as Hrange by (apply nth_error_some_inrange_Z in He; lia).
        specialize (Hcorr _ Hrange).
        apply nth_error_Znth_result in He. rewrite <- He, -> Hcorr.
        rewrite Nat2Z.id. 
        destruct (in_dec Nat.eq_dec x (map tc_roottid (tc_flatten tc))) as [ Hin | ]; auto.
        now rewrite -> tcs_find_in_iff, -> Hn in Hin.
    + split.
      * match goal with HH : context[is_tc_clockarray_proj] |- _ => apply HH; auto end.
        apply Forall_forall. intros x Hin.
        rewrite Hcorr. 2: rewrite Forall_forall in Htid; apply Htid in Hin; lia.
        rewrite Nat2Z.id. now destruct (in_dec Nat.eq_dec x (map tc_roottid (tc_flatten tc))).
      * hnf. intros x np Hn He.
        assert (0 <= Z.of_nat x < dim) as Hrange by (apply nth_error_some_inrange_Z in He; lia).
        specialize (Hcorr _ Hrange).
        apply nth_error_Znth_result in He. rewrite <- He, -> Hcorr.
        rewrite Nat2Z.id. 
        destruct (in_dec Nat.eq_dec x (map tc_roottid (tc_flatten tc))) as [ Hin | ]; auto.
        now rewrite -> tcs_find_in_iff, -> Hn in Hin.
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
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  tc_root_rep dim plnode plclk tc * tc_rep_noroot dim plnode plclk tc *
    unused_bag_rep dim plnode plclk (tc_flatten tc) |--
  EX lnode lclk, 
  !! (Zlength lnode = dim) &&
  !! (Zlength lclk = dim) &&
  !! (Foralltc (fun sub => Z.of_nat (tc_roottid sub) < dim /\
    Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) <= Int.max_signed) tc) &&
  !! (is_tc_clockarray_proj lclk tc) && !! (clockarray_emptypart lclk (tc_flatten tc)) &&
  !! (is_tc_nodearray_proj_full lnode tc) && !! (nodearray_emptypart lnode (tc_flatten tc)) &&
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

Lemma tc_rep_subtree_frame_pre tc : forall l sub (Hsub : subtc_witness l sub tc) 
  dim plnode plclk z1 z2 z3,
  tc_subroot_rep dim plnode plclk tc z1 z2 z3 *
    tc_rep_noroot dim plnode plclk tc |--
  EX z1' z2' z3' ,
  !! (l = nil -> z1 = z1' /\ z2 = z2' /\ z3 = z3') &&
  tc_subroot_rep dim plnode plclk sub z1' z2' z3' *
    tc_rep_noroot dim plnode plclk sub *
  (ALL sub', !! (tc_roottid sub = tc_roottid sub') -->
    ((tc_subroot_rep dim plnode plclk sub' z1' z2' z3' *
      tc_rep_noroot dim plnode plclk sub') -*
    tc_subroot_rep dim plnode plclk (tc_locate_update tc l sub') z1 z2 z3 *
      tc_rep_noroot dim plnode plclk (tc_locate_update tc l sub'))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
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
    cbn delta [tc_rep_noroot tc_roottid tc_rootclk tc_rootaclk tc_rootinfo info_tid info_clk info_aclk] beta iota.
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
    simpl tc_locate_update. rewrite Enth.
    unfold tc_rep_noroot at 4. fold tc_rep_noroot.
    rewrite <- ! Zlength_correct, -> ! upd_Znth_char; auto.
    rewrite -> map_app, -> fold_right_sepcon_app, -> tc_chn_rep_segment.
    cbn delta [fold_right_sepcon map] beta iota.
    unfold tc_subroot_rep at 2.
    cbn delta [tc_rep_noroot tc_roottid tc_rootclk tc_rootaclk tc_rootinfo info_tid info_clk info_aclk] beta iota.
    entailer!.

    (* still, need to destruct l and discuss? *)
    assert (tc_roottid (tc_locate_update ch l sub') = tc_roottid ch) as Eid.
    {
      destruct l.
      - simpl in Hsub |- *. now injection Hsub as <-.
      - destruct ch as [ni chn]. simpl in Hsub |- *. destruct (nth_error chn n); eqsolve.
    }
    rewrite -> ! Eid.
    entailer!.
    destruct pre; unfold tc_headch_Z; simpl; now try rewrite Eid.
Qed. 

Lemma tc_rep_subtree_frame tc : forall l sub (Hsub : subtc_witness l sub tc) 
  dim plnode plclk z1 z2 z3,
  tc_subroot_rep dim plnode plclk tc z1 z2 z3 *
    tc_rep_noroot dim plnode plclk tc |--
  EX z1' z2' z3' ,
  !! (l = nil -> z1 = z1' /\ z2 = z2' /\ z3 = z3') &&
  tc_subroot_rep dim plnode plclk sub z1' z2' z3' *
    tc_rep_noroot dim plnode plclk sub *
  (ALL chn_sub', 
    (tc_subroot_rep dim plnode plclk (Node (tc_rootinfo sub) chn_sub') z1' z2' z3' *
      tc_rep_noroot dim plnode plclk (Node (tc_rootinfo sub) chn_sub')) -*
    tc_subroot_rep dim plnode plclk (tc_locate_update tc l (Node (tc_rootinfo sub) chn_sub')) z1 z2 z3 *
      tc_rep_noroot dim plnode plclk (tc_locate_update tc l (Node (tc_rootinfo sub) chn_sub'))).
Proof.
  intros.
  sep_eapply tc_rep_subtree_frame_pre.
  1: apply Hsub.
  Intros z1' z2' z3'. Exists z1' z2' z3'.
  entailer!.
  apply allp_right. intros chn_sub'.
  allp_left (Node (tc_rootinfo sub) chn_sub').
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
    tc : (@treeclock nat), plclk : val, plnode : val, plstk : val, p : val,
    tc' : (@treeclock nat), plclk' : val, plnode' : val, plstk' : val, p' : val
  PRE [ tptr t_struct_treeclock, tptr t_struct_treeclock ]
    (* PROP (is_pos_tshort dim) *)
    PROP (is_pos_tint dim; 
      (* join requirement *)
      tc_shape_inv tc; tc_shape_inv tc'; tc_respect tc' tc; 
      (tc_getclk (tc_roottid tc) tc' <= tc_rootclk tc)%nat)
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
    pre : list (@treeclock nat), ch : (@treeclock nat), suf : list (@treeclock nat), 
    z1 : Z, z2 : Z, z3 : Z
  PRE [ tptr t_struct_treeclock, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; 
      Z.of_nat par < dim;
      (* required for judging whether par.headch = ch *)
      NoDup (map tc_roottid (pre ++ ch :: suf)))
    PARAMS (p; Vint (Int.repr (Z.of_nat (tc_roottid ch))); 
      offset_val (sizeof t_struct_node * Z.of_nat (tc_roottid ch)) plnode)
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
    tc : (@treeclock nat), tc_par : (@treeclock nat), l : list nat, 
    pre : list (@treeclock nat), sub : (@treeclock nat), suf : list (@treeclock nat)
  PRE [ tptr t_struct_treeclock, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; 
      Z.of_nat (tc_roottid tc_par) < dim;
      subtc_witness l tc_par tc; 
      tc_rootchn tc_par = pre ++ sub :: suf; 
      (* still required *)
      NoDup (map tc_roottid (tc_flatten tc)))
    PARAMS (p; Vint (Int.repr (Z.of_nat (tc_roottid sub))); 
      offset_val (sizeof t_struct_node * Z.of_nat (tc_roottid sub)) plnode)
    SEP (tc_rep dim plnode plclk tc;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p)
  POST [ tvoid ]
    EX z1' z2' z3' : Z,
    PROP ()
    RETURN ()
    SEP (tc_rep dim plnode plclk (tc_locate_update tc l (Node (tc_rootinfo tc_par) (pre ++ suf)));
      tc_subroot_rep dim plnode plclk sub z1' z2' z3';
      tc_rep_noroot dim plnode plclk sub;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p).

Definition push_child_spec_local :=
  DECLARE _push_child
  WITH dim : Z, v1 : val, plclk : val, plnode : val, v2 : val, v3 : val, p : val, 
    par : nat, 
    chn : list (@treeclock nat), sub : (@treeclock nat),
    z1 : Z, z2 : Z, z3 : Z, z4 : Z, z5 : Z, z6 : Z
  PRE [ tptr t_struct_treeclock, tint, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; 
      Z.of_nat par < dim)
    PARAMS (p; Vint (Int.repr (Z.of_nat par)); Vint (Int.repr (Z.of_nat (tc_roottid sub))); 
      offset_val (sizeof t_struct_node * Z.of_nat (tc_roottid sub)) plnode)
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
    SEP (data_at Tsh t_struct_node (node_payload z1 z2 z3 (Z.of_nat (tc_roottid sub)))
        (offset_val (sizeof t_struct_node * Z.of_nat par) plnode); 
      tc_chn_rep dim plnode plclk par default_nodefield default_nodefield (sub :: chn); 
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p).

Definition push_child_spec :=
  DECLARE _push_child
  WITH dim : Z, v1 : val, plclk : val, plnode : val, v2 : val, v3 : val, p : val, 
    tc : (@treeclock nat), tc_par : (@treeclock nat), sub : (@treeclock nat), l : list nat, 
    z1 : Z, z2 : Z, z3 : Z
  PRE [ tptr t_struct_treeclock, tint, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; 
      Z.of_nat (tc_roottid tc_par) < dim; 
      subtc_witness l tc_par tc)
    PARAMS (p; Vint (Int.repr (Z.of_nat (tc_roottid tc_par))); Vint (Int.repr (Z.of_nat (tc_roottid sub))); 
      offset_val (sizeof t_struct_node * Z.of_nat (tc_roottid sub)) plnode)
    SEP (tc_rep dim plnode plclk tc;
      tc_subroot_rep dim plnode plclk sub z1 z2 z3;
      tc_rep_noroot dim plnode plclk sub;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (tc_rep dim plnode plclk (tc_locate_update tc l (Node (tc_rootinfo tc_par) (sub :: tc_rootchn tc_par)));
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk, (plnode, (v2, v3))))) p).

Definition get_updated_nodes_join_chn_spec :=
  DECLARE _get_updated_nodes_join_chn
  WITH dim : Z, 
    (* plnode is not used here *)
    tc : (@treeclock nat), plclk : val, plnode : val, plstk : val, top : nat, p : val,
    v1 : val, plclk' : val, plnode' : val, v2 : val, v3 : val, p' : val,
    (* decoupling clk and par' *)
    clk : nat, par' : nat, chn' : list (@treeclock nat), 
    lclk : list (reptype t_struct_clock), lstk : list val,
    lclk' : list (reptype t_struct_clock), lnode' : list (reptype t_struct_node)
  PRE [ tptr t_struct_treeclock, tptr t_struct_treeclock, tint, tint ]
    PROP (0 <= dim <= Int.max_signed; 
      Z.of_nat par' < dim; 
      Foralltc (fun sub => Z.of_nat (tc_rootclk sub) <= Int.max_signed /\ 
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
      clockarray_emptypart lclk (tc_flatten tc); 
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
      data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tc_roottid tc)) 
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
            (map tc_roottid (tc_get_updated_nodes_join_aux tc clk chn'))) ++
          skipn (top + length (tc_get_updated_nodes_join_aux tc clk chn')) lstk) plstk;
      data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tc_roottid tc)) 
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
(* FIXME: rewrite this definition using tc_roottid to make it easier to deal with? *)
Definition node_is_null_as_bool tc (idx : nat) :=
  ((match tc with Node (mkInfo idx' _ _) nil => Nat.eqb idx idx' | _ => false end) ||
    (match tc_getnode idx tc with None => true | _ => false end))%bool.

Definition node_is_null_spec :=
  DECLARE _node_is_null
  WITH dim : Z, idx : nat, lnode : list (reptype t_struct_node),
    tc : (@treeclock nat), v1 : val, plnode : val, v2 : val, v3 : val, p : val
  PRE [ tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; Z.of_nat idx < dim; 
      Z.of_nat (tc_roottid tc) < dim; 
      Zlength lnode = dim; 
      nodearray_emptypart lnode (tc_flatten tc); is_tc_nodearray_proj_full lnode tc)
    PARAMS (offset_val (sizeof t_struct_node * Z.of_nat idx) plnode)
    SEP (data_at Tsh (tarray t_struct_node dim) lnode plnode;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tc_roottid tc))), 
          (v1, (plnode, (v2, v3))))) p)
  POST [ tint ]
    PROP () 
    RETURN (Val.of_bool (node_is_null_as_bool tc idx))
    SEP (data_at Tsh (tarray t_struct_node dim) lnode plnode;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tc_roottid tc))), 
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
  destruct (tc_getnode idx tc) as [ res | ] eqn:E.
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
      apply tcs_find_has_tid in E. destruct E as (Hin & Eid).
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
        rewrite -> Foralltc_Forall_subtree, -> Forall_forall in Hproj. specialize (Hproj _ Hin).
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
  match goal with HH : context [Foralltc ?a tc] |- _ => 
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
      Forall (fun tc' => (clk < tc_rootaclk tc' \/ (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc')%nat) (firstn i chn');
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
            (map tc_roottid (tc_get_updated_nodes_join_aux tc clk (firstn i chn')))) ++
        skipn (top + length (tc_get_updated_nodes_join_aux tc clk (firstn i chn'))) lstk) plstk;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim),
          (Vint (Int.repr (Z.of_nat (tc_roottid tc))),
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
  cbn delta [tcs_head_Z_default tcs_head_Z tc_roottid tc_rootinfo info_tid] beta iota in *.
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
  apply Foralltc_self, nth_error_Znth_result in Eclk'.
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
  repable_signed_gen (Z.of_nat (tc_roottid sub) :: Z.of_nat par :: nil).
  forward. forward. 
  rewrite_sem_add_ptr_int. forward.
  (* operate *)
  match goal with |- semax _ ?pls _ _ => pose (qq:=pls) end.
  pattern (tc_chn_rep dim plnode plclk par default_nodefield default_nodefield chn) in qq.
  pose proof (eq_refl qq) as Htmp. subst qq. 
  match type of Htmp with ?f _ = _ => 
    forward_if (f (tc_chn_rep dim plnode plclk par default_nodefield (Z.of_nat (tc_roottid sub)) chn)) end.
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
      repable_signed_gen (Z.of_nat (tc_roottid ch) :: nil).
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
  match goal with HH : context[subtc_witness] |- _ => rename HH into Hsub end.
  rewrite TT_andp.
  sep_apply (tc_rep_subtree_frame _ _ _ Hsub).
  Intros z1' z2' z3'.
  destruct tc_par as [ni chn].
  unfold tc_subroot_rep at 1, node_rep at 1. Intros.
  unfold tc_rep_noroot at 1. fold tc_rep_noroot.
  unfold tc_headch_Z at 1, tcs_head_Z at 1.
  cbn delta [tc_rootchn tc_roottid tc_rootclk tc_rootaclk tc_rootinfo] beta iota.

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
    entailer!.
  }
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
  match goal with HH : context[NoDup] |- _ => rename HH into Hnodup end.
  sep_apply tc_chn_rep_segment.
  unfold tc_subroot_rep, node_rep, node_payload. Intros.
  repable_signed_gen (Z.of_nat (tc_roottid ch) :: nil).
  forward. forward. forward. forward. forward.
  rewrite_sem_add_ptr_int. forward.

  (* TODO this would result in some repetition, but anyway for now *)
  apply semax_if_seq. forward_if.
  { 
    (* has to use assert_PROP to get the range of (tc_roottid t) *)
    assert_PROP (pre = nil).
    {
      destruct pre as [ | t pre ]. 1: entailer.
      simpl tc_chn_rep. Intros.
      repable_signed_gen (Z.of_nat (tc_roottid t) :: nil).
      match goal with HH : Int.repr _ = Int.repr _ |- _ => rename HH into Heq end.
      cbn in Heq. apply repr_inj_signed in Heq; auto.
      simpl in Hnodup. apply NoDup_cons_iff, proj1 in Hnodup.
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
        repable_signed_gen (Z.of_nat (tc_roottid t) :: nil).
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
        repable_signed_gen (Z.of_nat (tc_roottid t) :: nil).
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
  destruct w as ((((((((((((dim, v1), plclk), plnode), v2), v3), p), tc), tc_par), l), pre), sub), suf).
  Intros.
  (* first do subtree split *)
  unfold tc_rep at 1, tc_root_rep at 1.
  (* TODO streamline this? *)
  fold (tc_subroot_rep dim plnode plclk tc default_nodefield default_nodefield default_nodefield).
  match goal with HH : context[subtc_witness] |- _ => rename HH into Hsub end.
  rewrite TT_andp.
  sep_apply (tc_rep_subtree_frame _ _ _ Hsub).
  Intros z1 z2 z3.
  destruct tc_par as [ni chn].
  unfold tc_subroot_rep at 1, node_rep at 1. Intros.
  unfold tc_rep_noroot at 1. fold tc_rep_noroot.
  match goal with HH : context[pre ++ sub :: suf] |- _ => rename HH into Echn end.
  simpl in Echn. subst chn.
  unfold tc_headch_Z at 1, tcs_head_Z at 1.
  cbn delta [tc_rootchn tc_roottid tc_rootclk tc_rootaclk tc_rootinfo] beta iota.

  Exists (((((((((((((dim, v1), plclk), plnode), v2), v3), p), info_tid ni), pre), sub), suf), z1), z2), z3).
  match goal with |- (?a * _ * (_ * ?b) * ?c * _)%logic |-- _ => Exists (a * b * c)%logic end.
  entailer!.
  split.
  2:{
    apply subtc_witness_subtc in Hsub.
    match goal with HH : NoDup _ |- _ => rename HH into Hnodup end.
    rewrite -> tid_nodup_Foralltc_id in Hnodup.
    eapply Foralltc_subtc in Hsub. 2: apply Hnodup.
    simpl in Hsub. 
    now apply NoDup_cons_iff, proj2, tid_nodup_root_chn_split in Hsub.
  }
  intros. Intros z1' z2' z3'. Exists z1' z2' z3'. entailer!.
  allp_left (pre ++ suf).
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
    entailer!.
  }
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
  (Echn : tc_rootchn tc = pre ++ sub :: suf) (Hin : In sub (tc_rootchn tc))
  lnode prev (Hproj : is_tc_nodearray_proj_chnaux (tc_roottid tc) lnode prev (tc_rootchn tc)),
  Znth (Z.of_nat (tc_roottid sub)) lnode = node_payload 
    (tcs_head_Z suf) 
    (match (rev pre) with nil => prev | ch :: _ => Z.of_nat (tc_roottid ch) end) 
    (Z.of_nat (tc_roottid tc))
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
  (Echn : tc_rootchn tc = pre ++ sub :: suf) (Hin : In sub (tc_rootchn tc))
  lnode (Hproj : is_tc_nodearray_proj_chnaux (tc_roottid tc) lnode default_nodefield (tc_rootchn tc)),
  Znth (Z.of_nat (tc_roottid sub)) lnode = node_payload 
    (tcs_head_Z suf) (tcs_head_Z (rev pre)) (Z.of_nat (tc_roottid tc)) (tc_headch_Z sub).
Proof. intros. now apply nodearray_proj_read_correct_pre. Qed.

(* TODO why this is not proved? *)

Fact find_flat_map_some {A B : Type} (f : A -> list B) (l : list A)
  (g : B -> bool) :
  forall res, find g (flat_map f l) = Some res ->
  exists x, In x l /\ find g (f x) = Some res.
Proof.
  induction l as [ | x l IH ]; intros; simpl in H; try eqsolve.
  rewrite -> find_app in H.
  destruct (find g (f x)) as [ res' | ] eqn:E.
  - injection H as ->. simpl. eauto.
  - simpl. apply IH in H. firstorder.
Qed.

(* what is the usage of exists here ... *)

Fact subtc_has_parent tc 
  (* (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))  *)
  (idx : nat) (Hneq : idx <> tc_roottid tc) 
  (* TODO this condition may be revised *)
  res (Hres : tc_getnode idx tc = Some res) :
  exists tc_par, subtc tc_par tc /\ In res (tc_rootchn tc_par).
Proof.
  revert idx res Hres Hneq.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in Hres, Hneq.
  destruct (eqdec u idx); simpl in Hres; try eqsolve.
  apply find_flat_map_some in Hres.
  destruct Hres as (ch & Hin_ch & Hres).
  rewrite -> Forall_forall in IH. specialize (IH _ Hin_ch).
  fold (tc_getnode idx ch) in Hres.
  destruct (eqdec idx (tc_roottid ch)) as [ -> | ].
  - exists (Node (mkInfo u clk aclk) chn).
    split. 1: hnf; eqsolve.
    rewrite -> tc_getnode_self in Hres. simpl. eqsolve.
  - apply IH in Hres; auto.
    destruct Hres as (tc_par & Hsub & Hin_sub).
    exists tc_par.
    split; auto. apply subtc_trans with (tc':=ch); auto.
    now apply subtc_chn.
Qed.

Theorem body_join: 
  semax_body Vprog Gprog f_join join_spec.
Proof.
  saturate_lemmas.

  start_function.
  (* prepare *)
  unfold treeclock_rep.
  Intros. Intros lclk lnode lstk.
  (* TODO cannot customize the name of hypothesis? *)
  Intros. Intros lclk' lnode' lstk'.
  unfold treeclock_payload.
  unfold is_pos_tint in *.
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
  match goal with HH : Z.of_nat (tc_roottid tc) < dim |- _ => rename HH into Hlt end.
  match goal with HH : Z.of_nat (tc_roottid tc') < dim |- _ => rename HH into Hlt' end.
  match goal with HH : context [Foralltc ?a tc] |- _ => 
    match a with context[tc_rootclk] => rename HH into Hcb_tc end end.
  match goal with HH : context [Foralltc ?a tc'] |- _ => 
    match a with context[tc_rootclk] => rename HH into Hcb_tc' end end.
  epose proof (is_tc_nodearray_proj_tid_bounded _ _ (proj2 Hprojn1) ?[Goalq]) as Htid.
  [Goalq]: congruence.
  epose proof (is_tc_nodearray_proj_tid_bounded _ _ (proj2 Hprojn1') ?[Goalq]) as Htid'.
  [Goalq]: congruence.
  rewrite -> Hlen_lnode in Htid.
  rewrite -> Hlen_lnode' in Htid'.
  (* TODO what does it mean for "ca"? *)
  pose proof (is_tc_clockarray_proj_nth _ _ Hprojc1) as Hca_tc.
  pose proof (is_tc_clockarray_proj_nth _ _ Hprojc1') as Hca_tc'.
  assert (0 < dim) as Hdim by lia.
  pose proof (tid_nodup _ Hshape) as Hnodup.
  pose proof (tid_nodup _ Hshape') as Hnodup'.

  forward. forward. 
  forward_if.
  {
    match goal with H : _ |- _ => apply Nat2Z.inj in H; rename H into Erootid end.
    apply tc_join_roottid_same_trivial in Erootid.
    2: lia.
    forward. 
    unfold treeclock_rep at 1. Exists lclk lnode lstk.
    unfold treeclock_rep at 1. Exists lclk' lnode' lstk'.
    rewrite -> ! Erootid.
    entailer!.
  }

  match goal with H : _ |- _ => rewrite -> Nat2Z.inj_iff in H; rename H into Hrootid end.
  forward. forward. forward.

  array_focus (Z.of_nat (tc_roottid tc')) plclk' witheqn Etmp.
  rewrite_sem_add_ptr_int.
  pose proof (Foralltc_self _ _ Hca_tc') as Etmp2. cbn in Etmp2.
  rewrite -> Etmp.
  read_clock witheqn Etmp2. clear Etmp2.
  array_unfocus witheqn Etmp.

  forward. forward. forward. forward.
  rewrite_sem_add_ptr_int. 
  array_focus (Z.of_nat (tc_roottid tc')) plclk witheqn Etmp.
  rewrite -> Etmp.
  assert (0 <= Z.of_nat (tc_roottid tc') < Zlength lclk) as Eclk by (split; lia; congruence).
  apply clockarray_proj_tc_getinfo with (tc:=tc) in Eclk; try assumption.
  rewrite -> Nat2Z.id in Eclk.
  read_clock' witheqn Eclk. clear Eclk.
  array_unfocus witheqn Etmp.

  (* range guarantee *)
  pose proof Hcb_tc' as Hcb_tc'root. apply Foralltc_self, proj1 in Hcb_tc'root.
  pose proof (tc_getclk_in_int_range _ Hcb_tc (tc_roottid tc')) as Hcb_tc'root_getclk.

  forward_if.
  {
    match goal with HH : (Z.of_nat ?a >= Z.of_nat ?b) |- _ => assert (b <= a)%nat as Hle by lia end.
    assert (tc_join tc tc' = tc) as Ejoin by now apply tc_join_trivial.
    forward. 
    unfold treeclock_rep at 1. Exists lclk lnode lstk.
    unfold treeclock_rep at 1. Exists lclk' lnode' lstk'.
    rewrite -> ! Ejoin.
    entailer!.
  }
  match goal with HH : (Z.of_nat (tc_getclk (tc_roottid tc') tc) < _) |- _ => rename HH into Hlt_getclk end.
  rewrite <- Nat2Z.inj_lt in Hlt_getclk.

  forward_call.
  (* retract *)
  pose (vret:=match tc_getnode (tc_roottid tc') tc with None => true | _ => false end).
  replace (node_is_null_as_bool tc (tc_roottid tc')) with vret.
  2:{
    subst vret. unfold node_is_null_as_bool. destruct tc as [(u, ?, ?) [ | ]]; simpl; auto.
    simpl in Hrootid. apply Nat.eqb_neq in Hrootid. now rewrite -> Nat.eqb_sym, -> Hrootid.
  }

  (* before going forward, prepare for the node to be detached and change the representation format *)
  (* FIXME: need to reflect on using pureroot_tc' or tc' as the tcs of tc_detach_nodes ... *)
  pose (pureroot_tc':=Node (tc_rootinfo tc') nil).
  pose (sub:=(match tc_getnode (tc_roottid tc') tc with Some res => res | None => Node (mkInfo (tc_roottid tc') 0%nat 0%nat) nil end)).
  assert (tc_roottid sub = tc_roottid tc') as Eid.
  {
    destruct (tc_getnode (tc_roottid tc') tc) as [ res | ] eqn:Eres; auto.
    now apply tcs_find_has_tid in Eres.
  }
  pose (tc_d:=(fst (tc_detach_nodes (pureroot_tc' :: nil) tc))).
  sep_apply (tc_array2rep_and_bag plclk plnode _ _ _ tc Hlen_lclk Hlen_lnode).
  Intros.
  deadvars.
  freeze (map Z.of_nat (seq 3%nat 5%nat)) Fr.

  (* lightweight postcondition declaration *)
  (* proving forest at the same time may be convenient *)
  match goal with |- context[PROPx _ (LOCALx ?b (SEPx ?c))] =>
    match c with (?preserved :: _) => 
    forward_if (EX z1 z2 z3 : Z, PROPx 
      ((snd (tc_detach_nodes (pureroot_tc' :: nil) tc) = 
        match tc_getnode (tc_roottid tc') tc with Some _ => sub :: nil | None => nil end) :: nil) 
      (LOCALx b (SEPx [preserved; 
      tc_subroot_rep dim plnode plclk sub z1 z2 z3;
      tc_rep_noroot dim plnode plclk sub; 
      tc_rep dim plnode plclk tc_d; 
      unused_bag_rep dim plnode plclk (tc_flatten sub ++ tc_flatten tc_d); 
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tc_roottid tc))), (plclk, (plnode, (plstk, Vint (Int.repr (-1))))))) p])))%assert end end.
  {
    (* (tc_roottid tc') exists in tc *)
    subst vret tc_d.
    destruct (tc_getnode (tc_roottid tc') tc) as [ res | ] eqn:Eres.
    (* TODO why is this not streamlined? *)
    2:{ 
      match goal with HH : context[typed_true] |- _ => rename HH into Htmp end.
      unfold eval_unop in Htmp. simpl in Htmp. now apply typed_true_tint_Vint in Htmp.
    }
    subst sub.
    (* tracing, but not framing *)
    pose proof Eres as Htmp. apply subtc_has_parent in Htmp; auto.
    destruct Htmp as ([ni chn] & (l & Hsub)%subtc_witness_iff & (pre & suf & Echn)%in_split).
    simpl in Echn. subst chn.
    pose proof Hsub as Hsub'%subtc_witness_subtc.
    pose proof Hsub' as Htid_par.
    eapply Foralltc_subtc in Htid_par. 2: apply Htid. simpl in Htid_par.
    (* use single detach *)
    pose proof (tc_detach_nodes_single _ Hnodup res _ _ Hsub (in_pre_suf res)) as Htmp.
    rewrite -> tc_remove_ch_when_nodup in Htmp.
    2: now apply tid_nodup_subtc in Hsub'.
    erewrite -> tc_detach_nodes_tcs_congr with (tcs2:=(pureroot_tc' :: nil)) in Htmp.
    2: intros; subst pureroot_tc'; simpl; rewrite -> Eid; tauto.

    forward_call (dim, Vint (Int.repr (Z.of_nat (tc_roottid tc))), plclk, plnode, plstk, Vint (Int.repr (-1)), p, 
      tc, Node ni (pre ++ res :: suf), l, pre, res, suf).
    1:{ entailer!. simpl. now rewrite Eid. }
    Intros vret. destruct vret as ((z1, z2), z3). Exists z1 z2 z3.
    entailer!. 1: now rewrite Htmp.
    entailer!.
    rewrite -> Htmp. simpl. entailer!.
    (* change bag *)
    erewrite -> unused_bag_rep_perm. 
    1: apply derives_refl.
    apply Permutation_rootinfo2roottid.
    etransitivity. 1: apply tc_detach_nodes_dom_partition.
    rewrite Htmp. simpl. rewrite app_nil_r.
    apply Permutation_map, Permutation_app_comm.
  }
  {
    subst vret.
    destruct (tc_getnode (tc_roottid tc') tc) as [ res | ] eqn:Eres.
    1:{ 
      match goal with HH : context[typed_false] |- _ => rename HH into Htmp end.
      unfold eval_unop in Htmp. simpl in Htmp. now apply typed_false_tint_Vint in Htmp.
    }
    (* use intact *)
    pose proof (tc_detach_nodes_intact (pureroot_tc' :: nil) tc) as Htmp.
    removehead Htmp.
    2:{
      simpl. fold (tc_roottid tc'). intros t Hin [ <- | ]; auto.
      assert (In (tc_roottid tc') (map tc_roottid (tc_flatten tc))) as Hin'
        by (destruct tc; simpl in Hin |- *; tauto).
      now rewrite -> tc_getnode_in_iff, -> Eres in Hin'.
    }
    (* get one from the bag *)
    rewrite -> unused_bag_rep_alloc with (tc:=sub); auto.
    subst sub.
    forward. do 3 Exists default_nodefield.
    unfold tc_subroot_rep, clock_rep, node_rep, default_clockstruct, default_nodestruct.
    entailer!.
    1: rewrite Htmp; simpl; split; try lia; auto.
    simpl.
    subst tc_d. rewrite Htmp. entailer!.
  }

  Intros z1 z2 z3.
  match goal with HH : snd (tc_detach_nodes _ _) = _ |- _ => rename HH into Edetach_snd end.
  thaw Fr. rewrite -> ! Nat2Z.id.
  deadvars. clear vret.
  unfold tc_subroot_rep, clock_rep, clock_payload. rewrite -> ! Eid. Intros.
  forward. forward. forward. 
  rewrite_sem_add_ptr_int.
  (* since the representation format is not array, it is not very easy to read (tc_rootclk tc) ... *)
  unfold tc_rep, tc_root_rep, clock_rep, clock_payload.
  Intros.
  (* TODO this is bad ... *)
  pose proof (tc_detach_nodes_fst_rootinfo_same (pureroot_tc' :: nil) tc) as Htmp.
  pose proof (tc_rootinfo_tid_inj Htmp) as Htmp_tid.
  pose proof (tc_rootinfo_clk_inj Htmp) as Htmp_clk.
  pose proof (tc_rootinfo_aclk_inj Htmp) as Htmp_aclk.
  subst tc_d.
  rewrite Htmp_tid. forward. rewrite Htmp_clk. forward.

  (* we may possibly use the local spec here, but anyway *)
  pose (sub':=Node (mkInfo (tc_roottid tc') (tc_rootclk tc') (tc_rootclk tc)) (tc_rootchn sub)).
  (* have to change clk & aclk of sub before pushing child *)
  freeze (0 :: 1 :: 2 :: 3 :: 4 :: 11 :: nil) Fr.
  forward_call (dim, Vint (Int.repr (Z.of_nat (tc_roottid tc))), plclk, plnode, plstk, Vint (Int.repr (-1)), p, 
    (fst (tc_detach_nodes (pureroot_tc' :: nil) tc)), 
    (fst (tc_detach_nodes (pureroot_tc' :: nil) tc)), sub', @nil nat, z1, z2, z3).
  1:{ entailer!. simpl. now rewrite Htmp_tid. }
  1:{
    subst sub'.
    unfold tc_subroot_rep, tc_rep, tc_root_rep, clock_rep, clock_payload.
    simpl.
    rewrite -> ! Htmp_tid, -> ! Htmp_clk, -> ! Htmp_aclk.
    (* ... *)
    entailer!.
    destruct sub. unfold tc_headch_Z. simpl. entailer!. 
    rewrite <- Eid. simpl. entailer!.
  }

  (* turn to the initial partial join *)
  thaw Fr. 
  cbv delta [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] beta iota.
  deadvars.
  simpl tc_locate_update.
  subst sub'.
  remember (Node _ (_ :: _)) as tc_join0 eqn:E0.
  (* then need to reestablish various things about partial join result ... *)
  assert (~In (tc_roottid tc) (map tc_roottid (tc_flatten pureroot_tc'))) as Hrootid'.
  { subst pureroot_tc'. simpl. intros [ Hc | [] ]. fold (tc_roottid tc') in Hc. congruence. }
  (* TODO extract this? but this seems like a niche case, since there is only one node in pureroot_tc' ... *)
  assert (tc_join_partial tc pureroot_tc' = tc_join0) as E0'.
  {
    subst pureroot_tc' tc_join0.
    unfold tc_join_partial.
    simpl.
    destruct (tc_detach_nodes _ _) as (pivot, forest) eqn:Edetach.
    destruct tc' as [(?, ?, ?) ?], pivot as [(?, ?, ?) ?].
    simpl in *. rewrite -> Edetach_snd.
    f_equal. f_equal. f_equal. 1: congruence.
    destruct (tc_getnode info_tid tc) as [ res | ] eqn:Eres; simpl. 
    2: reflexivity.
    subst sub. apply find_some in Eres. now rewrite -> (proj2 Eres).
  }
  assert (tc_rootinfo tc_join0 = tc_rootinfo tc) as Einfo_join0
    by (rewrite <- E0'; apply tc_join_partial_rootinfo_same).
  (* TODO extract this? but this seems like a niche case, since there is only one node in pureroot_tc' ... *)
  rewrite -> unused_bag_rep_perm with (tcs2:=tc_flatten tc_join0).
  2:{
    destruct (fst (tc_detach_nodes _ _)) as [(i0, ?, ?) ?], sub as [(i1, ?, ?) ?].
    subst tc_join0.
    simpl. rewrite -> ! map_app. simpl.
    replace i1 with (tc_roottid tc') by congruence.
    etransitivity. 
    1: apply Permutation_cons; [ reflexivity | symmetry; apply Permutation_middle ].
    now apply list.Permutation_swap.
  }
  epose proof (tc_get_updated_nodes_join_aux_tc_congr tc_join0 tc 
    (tc_getclk (tc_roottid tc') tc) (tc_rootchn tc') ?[Goalq]) as Egj.
  [Goalq]:{
    (* need to prove that the incoming children do not appear in the partial join *)
    (* TODO extract this? but this seems like a niche case, since there is only one node in pureroot_tc' ... *)
    apply tid_nodup, tid_nodup_Foralltc_id, Foralltc_self in Hshape'.
    apply Forall_forall.
    intros ch Hin_ch.
    rewrite <- E0', -> tc_join_partial_getclk; try assumption.
    all: subst pureroot_tc'; simpl in |- *.
    2: constructor; auto; constructor.
    destruct (eqdec (info_tid (tc_rootinfo tc')) (tc_roottid ch)) as [ Ee | ]; simpl; try reflexivity.
    destruct tc' as [(z', ?, ?) chn_z'].
    simpl in Ee, Hin_ch, Hshape' |- *. subst z'.
    erewrite -> NoDup_cons_iff, -> Permutation_in_mutual in Hshape'.
    2: apply Permutation_map, tc_flatten_root_chn_split.
    exfalso. apply (proj1 Hshape'), in_map, in_app_iff. tauto.
  }
  match type of Egj with map ?ff ?al = map ?ff ?bl => assert (length al = length bl) as Elen
    by (rewrite <- ! map_length with (f:=ff), -> Egj; reflexivity) end.
  (* TODO streamline this? *)
  apply f_equal with (f:=map info_tid) in Egj.
  rewrite -> ! map_map in Egj. 
  rewrite -> 2 map_ext with (f:=(fun x : treeclock => info_tid (tc_rootinfo x))) (g:=tc_roottid) in Egj; auto.

  (* fold *)
  unfold tc_rep. sep_apply tc_rep_and_bag2array.
  1:{
    rewrite <- E0'. apply tc_join_partial_tid_nodup; try assumption.
    constructor; auto; constructor.
  }
  Intros lnode0 lclk0.
  clear dependent lnode.
  clear dependent lclk.
  forward_call (dim, tc_join0, plclk, plnode, plstk, 0%nat, p, 
    Vint (Int.repr (Z.of_nat (tc_roottid tc'))), plclk', plnode', plstk', Vint (Int.repr (-1)), p', 
    tc_getclk (tc_roottid tc') tc, tc_roottid tc', tc_rootchn tc', lclk0, lstk, lclk', lnode').
  1: rewrite <- (tc_rootinfo_tid_inj Einfo_join0); entailer!.
  1:{
    split.
      (* this is interesting. originally I think I have to use tc_join_partial_getclk_in_int_range, 
          but it turns out that the post-condition already gives what I want. 
        is this just coincidence? *)
    1: match goal with HH : Foralltc _ tc_join0 |- _ => eapply Foralltc_impl; [ | apply HH ]; simpl; intros; tauto end.
    split.
    1: now apply Foralltc_chn_selves.
    split.
    1:{ 
      destruct Hprojn1' as (Hroot' & _). 
      apply nth_error_Znth_result in Hroot'. 
      rewrite Hroot'. now simpl.
    }
    split.
    1:{ apply Foralltc_chn_selves. now apply Foralltc_idempotent in Hprojc1'. }
    split.
    1: now apply proj2, Foralltc_self in Hprojn1'.

    simpl. rewrite -> Elen.
    (* play with inequality *)
    (* TODO unify with the approach in the loop? *)
    transitivity (Z.of_nat (length (tc_rootchn tc'))).
    1:{
      pose proof (tc_get_updated_nodes_join_aux_result_submap 
        tc (tc_getclk (tc_roottid tc') tc) (tc_rootchn tc')) as (chn' & Hsl & E).
      rewrite E, map_length. 
      apply list.sublist_length in Hsl.
      lia.
    }
    transitivity (Z.of_nat (tc_size tc')).
    1: pose proof (tc_size_chn_lt_full tc'); lia.
    now apply tc_size_bounded_by_dim.
  }
  (* go back to tc *)
  simpl. rewrite -> ! Elen, -> ! Egj. clear Elen Egj.

  (* now prepare for the loop invariant *)
  deadvars.
  forward_loop
  (EX lstk_pre : list nat, EX lstk_suf : list val, EX pf : (@treeclock nat),
    EX lclk : list (reptype t_struct_clock), EX lnode : list (reptype t_struct_node),
    PROP ( (* seems like we do not need to specify the length? *)
      (* (Zlength lstk_pre + Zlength lstk_suf = dim)%Z; *)
      tc_traversal_snapshot (tc_get_updated_nodes_join tc tc') lstk_pre pf;
      nodearray_emptypart lnode (tc_flatten (tc_join_partial tc pf));
      is_tc_nodearray_proj_full lnode (tc_join_partial tc pf);
      clockarray_emptypart lclk (tc_flatten (tc_join_partial tc pf));
      is_tc_clockarray_proj lclk (tc_join_partial tc pf);
      Zlength lclk = dim;
      Zlength lnode = dim;
      (* this could be useful *)
      Foralltc
        (fun sub : treeclock =>
         Z.of_nat (tc_roottid sub) < dim /\
         Z.of_nat (tc_rootclk sub) <= Int.max_signed /\
         Z.of_nat (tc_rootaclk sub) <= Int.max_signed) (tc_join_partial tc pf); 
      (* interesting enough, this is actually required *)
      ~ In (tc_roottid tc') lstk_pre;
      (* TODO is this free? *)
      ~ In (tc_roottid tc) (map tc_roottid (tc_flatten pf)))
    LOCAL (temp _self p; temp _tc p')
    SEP (data_at Tsh (tarray t_struct_clock dim) lclk' plclk';
      data_at Tsh (tarray t_struct_node dim) lnode' plnode';
      data_at Tsh (tarray tint dim) lstk' plstk';
      data_at Tsh t_struct_treeclock (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tc_roottid tc'))),
        (plclk', (plnode', (plstk', Vint (Int.repr (-1))))))) p';
      data_at Tsh (tarray t_struct_clock dim) lclk plclk;
      data_at Tsh (tarray t_struct_node dim) lnode plnode;
      data_at Tsh (tarray tint dim) (map (fun x : nat => Vint (Int.repr (Z.of_nat x))) lstk_pre ++ lstk_suf) plstk;
      data_at Tsh t_struct_treeclock
        (treeclock_payload dim (Z.of_nat (tc_roottid (tc_join_partial tc pf))) plclk plnode plstk
          (Zlength lstk_pre - 1)) p))%assert.
  1:{ (* enter the loop *)
    do 2 EExists. Exists pureroot_tc' lclk0 lnode0.
    entailer!.
    - rewrite -> E0'. 
      match goal with |- ?A /\ _ /\ _ /\ ?B => enough (A /\ B) by intuition end.
      split.
      + pose proof (tc_traversal_snapshot_init (tc_get_updated_nodes_join tc tc')) as Hini.
        rewrite -> (prefixtc_rootinfo_same (tc_get_updated_nodes_join_is_prefix tc tc')) in Hini.
        subst pureroot_tc'.
        destruct tc'.
        apply Hini.
      + (* TODO streamline this? *)
        pose proof (tc_get_updated_nodes_join_aux_result_submap 
          tc (tc_getclk (tc_roottid tc') tc) (tc_rootchn tc')) as (chn' & Hsl & E).
        rewrite E, in_map_iff.
        intros (? & Eid' & (ch & <- & Hin)%in_map_iff).
        eapply sublist_In in Hin.
        2: apply Hsl.
        rewrite -> (tc_rootinfo_tid_inj (prefixtc_rootinfo_same (tc_get_updated_nodes_join_is_prefix _ _))) in Eid'.
        rewrite -> tc_flatten_direct_result, -> map_cons, -> NoDup_cons_iff in Hnodup'.
        erewrite -> Permutation_in_mutual in Hnodup'.
        2: apply Permutation_map, tc_flatten_root_chn_split.
        rewrite -> map_app, -> in_app_iff in Hnodup'.
        apply Hnodup', or_introl.
        rewrite <- Eid'. apply in_map. assumption.
    - rewrite -> Zlength_map, <- Zlength_correct, -> E0'.
      apply derives_refl.
  }

  Intros lstk_pre lstk_suf pf lclk lnode.
  assert_PROP (Zlength ((map (fun x : nat => Vint (Int.repr (Z.of_nat x))) lstk_pre ++ lstk_suf)) = dim)%Z 
    as Hlensum by entailer!.
  rewrite -> Zlength_app, -> Zlength_map in Hlensum.
  match goal with HH : tc_traversal_snapshot _ _ _ |- _ => rename HH into Htts end.
  unfold treeclock_payload.
  match goal with HH : Foralltc _ (tc_join_partial _ _) |- _ => 
    rewrite Foralltc_and in HH; destruct HH as (Htid_parjoin & Hcb_parjoin) end.
  match goal with HH : ~ In _ lstk_pre |- _ => rename HH into Hnotin_tc' end.

  forward. forward_if.
  2:{ (* end *)
    match goal with HH : Zlength lstk_pre - 1 < 0 |- _ => rename HH into Hl0; rewrite Zlength_correct in Hl0 end.
    destruct lstk_pre; [ | simpl in Hl0; lia ].
    simpl. replace (Zlength _ - 1) with (-1) by list_solve.
    apply tc_traversal_snapshot_inv_stacknil in Htts. 2: reflexivity.
    subst pf.
    (* now we get actual join *)
    assert (tc_join_partial tc (tc_get_updated_nodes_join tc tc') = tc_join tc tc') as Ejoin.
    { rewrite -> tc_join_go; try reflexivity. lia. }
    rewrite -> Ejoin in *.
    forward. entailer!.
    unfold treeclock_rep at 1. Exists lclk lnode lstk_suf.
    unfold treeclock_rep at 1. Exists lclk' lnode' lstk'.
    entailer!.
    unfold tc_roottid.
    rewrite <- Ejoin, -> tc_join_partial_rootinfo_same.
    fold (tc_roottid tc).
    congruence.
  }

  (* cleaning and preparing *)
  clear dependent sub.
  clear dependent pureroot_tc'.
  clear dependent tc_join0.
  clear z1 z2 z3.
  assert (lstk_pre <> nil) as Hnotnil.
  1: intros ->; list_solve.
  match goal with HH : Zlength lstk_pre - 1 >= 0 |- _ => rename HH into Hlen_lstk_pre_ge0 end.
  apply tc_traversal_snapshot_inv_stacknotnil in Htts; try assumption. 
  destruct Htts as (l & sub & Hprefix_sub & Elstk_pre & Epf).
  rewrite -> map_app in Elstk_pre.
  simpl in Elstk_pre.
  assert (tc_roottid sub <> tc_roottid tc') as Hrootid_sub'.
  {
    subst lstk_pre.
    rewrite in_app_iff in Hnotin_tc'. simpl in Hnotin_tc'. tauto.
  }
  (* TODO streamline the following preparation? *)
  (* prepare partial join and pf *)
  epose proof (tc_get_updated_nodes_join_shape tc' Hshape' tc ?[Goalq1] ?[Goalq2]) as (Hpfshape & _).
  [Goalq1]: assumption.
  [Goalq2]: assumption.
  pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix_all.
  pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix_all Hshape') as Hshape_prefix.
  epose proof (tc_vertical_splitr_is_prefix _ _ _) as Hprefix_pf.
  rewrite <- Epf in Hprefix_pf.
  pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix_pf Hshape_prefix) as Hshape_pf.
  epose proof (tc_join_partial_tid_nodup tc pf Hnodup (tid_nodup _ Hshape_pf) ?[Goalq]) as Hnodup_parjoin.
  [Goalq]: assumption.
  pose proof (prefixtc_flatten_info_incl Hprefix_all) as Hprefix_all_info.
  pose proof (eq_refl (tc_join_partial tc pf)) as Eparjoin_unfold.
  unfold tc_join_partial in Eparjoin_unfold at 2.
  epose proof (tc_detach_nodes_fst_rootinfo_same (tc_flatten pf) tc) as Eni_z.
  destruct (tc_detach_nodes (tc_flatten pf) tc) as (pivot, forest) eqn:Edetach.
  destruct pivot as [ ni_z chn_pivot ] eqn:Epivot.
  simpl in Eni_z. subst ni_z.
  pose proof (tc_attach_nodes_rootinfo_same forest pf) as Eni_a.
  destruct (tc_attach_nodes forest pf) as [ni_a chn_a] eqn:Eattach.
  pose proof (prefixtc_rootinfo_same Hprefix_pf) as Erootinfo_pf.
  pose proof (prefixtc_rootinfo_same Hprefix_all) as Erootinfo_prefix.
  rewrite Erootinfo_pf, Erootinfo_prefix in Eni_a.
  simpl in Eni_a. subst ni_a.
  match type of Eparjoin_unfold with _ = ?a =>
    replace a with (Node (tc_rootinfo tc) (Node (mkInfo (tc_roottid tc') (tc_rootclk tc') (tc_rootclk tc)) chn_a :: chn_pivot))
    in Eparjoin_unfold end.
  2: unfold tc_roottid, tc_rootclk; destruct (tc_rootinfo tc'); simpl; reflexivity.
  (* prepare the next prefix *)
  assert (l <> nil) as Hnotnil_l.
  {
    destruct l; auto.
    simpl in Hprefix_sub. injection Hprefix_sub as <-.
    rewrite -> (tc_rootinfo_tid_inj Erootinfo_prefix) in Hrootid_sub'.
    contradiction.
  }
  remember (tc_vertical_splitr false (tc_get_updated_nodes_join tc tc') l) as pfi eqn:Epfi.
  epose proof (tc_vertical_splitr_is_prefix _ _ _) as Hprefix_pfi.
  rewrite <- Epfi in Hprefix_pfi.
  pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix_pfi Hshape_prefix) as Hshape_pfi.
  pose proof (tc_vertical_splitr_forward _ Hnotnil_l _ _ Hprefix_sub) as Htmp.
  rewrite <- ! Epfi, <- Epf in Htmp.
  destruct Htmp as (tc_par_pf & Etc_par_pf & Epfi_alt).
  pose proof (tc_locate_update_prepend_dom _ (Node (tc_rootinfo sub) nil :: nil)
    (tc_rootinfo tc_par_pf) id _ _ Etc_par_pf eq_refl) as Hpfi_dom.
  cbn delta [app] beta iota in Hpfi_dom.
  rewrite ! map_id_eq, <- Epfi_alt in Hpfi_dom. (* not simpl *)
  pose proof Hpfi_dom as Hpfi_tiddom%Permutation_rootinfo2roottid.
  simpl in Hpfi_tiddom.
  (* prepare bound and lt conditions *)
  assert (In (tc_rootinfo sub) (map tc_rootinfo (tc_flatten tc'))) as (subo & Esub_info & Hsubo)%in_map_iff
    by (eapply Hprefix_all_info, in_map, subtc_witness_iff; eauto).
  pose proof Hsubo as Hsub_tid.
  eapply Foralltc_subtc in Hsub_tid. 2: apply Htid'.
  pose proof Hsubo as Hcb_sub_clk.
  eapply Foralltc_subtc in Hcb_sub_clk. 2: apply Hcb_tc'.
  (* TODO on plclk'? *)
  pose proof Hsubo as Es_sub_clk.
  eapply Foralltc_subtc in Es_sub_clk. 2: apply Hca_tc'.
  pose proof Hprefix_sub as Hlt_sub_getclk%subtc_witness_subtc.
  eapply Foralltc_subtc in Hlt_sub_getclk. 2: apply Hpfshape.
  simpl in Hsub_tid, Hcb_sub_clk, Es_sub_clk, Hlt_sub_getclk. 
  unfold tc_roottid, tc_rootclk, tc_rootaclk in Hsub_tid, Hcb_sub_clk, Es_sub_clk.
  rewrite -> Esub_info in Hsub_tid, Hcb_sub_clk, Es_sub_clk.
  fold (tc_roottid sub) (tc_rootclk sub) (tc_rootaclk sub) in Hsub_tid, Hcb_sub_clk, Es_sub_clk.
  destruct Hcb_sub_clk as (Hcb_sub_clk & Hcb_sub_aclk).
  (* FIXME: extract this out? *)
  assert (tc_roottid sub <> tc_roottid tc) as Hrootid_sub.
  {
    unfold tc_getclk in Hlt_sub_getclk. intros EE. rewrite EE, tc_getnode_self in Hlt_sub_getclk. 
    assert (tc_getclk (tc_roottid tc) tc' = tc_rootclk sub).
    {
      rewrite <- EE, <- (tc_rootinfo_tid_inj Esub_info), tc_getclk_viewchange, tid_nodup_find_self_sub; try assumption.
      now apply tc_rootinfo_clk_inj.
    }
    lia.
  }
  clear dependent subo.
  assert (~ In (tc_roottid tc) (map tc_roottid (tc_flatten pfi))) as Hnotin_tc.
  {
    erewrite Permutation_in_mutual. 2: apply Hpfi_tiddom.
    fold (tc_roottid sub).
    simpl. tauto.
  } 
  assert (~ In (tc_roottid sub) (map tc_roottid (tc_flatten pf))) as Hnotin.
  {
    eapply tid_nodup, Permutation_NoDup in Hshape_pfi.
    2: apply Hpfi_tiddom.
    simpl in Hshape_pfi.
    apply NoDup_cons_iff in Hshape_pfi. tauto.
  }
  (* also need to restore the value of (tc_getclk (tc_roottid sub) tc) *)
  (* FIXME: consider this "if and only if" reasoning? *)
  assert (base.fmap tc_rootinfo_partial (tc_getnode (tc_roottid sub) tc) = 
    base.fmap tc_rootinfo_partial (tc_getnode (tc_roottid sub) (tc_join_partial tc pf))) as Egetsub.
  {
    destruct (tc_getnode (tc_roottid sub) (tc_join_partial tc pf)) as [ res | ] eqn:Eres; simpl.
    - apply tcs_find_has_tid in Eres.
      destruct Eres as (Hres%(in_map tc_rootinfo_partial) & Eid).
      eapply Permutation_in in Hres.
      2: apply tc_join_partial_dom_partial_info'; try assumption.
      2: subst; now apply tid_nodup.
      rewrite -> in_app_iff in Hres. destruct Hres as [ Hres | Hres ].
      + rewrite -> in_map_iff in Hres.
        destruct Hres as (res' & Epinfo & Hres'%filter_In%proj1).
        now rewrite <- Eid, <- (tc_partialinfo_tid_inj Epinfo), <- Epinfo, -> tid_nodup_find_self_sub.
      + rewrite -> in_map_iff in Hres.
        destruct Hres as (res' & Epinfo & Hres'%(in_map tc_roottid)).
        pose proof (tc_partialinfo_tid_inj Epinfo).
        congruence.
    - destruct (tc_getnode (tc_roottid sub) tc) as [ res' | ] eqn:Eres'; simpl.
      2: reflexivity.
      apply tcs_find_has_tid in Eres'.
      destruct Eres' as (Hres' & Eid).
      match type of Eres with ?r = _ => assert (~ (Datatypes.is_true (ssrbool.isSome r))) as Eres_ by now rewrite Eres end.
      rewrite <- tc_getnode_in_iff in Eres_.
      exfalso. apply Eres_.
      (* TODO start to repeat! *)
      epose proof (tc_join_partial_dom_partial_info' _ _ Hnodup (tid_nodup _ Hshape_pf) ?[Goalq]) as Htmp.
      [Goalq]: assumption.
      rewrite <- map_app in Htmp.
      eapply Permutation_in.
      1: symmetry; apply Permutation_partialinfo2roottid, Htmp.
      rewrite -> map_app, -> in_app_iff. left.
      apply in_map_iff. exists res'. split; try assumption.
      apply filter_In. split; try assumption.
      rewrite Eid. rewrite -> tcs_find_in_iff in Hnotin. 
      unfold Datatypes.is_true in Hnotin.
      now apply eq_true_not_negb.
  }

  (* read stack top *)
  forward. forward. forward. 
  rewrite sub_repr.
  (* TODO make some contextual rewriting? *)
  match goal with |- context[map ?ff lstk_pre] => rewrite -> (f_equal (map ff) Elstk_pre), -> ! map_app end.
  simpl map.
  rewrite <- app_cons_assoc.
  match type of Elstk_pre with _ = ?ll ++ _ => 
    assert (Zlength (map (fun x : nat => Vint (Int.repr (Z.of_nat x))) ll) = Zlength lstk_pre - 1) 
    as Hlen_lstk_pre_pre by list_solve end.
  rewrite <- Hlen_lstk_pre_pre at 1.
  forward.
  1: entailer!.
  1:{
    rewrite -> sublist.Znth_app1; auto. 
    entailer!.
  }
  rewrite -> sublist.Znth_app1; auto.
  deadvars. clear Hlen_lstk_pre_pre.

  (* from now on, mainly repeating the procedure above *)
  forward. forward. forward. forward. forward. forward.
  deadvars.
  rewrite_sem_add_ptr_int.
  array_focus (Z.of_nat (tc_roottid sub)) plclk witheqn Etmp.
  rewrite -> Etmp.
  assert (0 <= Z.of_nat (tc_roottid sub) < Zlength lclk) as Eclk by (split; lia; congruence).
  apply clockarray_proj_tc_getinfo with (tc:=tc_join_partial tc pf) in Eclk; try assumption.
  rewrite -> Nat2Z.id in Eclk.
  replace (tc_getclk (tc_roottid sub) _) with (tc_getclk (tc_roottid sub) tc) in Eclk.
  2:{
    (* TODO ... *)
    rewrite -> ! tc_getclk_viewchange.
    destruct (tc_getnode (tc_roottid sub) tc) as [[(?, ?, ?) ?] | ], 
      (tc_getnode (tc_roottid sub) (tc_join_partial tc pf)) as [[(?, ?, ?) ?] | ]; simpl in Egetsub |- *; congruence.
  }
  read_clock' witheqn Eclk. clear Eclk.
  array_unfocus witheqn Etmp.

  forward_call.
  1: unfold tc_roottid; rewrite -> tc_join_partial_rootinfo_same; fold (tc_roottid tc); lia.
  (* retract *)
  (* write tc_getnode (tc_roottid sub) (tc_join_partial tc pf) here to align with the code *)
  pose (vret:=match tc_getnode (tc_roottid sub) (tc_join_partial tc pf) with None => true | _ => false end).
  replace (node_is_null_as_bool (tc_join_partial tc pf) (tc_roottid sub)) with vret.
  2:{
    subst vret. unfold node_is_null_as_bool.
    destruct (tc_getnode (tc_roottid sub) (tc_join_partial tc pf)) as [? | ]; simpl in Egetsub |- *; try congruence.
    2: now rewrite orb_true_r.
    (*
    destruct (tc_getnode (tc_roottid sub) tc) as [? | ], 
      (tc_getnode (tc_roottid sub) (tc_join_partial tc pf)) as [? | ]; simpl in Egetsub |- *; try congruence.
    2: now rewrite orb_true_r.
    *)
    destruct (tc_join_partial tc pf) as [(uu, ?, ?) [ | ]] eqn:EE; auto.
    apply f_equal with (f:=tc_rootinfo) in EE.
    rewrite -> tc_join_partial_rootinfo_same in EE. 
    simpl in Hrootid_sub, EE. apply Nat.eqb_neq in Hrootid_sub. 
    unfold tc_roottid in Hrootid_sub at 2. rewrite -> EE in Hrootid_sub. 
    simpl in Hrootid_sub. now rewrite Hrootid_sub.
  }

  (* before going forward, prepare for the node to be detached and change the representation format *)
  pose (subi:=(match tc_getnode (tc_roottid sub) (tc_join_partial tc pf) with Some res => res | None => Node (mkInfo (tc_roottid sub) 0%nat 0%nat) nil end)).
  assert (tc_roottid subi = tc_roottid sub) as Eid.
  {
    destruct (tc_getnode (tc_roottid sub) (tc_join_partial tc pf)) as [ res | ] eqn:Eres; auto.
    now apply tcs_find_has_tid in Eres.
  }
  pose (tc_d:=(fst (tc_detach_nodes (sub :: nil) (tc_join_partial tc pf)))).
  sep_apply (tc_array2rep_and_bag plclk plnode lclk lnode dim (tc_join_partial tc pf)).
  Intros.
  freeze (map Z.of_nat (seq 3%nat 5%nat)) Fr.

  (* lightweight postcondition declaration *)
  (* proving forest at the same time may be convenient *)
  match goal with |- context[PROPx _ (LOCALx ?b (SEPx ?c))] =>
    match c with (?preserved :: _) => 
    forward_if (EX z1 z2 z3 : Z, PROPx 
      ((snd (tc_detach_nodes (sub :: nil) (tc_join_partial tc pf)) = 
        match tc_getnode (tc_roottid sub) (tc_join_partial tc pf) with Some _ => subi :: nil | None => nil end) :: nil) 
      (LOCALx b (SEPx [preserved; 
      tc_subroot_rep dim plnode plclk subi z1 z2 z3;
      tc_rep_noroot dim plnode plclk subi; 
      tc_rep dim plnode plclk tc_d; 
      unused_bag_rep dim plnode plclk (tc_flatten subi ++ tc_flatten tc_d); 
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tc_roottid (tc_join_partial tc pf)))), 
          (plclk, (plnode, (plstk, Vint (Int.repr (Zlength lstk_pre - 1 - 1))))))) p])))%assert end end.
  {
    (* (tc_roottid sub) exists in tc *)
    subst vret tc_d.
    destruct (tc_getnode (tc_roottid sub) (tc_join_partial tc pf)) as [ res | ] eqn:Eres.
    2:{ 
      match goal with HH : context[typed_true] |- _ => rename HH into Htmp end.
      unfold eval_unop in Htmp. simpl in Htmp. now apply typed_true_tint_Vint in Htmp.
    }
    subst subi.
    (* tracing, but not framing *)
    pose proof Eres as Htmp. apply subtc_has_parent in Htmp; auto.
    2: now rewrite -> Eparjoin_unfold.
    destruct Htmp as ([ni chn] & (lres & Hsub)%subtc_witness_iff & (pre & suf & Echn)%in_split).
    simpl in Echn. subst chn.
    pose proof Hsub as Hsub'%subtc_witness_subtc.
    pose proof Hsub' as Htid_par.
    eapply Foralltc_subtc in Htid_par. 2: apply Htid_parjoin. simpl in Htid_par.
    (* use single detach *)
    pose proof (tc_detach_nodes_single _ Hnodup_parjoin res _ _ Hsub (in_pre_suf res)) as Htmp.
    rewrite -> tc_remove_ch_when_nodup in Htmp.
    2: now apply tid_nodup_subtc in Hsub'.
    erewrite -> tc_detach_nodes_tcs_congr with (tcs2:=(sub :: nil)) in Htmp.
    2: intros; simpl; rewrite -> Eid; tauto.

    forward_call (dim, Vint (Int.repr (Z.of_nat (tc_roottid (tc_join_partial tc pf)))), plclk, plnode, plstk, 
      Vint (Int.repr (Zlength lstk_pre - 1 - 1)), p, tc_join_partial tc pf, Node ni (pre ++ res :: suf), lres, pre, res, suf).
    1:{ entailer!. simpl. now rewrite Eid. }
    Intros vret. destruct vret as ((z1, z2), z3). Exists z1 z2 z3.
    entailer!. 1: now rewrite Htmp.
    entailer!.
    rewrite -> Htmp. simpl. entailer!.
    (* change bag *)
    erewrite -> unused_bag_rep_perm. 
    1: apply derives_refl.
    apply Permutation_rootinfo2roottid.
    etransitivity. 1: apply tc_detach_nodes_dom_partition.
    rewrite Htmp. simpl. rewrite app_nil_r.
    apply Permutation_map, Permutation_app_comm.
  }
  {
    subst vret.
    destruct (tc_getnode (tc_roottid sub) (tc_join_partial tc pf)) as [ res | ] eqn:Eres.
    1:{ 
      match goal with HH : context[typed_false] |- _ => rename HH into Htmp end.
      unfold eval_unop in Htmp. simpl in Htmp. now apply typed_false_tint_Vint in Htmp.
    }
    (* use intact *)
    pose proof (tc_detach_nodes_intact (sub :: nil) (tc_join_partial tc pf)) as Htmp.
    removehead Htmp.
    2:{
      simpl. intros t Hin [ <- | ]; auto.
      assert (In (tc_roottid sub) (map tc_roottid (tc_flatten (tc_join_partial tc pf)))) as Hin'
        by (rewrite tc_flatten_direct_result; simpl; right; assumption).
      now rewrite -> tc_getnode_in_iff, -> Eres in Hin'.
    }
    (* get one from the bag *)
    rewrite -> unused_bag_rep_alloc with (tc:=subi); auto.
    subst subi.
    forward. do 3 Exists default_nodefield.
    unfold tc_subroot_rep, clock_rep, node_rep, default_clockstruct, default_nodestruct.
    entailer!.
    1: rewrite Htmp; simpl; split; try lia; auto.
    simpl.
    subst tc_d. rewrite Htmp. entailer!.
  }

  Intros z1 z2 z3.
  match goal with HH : snd (tc_detach_nodes _ _) = _ |- _ => rename HH into Edetach_snd end.
  (* use single detach prepend child *)
  epose proof (tc_detach_nodes_prepend_child (tc_rootinfo tc) (Node (mkInfo (tc_roottid tc') (tc_rootclk tc') (tc_rootclk tc)) chn_a) 
    chn_pivot (sub :: nil) ?[Goalq]) as Edetach0.
  [Goalq]:{
    simpl. unfold has_same_tid. now destruct (eqdec (tc_roottid sub) (tc_roottid tc')).
  }
  rewrite <- Epivot, <- Eparjoin_unfold in Edetach0.
  pose proof (tc_detach_nodes_fst_rootinfo_same (sub :: nil) pivot) as Htmp.
  destruct (tc_detach_nodes (sub :: nil) pivot) as (pivot_main, forest_main) eqn:Edetach_main.
  destruct pivot_main as [ni_main chn_pivot_main] eqn:Epivot_main.
  simpl in Htmp. rewrite -> Epivot in Htmp. simpl in Htmp. subst ni_main.
  (* TODO ad hoc replacement *)
  pose proof (tc_detach_nodes_fst_rootinfo_same (sub :: nil) (tc_attach_nodes forest pf)) as Htmp.
  destruct (tc_detach_nodes (sub :: nil) (tc_attach_nodes forest pf)) as (pivot_a, forest_a) eqn:Edetach_a.
  destruct pivot_a as [ni_pivot_a chn_pivot_a] eqn:Epivot_a.
  simpl in Htmp. rewrite -> Eattach in Htmp. simpl in Htmp. subst ni_pivot_a.
  assert (tc_detach_nodes (sub :: nil) (Node (mkInfo (tc_roottid tc') (tc_rootclk tc') (tc_rootclk tc)) chn_a) =
    (Node (mkInfo (tc_roottid tc') (tc_rootclk tc') (tc_rootclk tc)) chn_pivot_a, forest_a)) as Edetach_a_tmp.
  {
    rewrite -> Eattach in Edetach_a.
    simpl in Edetach_a |- *.
    destruct (List.split _) eqn:?, (partition _ _) eqn:EEE in |- *.
    rewrite -> EEE in Edetach_a.
    destruct pivot_a. simpl. congruence.
  }
  rewrite Edetach_a_tmp in Edetach0. clear Edetach_a_tmp.
  rewrite Edetach0 in Edetach_snd.
  simpl in Edetach_snd.
  (* distribute the single detach on attach result *)
  epose proof (tc_detach_attach_distr1_fst pf forest sub ?[Goalq]) as Etmp1.
  [Goalq]: assumption.
  epose proof (tc_detach_attach_distr1_snd' pf forest sub ?[Goalq1] ?[Goalq2] ?[Goalq3] (tid_nodup _ Hshape_pf)) as Etmp2.
  [Goalq1]: assumption.
  [Goalq2]:{
    epose proof (tc_detach_nodes_dom_incl _ _) as Htmpincl.
    rewrite Edetach in Htmpincl. simpl in Htmpincl.
    eapply Forall_impl. 2: apply Htmpincl.
    simpl. intros ?. now rewrite tcs_find_in_iff.
  }
  [Goalq3]:{
    (* TODO lift this? *)
    epose proof (tc_detach_nodes_tid_nodup _ _ Hnodup) as Hnodup_forest.
    rewrite Edetach in Hnodup_forest.
    now apply proj1, tid_nodup_root_chn_split, proj1 in Hnodup_forest.
  }
  rewrite -> Edetach_a in Etmp1, Etmp2.
  simpl in Etmp1, Etmp2.
  (* now consider the partial join we are going to build in this iteration *)
  pose proof (tc_detach_nodes_tcs_app_fst (tc_flatten pf) (sub :: nil) tc) as Htmp1fst.
  pose proof (tc_detach_nodes_tcs_app_snd (tc_flatten pf) (sub :: nil) tc) as Htmp1snd.
  rewrite -> Edetach, <- ! Epivot in Htmp1fst, Htmp1snd.
  cbn delta [fst snd] beta iota in Htmp1fst, Htmp1snd.
  rewrite -> Edetach_main in Htmp1fst, Htmp1snd.
  cbn delta [fst snd] beta iota in Htmp1fst, Htmp1snd.
  pose proof (eq_refl (tc_join_partial tc pfi)) as Eparjoin0_unfold.
  unfold tc_join_partial in Eparjoin0_unfold at 2.
  rewrite -> Epfi in Eparjoin0_unfold at 2.
  epose proof (tc_detach_nodes_tcs_congr (tc_flatten pf ++ (sub :: nil)) (tc_flatten pfi) ?[Goalq]) as Edetach_cong.
  [Goalq]:{
    apply Permutation_in_mutual.
    rewrite Hpfi_tiddom, map_app, Permutation_app_comm.
    simpl. reflexivity.
  }
  rewrite <- Epfi, <- Edetach_cong in Eparjoin0_unfold. 
  destruct (tc_detach_nodes (tc_flatten pf ++ [sub]) tc) as (pivot1, forest1) eqn:Edetach1.
  simpl in Htmp1fst, Htmp1snd.
  subst pivot1.
  pose proof (tc_attach_nodes_rootinfo_same forest1 pfi) as Eni_a1.
  destruct (tc_attach_nodes forest1 pfi) as [ni_a1 chn_a1] eqn:Eattach1.
  pose proof (prefixtc_rootinfo_same Hprefix_pfi) as Erootinfo_pfi.
  rewrite Erootinfo_pfi, Erootinfo_prefix in Eni_a1.
  simpl in Eni_a1. subst ni_a1.
  (* TODO ad hoc replacement *)
  assert (tc_rootinfo tc' = mkInfo (tc_roottid tc') (tc_rootclk tc') (tc_rootaclk tc')) as Htmp
    by (destruct tc' as [(?, ?, ?) ?]; now simpl).
  rewrite -> Htmp in Eparjoin0_unfold. clear Htmp.
  fold (tc_rootclk tc) in Eparjoin0_unfold.
  rewrite <- Etmp2, <- Permutation_app_rot, -> app_assoc, -> Edetach_snd in Htmp1snd.
  match type of Htmp1snd with _ _ ?bl => rewrite -> tc_attach_nodes_forest_congr with (forest2:=bl) in Eattach1 end.
  2:{
    (* FIXME: extract this out? *)
    (* TODO lift this? *)
    epose proof (tc_detach_nodes_tid_nodup _ _ Hnodup) as Hnodup_forest1.
    rewrite Edetach1 in Hnodup_forest1.
    simpl in Hnodup_forest1.
    apply proj1, tid_nodup_root_chn_split, proj1 in Hnodup_forest1.
    pose proof Hnodup_forest1 as Hnodup_forest2%(Permutation_NoDup (Permutation_map tc_roottid Htmp1snd)).
    (* trivial! *)
    apply Foralltc_trivial.
    intros tc0.
    pose proof (tid_nodup_find_self _ Hnodup_forest2) as Htmp2.
    rewrite -> Forall_forall in Htmp2.
    match goal with |- ?ra = _ => destruct ra as [ res1 | ] eqn:Eres1 end.
    - apply find_some in Eres1. rewrite has_same_tid_true in Eres1.
      destruct Eres1 as (Hres1 & Eid1).
      eapply Permutation_in in Hres1. 2: apply Htmp1snd.
      apply Htmp2 in Hres1.
      rewrite Eid1, Hres1. reflexivity.
    - match goal with |- _ = ?rb => destruct rb as [ res2 | ] eqn:Eres2 end.
      2: reflexivity.
      apply find_some in Eres2. rewrite has_same_tid_true in Eres2.
      destruct Eres2 as (Hres2 & Eid2).
      eapply Permutation_in in Hres2. 2: symmetry; apply Htmp1snd.
      eapply find_none in Eres1. 2: apply Hres2.
      rewrite -> has_same_tid_false in Eres1. contradiction.
  }

  (* update clk and aclk *)
  thaw Fr. rewrite -> ! Nat2Z.id.
  deadvars. clear vret.
  unfold tc_subroot_rep, clock_rep, clock_payload. rewrite -> ! Eid. Intros.
  array_focus (Z.of_nat (tc_roottid sub)) plclk' witheqn Etmp.
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

  (* relate single attach with current situation *)
  match type of Eattach1 with tc_attach_nodes (?al ++ _) _ = _ =>
    epose proof (tc_attach_nodes_single pf (map fst (map (tc_detach_nodes [sub]) forest)) 
      (Node (tc_rootinfo sub) (tc_rootchn subi)) ?[Goalq1] ?[Goalq2] 
        al ?[Goalq3] _ _ Etc_par_pf) as (tc_par' & Etc_par' & _ & Eattach1_alt) end.
  [Goalq1]:{
    (* ... *)
    simpl. fold (tc_roottid sub).
    destruct (find _ _) as [ res | ] eqn:Eres in |- *.
    2: reflexivity.
    apply find_some in Eres. 
    rewrite map_map, has_same_tid_true in Eres.
    destruct Eres as (Hin%(in_map tc_roottid) & Eidtmp).
    erewrite -> map_map, map_ext in Hin.
    2: intros tc0; unfold tc_roottid; rewrite tc_detach_nodes_fst_rootinfo_same; fold (tc_roottid tc0); reflexivity.
    rewrite in_map_iff in Hin.
    destruct Hin as (tc0 & Eidtmp2 & Hin).
    (* TODO this appeared somewhere above; check this tactic below *)
    epose proof (tc_detach_nodes_dom_incl _ _) as Htmpincl.
    rewrite Edetach, Forall_forall in Htmpincl. simpl in Htmpincl.
    specialize (Htmpincl _ Hin).
    rewrite <- tcs_find_in_iff in Htmpincl.
    congruence.
  }
  [Goalq2]: assumption.
  [Goalq3]:{
    destruct (tc_getnode _ _) as [ res | ] eqn:Eres in |- *; subst subi; rewrite Eres.
    - simpl. split; auto. apply tcs_find_has_tid in Eres. apply Eres.
    - reflexivity.
  }
  simpl in Eattach1_alt.
  rewrite <- Epfi_alt, -> Eattach1 in Eattach1_alt.

  (* read par *)
  epose proof (tc_vertical_splitr_locate _ _ _ _ Hprefix_sub) as E_loc_pfi_sub.
  rewrite <- Epfi in E_loc_pfi_sub.
  simpl in E_loc_pfi_sub.
  pose proof (is_tc_nodearray_proj_onlypar_derived _ _ (proj2 Hprojn1')) as Hop_d.
  pose proof (is_tc_nodearray_proj_onlypar_prefix_preserve _ _ _ Hprefix_all Hop_d) as Hop_prefix.
  pose proof (is_tc_nodearray_proj_onlypar_prefix_preserve _ _ _ Hprefix_pfi Hop_prefix) as Hop_pfi.
  epose proof (is_tc_nodearray_proj_onlypar_read_parent lnode' _ Hop_pfi _ ?[Goalqa] _ E_loc_pfi_sub) as Hreadpar.
  [Goalqa]: destruct l; simpl; auto; try contradiction.
  (* --> tc_par_pf *)
  replace (removelast _) with (repeat 0%nat (Datatypes.length l - 1)) in Hreadpar.
  2:{
    replace (length l)%nat with ((length l - 1) + 1)%nat at 2.
    2: destruct l; try contradiction; simpl; lia.
    rewrite List.repeat_app. simpl. rewrite removelast_last. reflexivity.
  }
  rewrite Epfi_alt in Hreadpar.
  epose proof (tc_locate_update_pos_app _ _ nil _ _ Etc_par_pf) as Htmp. (* TODO have to use this? *)
  rewrite -> app_nil_r, <- Epfi_alt in Htmp.
  simpl in Htmp.
  rewrite <- Epfi_alt, -> Htmp in Hreadpar.
  simpl in Hreadpar. injection Hreadpar as Hreadpar.
  clear Htmp.
  (* --> tc_par', with colocate *)
  pose proof (tc_attach_nodes_colocate (map fst (map (tc_detach_nodes [sub]) forest)) pf _ _ Etc_par_pf) as Eparpar.
  rewrite Etc_par' in Eparpar. 
  simpl in Eparpar. injection Eparpar as Eparpar.
  rewrite <- Eparpar in Hreadpar.
  fold (tc_roottid sub) in Hreadpar.
  fold (tc_roottid tc_par') in Hreadpar.
  (* range guarantee ... TODO tedious? *)
  assert (Z.of_nat (tc_roottid tc_par') < dim) as Htc_par'_tid.
  {
    eapply subtc_witness_subtc, in_map with (f:=tc_rootinfo), prefixtc_flatten_info_incl in Etc_par_pf.
    2: apply Hprefix_pf.
    apply Hprefix_all_info in Etc_par_pf.
    rewrite in_map_iff in Etc_par_pf.
    destruct Etc_par_pf as (subtmp & Etmp & Hin).
    eapply Foralltc_subtc in Hin. 2: apply Htid'.
    simpl in Hin.
    unfold tc_roottid. rewrite -> Eparpar, <- Etmp. exact Hin.
  }
  (* real reading *)
  array_focus (Z.of_nat (tc_roottid sub)) plnode' witheqn Etmp.
  rewrite Etmp.
  destruct (Znth (Z.of_nat (tc_roottid sub)) lnode') as (zz1, (zz2, (zz3, zz4))) eqn:Es.
  simpl in zz1, zz2, zz3, zz4, Es, Hreadpar.
  subst zz3.
  forward.
  array_unfocus witheqn Etmp.
  deadvars.

  (* depict the final situation *)
  pose (ni_targ:=(match (length l - 1)%nat with O => mkInfo (tc_roottid tc') (tc_rootclk tc') (tc_rootclk tc)
    | S _ => tc_rootinfo tc_par' end)).
  (* TODO is Efinal1 useful? *)
  assert (info_tid ni_targ = tc_roottid tc_par' /\
    tc_locate tc_d (repeat 0%nat (length l)) = Some (Node ni_targ (tc_rootchn tc_par')) /\
    tc_locate_update tc_d (repeat 0%nat (length l))
      (Node ni_targ (Node (tc_rootinfo sub) (tc_rootchn subi) :: tc_rootchn tc_par')) = 
    tc_join_partial tc pfi) as (Erootinfo_targ & Efinal1 & Efinal2).
  {
    subst tc_d ni_targ.
    rewrite <- Etmp1 in Eattach1_alt, Etc_par'. (* TODO where to put this tactic? *)
    rewrite Edetach0, Eparjoin0_unfold. simpl.
    destruct l as [ | x l' ]; try contradiction.
    simpl. rewrite -> Nat.sub_0_r.
    destruct (list_ifnil_destruct l') as [ -> | Hnotnil_l' ].
    - simpl in Eattach1_alt, Etc_par' |- *. rewrite -> upd_Znth0.
      split. 1: destruct tc_par'; simpl in *; unfold tc_roottid; congruence.
      split; try congruence.
      do 2 f_equal. destruct tc_par'. injection Etc_par' as <-. simpl. assumption.
    - assert (exists n', length l' = S n') as (n' & Hlen') by (destruct l'; try contradiction; simpl; eauto).
      simpl in Eattach1_alt, Etc_par'. rewrite -> Nat.sub_0_r, Hlen' in Eattach1_alt, Etc_par'.
      rewrite Hlen', upd_Znth0.
      split; try reflexivity.
      simpl in Eattach1_alt, Etc_par' |- *.
      destruct chn_pivot_a; split; try congruence.
      now destruct tc_par'.
  }

  (* go push child *)
  freeze (0 :: 1 :: 2 :: 3 :: 4 :: 9 :: nil) Fr.
  forward_call (dim, Vint (Int.repr (Z.of_nat (tc_roottid (tc_join_partial tc pf)))), plclk, plnode, plstk, Vint (Int.repr (Zlength lstk_pre - 1 - 1)), p, 
    tc_d, Node ni_targ (tc_rootchn tc_par'), Node (tc_rootinfo sub) (tc_rootchn subi), (repeat 0%nat (Datatypes.length l)), z1, z2, z3).
  1:{ entailer!. simpl. now rewrite Erootinfo_targ. }
  1:{
    unfold tc_subroot_rep, clock_rep, clock_payload.
    simpl.
    fold (tc_roottid sub). fold (tc_rootclk sub). fold (tc_rootaclk sub).
    destruct subi.
    simpl. simpl in Eid. rewrite Eid.
    unfold tc_headch_Z. simpl.
    entailer!.
  }
  1:{ simpl. rewrite Erootinfo_targ. assumption. }
  cbn delta [tc_rootinfo tc_rootchn] beta iota.
  rewrite -> Efinal2.
  thaw Fr.
  cbv delta [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] beta iota.
  deadvars.
  rewrite -> unused_bag_rep_perm with (tcs2:=tc_flatten (tc_join_partial tc pfi)).
  2:{
    pose proof (tc_locate_update_prepend_dom _ (Node (tc_rootinfo sub) (tc_rootchn subi) :: nil)
      ni_targ info_tid _ _ Efinal1 eq_refl) as Htmp.
    simpl in Htmp.
    rewrite app_nil_r in Htmp.
    simpl in Htmp.
    rewrite Efinal2 in Htmp.
    (* TODO streamline this *)
    fold (tc_roottid sub) in Htmp. rewrite <- Eid in Htmp.
    rewrite ! map_map in Htmp.
    rewrite -> 2 map_ext with (f:=(fun x : treeclock => info_tid (tc_rootinfo x))) (g:=tc_roottid) in Htmp; auto.
    rewrite Htmp, ! map_app, tc_flatten_direct_result with (tc:=subi).
    simpl. reflexivity.
  }

  (* fold *)
  unfold tc_rep. sep_apply tc_rep_and_bag2array.
  1:{
    apply tc_join_partial_tid_nodup; try assumption.
    now apply tid_nodup.
  }
  Intros lnode1 lclk1.
  clear dependent lnode.
  clear dependent lclk.

  (* trace back to the original tree *)
  pose proof (tc_get_updated_nodes_join_trace _ _ _ (subtc_witness_subtc _ _ _ Hprefix_sub)) 
    as (sub' & Hsub' & Esub).
  pose proof (prefixtc_rootinfo_same (tc_get_updated_nodes_join_is_prefix tc sub')) as Erooinfo_sub'.
  rewrite <- Esub in Erooinfo_sub'.
  (* some tricky things *)
  pose proof (tc_vertical_splitr_tofull _ _ _ Hprefix_sub) as Epff.
  epose proof (tc_vertical_splitr_is_prefix _ _ _) as Hprefix_pff.
  rewrite -> Epff, <- Epfi in Hprefix_pff.
  pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix_pff Hshape_prefix) as Hshape_pff.
  pose proof (tc_locate_update_prepend_dom _ (tc_rootchn sub) (tc_rootinfo sub) id _ _ 
    E_loc_pfi_sub eq_refl) as Htmp.
  rewrite ! map_id_eq, app_nil_r in Htmp.
  eapply tid_nodup, Permutation_NoDup in Hshape_pff.
  2: etransitivity; [ | apply Permutation_rootinfo2roottid, Htmp ]; now destruct sub.
  clear Htmp.
  (* TODO this proof about congr seemes to be repeating *)
  epose proof (tc_get_updated_nodes_join_aux_tc_congr (tc_join_partial tc pfi) tc 
    (tc_getclk (tc_roottid sub) tc) (tc_rootchn sub') ?[Goalqa]) as Egj.
  [Goalqa]:{
    (* TODO tedious! *)
    apply Forall_forall.
    intros ch Hin_ch.
    pose proof (subtc_trans _ _ _ (subtc_chn _ _ Hin_ch) Hsub') as Hsub_ch.

    (* route 1: get lt *)
    rewrite tc_join_partial_getclk; auto.
    2: apply tid_nodup; assumption.
    destruct (tc_getnode (tc_roottid ch) pfi) as [ res | ] eqn:Eres; auto.
    pose proof Eres as Eres_.
    apply tcs_find_has_tid in Eres.
    destruct Eres as (Eres & Eid_ch).
    pose proof Eres as Eres_info%(in_map tc_rootinfo).
    pose proof (prefixtc_flatten_info_incl Hprefix_pfi) as Hprefix_pfi_info.
    apply Hprefix_pfi_info, in_map_iff in Eres_info.
    destruct Eres_info as (res' & Einfo & Hin).
    pose proof Hin as Hin'. 
    eapply Foralltc_subtc in Hin'. 2: apply Hpfshape. simpl in Hin'.
    rewrite -> (tc_rootinfo_tid_inj Einfo), -> (tc_rootinfo_clk_inj Einfo) in Hin'.

    (* route 2: unify tc_rootinfo res with tc_rootinfo ch *)
    pose proof (tid_nodup_find_self_sub tc_rootinfo tc' (tid_nodup _ Hshape')) as Hself.
    pose proof Hself as Hself1.
    specialize (Hself1 _ Hsub_ch).
    apply in_map with (f:=tc_rootinfo), Hprefix_all_info, in_map_iff in Hin.
    destruct Hin as (res'' & Einfo' & Hin).
    pose proof Hself as Hself2.
    specialize (Hself2 _ Hin).
    rewrite -> (tc_rootinfo_tid_inj Einfo'), -> (tc_rootinfo_tid_inj Einfo), -> Eid_ch, -> Hself1 in Hself2.
    injection Hself2 as Hself2.
    rewrite Einfo', Einfo in Hself2.
    rewrite -> Eid_ch, <- (tc_rootinfo_clk_inj Hself2) in Hin'.

    (* ... *)
    destruct sub' as [(u, clk, aclk) chn].
    simpl in Hin_ch.
    eapply tc_shape_inv_sub, Foralltc_subtc in Hshape'.
    2: apply Hsub'.
    eapply tc_respect_sub, Foralltc_subtc in Hrespect.
    2: apply Hsub'.
    pose proof (tc_get_updated_nodes_join_aux_result_regular tc u clk aclk chn Hshape' Hrespect)
      as (chn' & Hsublist & Eaux & _ & Hjudge & _).
    rewrite -> Forall_forall in Hjudge. specialize (Hjudge _ Hin_ch).
    rewrite <- Hjudge in Hin'.

    (* use the property obtained above *)
    rewrite tc_get_updated_nodes_join_eta in Esub.
    cbn delta [info_tid] beta iota in Esub.
    rewrite Eaux in Esub.
    subst sub. simpl in Hshape_pff.
    rewrite -> map_app, <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hshape_pff.
    repeat setoid_rewrite base.elem_of_list_In in Hshape_pff.
    destruct Hshape_pff as (_ & Htarg & _).
    exfalso. eapply Htarg. 2: apply tc_getnode_in_iff; rewrite Eres_; auto.
    eapply Permutation_in.
    1: symmetry; apply Permutation_map, tc_flatten_root_chn_split.
    rewrite map_app, in_app_iff. left.
    rewrite map_map. rewrite -> map_ext with (g:=tc_roottid).
    2: intros a; unfold tc_roottid; rewrite (prefixtc_rootinfo_same (tc_get_updated_nodes_join_is_prefix _ _)); reflexivity.
    apply in_map. assumption.
  }
  match type of Egj with map ?ff ?al = map ?ff ?bl => assert (length al = length bl) as Elen
    by (rewrite <- ! map_length with (f:=ff), -> Egj; reflexivity) end.
  apply f_equal with (f:=map info_tid) in Egj.
  rewrite -> ! map_map in Egj. 
  rewrite -> 2 map_ext with (f:=(fun x : treeclock => info_tid (tc_rootinfo x))) (g:=tc_roottid) in Egj; auto.
  remember (removelast lstk_pre) as lstk_pre' eqn:Elstk_pre'.
  rewrite Elstk_pre, removelast_last in Elstk_pre'.
  assert (tc_traversal_snapshot (tc_get_updated_nodes_join tc tc')
    (lstk_pre' ++ (map tc_roottid (tc_get_updated_nodes_join_aux (tc_join_partial tc pfi) 
      (tc_getclk (tc_roottid sub) tc) (tc_rootchn sub'))))
    (tc_vertical_splitr false (tc_get_updated_nodes_join tc tc') l)) as Htts_goal.
  {
    subst lstk_pre' sub.
    rewrite Egj, (tc_rootinfo_tid_inj Erooinfo_sub').
    eapply eq_ind_r with (y:=map tc_roottid (tc_get_updated_nodes_join_aux _ _ _)).
    1: rewrite <- map_app; apply tc_traversal_snapshot_trans, Hprefix_sub.
    destruct sub'.
    rewrite tc_get_updated_nodes_join_eta.
    reflexivity.
  }
  pose proof (is_tc_nodearray_proj_onlyheadch_derived_full _ _ Hprojn1') as Hreadheadch.
  eapply Foralltc_subtc in Hreadheadch.
  2: apply Hsub'.
  hnf in Hreadheadch.
  match goal with |- context[data_at Tsh (tarray tint dim) ?lstkstk plstk] =>
    forward_call (dim, tc_join_partial tc pfi, plclk, plnode, plstk, (length lstk_pre - 1)%nat, p, 
      Vint (Int.repr (Z.of_nat (tc_roottid tc'))), plclk', plnode', plstk', Vint (Int.repr (-1)), p', 
      tc_getclk (tc_roottid sub) tc, tc_roottid sub', tc_rootchn sub', lclk1, lstkstk, lclk', lnode') end.
  1:{ 
    entailer!. simpl. 
    rewrite <- (tc_rootinfo_tid_inj Erooinfo_sub').
    reflexivity.
  }
  1:{
    unfold treeclock_payload, tc_roottid.
    rewrite ! tc_join_partial_rootinfo_same.
    rewrite Zlength_correct in Hlen_lstk_pre_ge0 |- *.
    (* ... *)
    replace (Z.of_nat (length lstk_pre) - 1 - 1) with (Z.of_nat (length lstk_pre - 1) - 1) by lia.
    entailer!.
  }
  1:{
    match goal with HH : Foralltc _ (tc_join_partial tc pfi) |- _ => rename HH into Hbundle end.
    apply Foralltc_and in Hbundle.
    split.
    1: rewrite <- (tc_rootinfo_tid_inj Erooinfo_sub'); assumption.
    split.
    1: apply Hbundle.
    split.
    1:{
      eapply Foralltc_subtc in Hsub'. 2: rewrite -> Foralltc_idempotent; apply Hcb_tc'.
      apply Foralltc_chn_selves.
      assumption.
    } 
    split.
    1:{ 
      subst lstk_pre. rewrite -> Zlength_app, Zlength_map in Hlensum |- *.
      rewrite Zlength_map, Zlength_cons. rewrite <- Hlensum. clear. list_solve.
    }
    split.
    1:{
      eapply Foralltc_subtc in Hsub'. 2: rewrite -> Foralltc_idempotent; apply Hprojc1'.
      apply Foralltc_chn.
      assumption.
    }
    split.
    1:{
      eapply Foralltc_subtc in Hsub'. 2: apply Hprojn1'. assumption.
    } 
    1:{
      (* stack property *)
      replace (length lstk_pre - 1)%nat with (length lstk_pre')%nat by (subst; rewrite app_length; simpl; lia).
      match goal with |- context[(_ + length ?ll)%nat] => replace (length ll) with (length (map tc_roottid ll)) end.
      2: now rewrite map_length.
      subst lstk_pre'.
      rewrite <- app_length.
      inversion Htts_goal.
      1: simpl; lia.
      match goal with HH : ?ll = _ |- context[length ?ll] => rewrite HH end.
      rewrite map_length, app_length.
      match goal with |- context[length (snd (_ ?tcc ?ll))] => 
        pose proof (tc_traversal_waitlist_length_lt_tc_size tcc ll) as Htmp end.
      simpl.
      pose proof (prefixtc_size_le Hprefix_all).
      pose proof (tc_size_bounded_by_dim tc' dim Hdim Htid' (tid_nodup _ Hshape')).
      unfold tc_size in *.
      lia.
    }
  }

  (* final! *)
  (* first, deal with length *)
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
  Exists pfi lclk1 lnode1.
  rewrite ! map_length in Elstk_pre_len'.
  rewrite 1 Elstk_pre_len'.
  rewrite <- app_length, <- Zlength_correct, -> Zlength_map.
  entailer!.
  {
    split.
    - rewrite map_app, Egj. 
      eapply eq_ind_r with (y:=map tc_roottid (tc_get_updated_nodes_join_aux _ _ _)).
      1: rewrite <- map_app; apply tc_traversal_snapshot_trans, Hprefix_sub.
      destruct sub'.
      rewrite tc_get_updated_nodes_join_eta.
      reflexivity.
    - rewrite map_app, in_app_iff.
      rewrite in_app_iff in Hnotin_tc'.
      intros [ Hin | Hin ]. 1: apply Hnotin_tc'; tauto.
      rewrite Egj, (tc_rootinfo_tid_inj Erooinfo_sub') in Hin.
      revert Hin.
      replace (tc_get_updated_nodes_join_aux _ _ _) with (tc_rootchn (tc_get_updated_nodes_join tc sub'))
        by (destruct sub'; rewrite tc_get_updated_nodes_join_eta; reflexivity).
      erewrite -> map_app, -> Permutation_app_tail in Hshape_pff.
      2: apply Permutation_map, tc_flatten_root_chn_split.
      rewrite -> map_app, -> Permutation_app_comm, -> tc_flatten_direct_result in Hshape_pff.
      simpl in Hshape_pff.
      rewrite -> NoDup_cons_iff, -> ! in_app_iff in Hshape_pff.
      intros Hin. apply Hshape_pff. right. left.
      unfold tc_roottid in Hin |- *.
      rewrite Erootinfo_pfi, Erootinfo_prefix. apply Hin.
  }

(* require around 45 seconds to check this Qed *)
Qed.

End Main_Proof.
