Require Import VST.floyd.proofauto.
Require Import distributedclocks.clocks.treeclock.
From distributedclocks.vst Require Import treeclock_clight util_vst array_support util_treeclock.
From distributedclocks.utils Require Import libtac.

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
    (* let tmp := aux (Z.of_nat (tc_roottid ch)) chn' in  *)
    nth_error l (tc_roottid ch) = 
    Some (node_payload (match chn' with nil => default_nodefield | ch' :: _ => (Z.of_nat (tc_roottid ch')) end) 
      prev (Z.of_nat par) (tc_headch_Z ch)) /\
    aux (Z.of_nat (tc_roottid ch)) chn'
    (*
    match chn' with
    | nil =>
      nth_error l (tc_roottid ch) = 
      Some (node_payload lch default_nodefield (Z.of_nat par) (tc_headch_Z ch))
    | ch' :: _ =>
      nth_error l (tc_roottid ch) = 
      Some (node_payload lch (Z.of_nat (tc_roottid ch')) (Z.of_nat par) (tc_headch_Z ch))
      /\ tmp
    end
    *)
  end.

(*
(* TODO cannot find decreasing measure? *)
Definition is_tc_nodearray_proj_aux (par headch : nat) (l : list (reptype t_struct_node)) :
  nat -> list treeclock -> Prop := 
  fix aux lch chn {struct chn} : Prop := 
  match chn with
  | nil => True (* will not enter this *)
  | ch :: nil => 
    nth_error l (tc_roottid ch) = 
    Some (node_payload (Z.of_nat lch) 0%Z (Z.of_nat par) (Z.of_nat headch))
  | ch :: ch' :: chn' =>
    nth_error l (tc_roottid ch) = 
    Some (node_payload (Z.of_nat lch) (Z.of_nat (tc_roottid ch')) (Z.of_nat par) (Z.of_nat headch)) /\
    aux (tc_roottid ch) (ch' :: chn')
  end. 
*)

Definition is_tc_nodearray_proj_aux (l : list (reptype t_struct_node)) (tc : @treeclock nat): Prop :=
  is_tc_nodearray_proj_chnaux (tc_roottid tc) l default_nodefield (tc_rootchn tc).
  (*
  let: Node _ chn := tc in 
  match chn with
  | nil => True
  | ch :: _ => is_tc_nodearray_proj_chnaux (tc_roottid tc) l default_nodefield chn
  end.
  *)

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

(*
Fixpoint tc_rep (dim : Z) (plnode plclk : val) (tc : @treeclock nat) : mpred :=
  match tc with Node (mkInfo u clk aclk) chn =>
  (tc_chn_rep dim plnode plclk u default_nodefield chn *
  fold_right_sepcon (map (tc_rep dim plnode plclk) chn))%logic
  end.
*)

(* TODO the representation of unused_bag_rep is debatable *)

(* Definition unused_bag_rep (dim : Z) (plnode plclk : val) (l : list nat) : mpred := *)
Definition unused_bag_rep (dim : Z) (plnode plclk : val) (tcs : list (@treeclock nat)) : mpred :=
  (*
  ALL i : nat, !! (~ In i l /\ Z.of_nat i < dim) --> EX c1 c2 z1 z2 z3 z4, 
    clock_rep c1 c2 (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    node_rep z1 z2 z3 z4 (offset_val (sizeof t_struct_node * Z.of_nat i) plnode).
  *)
  (*
  ALL i : nat, !! (~ In i l /\ Z.of_nat i < dim) --> 
    data_at Tsh t_struct_clock (clock_payload 0%Z 0%Z) (offset_val (sizeof t_struct_clock * Z.of_nat i) plclk) *
    data_at Tsh t_struct_node default_nodestruct (offset_val (sizeof t_struct_node * Z.of_nat i) plnode). 
  *)
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

(*
Fact is_tc_nodearray_proj_aux_tid_bounded lnode tc (Hproj : is_tc_nodearray_proj_aux lnode tc) :
  Forall (fun tc' => Z.of_nat (tc_roottid tc') < Zlength lnode) (tc_rootchn tc).
Proof.
  destruct tc as [(u, clk, aclk) chn].
  now apply is_tc_nodearray_proj_chnaux_tid_bounded in Hproj.
Qed.
*)

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
  (* at least, we can eliminate some hard induction now *)
  (*
  revert lnode Hproj HH.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in HH.
  apply Foralltc_cons_iff in Hproj. destruct Hproj as (Hchn & Hproj). 
  constructor; simpl; auto.
  apply is_tc_nodearray_proj_chnaux_tid_bounded in Hchn.
  rewrite -> Forall_forall in IH, Hproj, Hchn |- *.
  intros ch Hin. specialize (Hproj _ Hin). specialize (Hchn _ Hin). apply IH; auto.
  *)
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

(*
Fact is_tc_nodearray_proj_aux_regular lnode tc (Hproj : is_tc_nodearray_proj_aux lnode tc)
  dim (Hlen : Zlength lnode = dim)
  (Hu : Z.of_nat (tc_roottid tc) < dim)
  (Hchn : Forall (fun ch => default_nodefield <= tc_headch_Z ch < dim) (tc_rootchn tc)) :
  Forall (fun tc' => node_struct_regular dim (Znth (Z.of_nat (tc_roottid tc')) lnode)) (tc_rootchn tc).
Proof.
  destruct tc as [(u, clk, aclk) chn].
  simpl in Hu, Hproj, Hchn |- *.
  destruct chn. 1: constructor.
  eapply is_tc_nodearray_proj_chnaux_regular; eauto.
  unfold default_nodefield. lia.
Qed.
*)

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
  pose proof (tc_getnode_in_iff a tcs1) as H1.
  pose proof (tc_getnode_in_iff a tcs2) as H2.
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
  - intros x. rewrite <- seq_upto, -> filter_In, -> in_seq, -> tc_getnode_in_iff.
    split; try tauto. intros HH. split; auto.
    rewrite <- tc_getnode_in_iff in HH.
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
        now rewrite -> tc_getnode_in_iff, -> Hn in Hin.
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
        now rewrite -> tc_getnode_in_iff, -> Hn in Hin.
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

Lemma tc_rep_subtree_frame tc : forall l sub (Hsub : subtc_witness l sub tc) 
  dim plnode plclk z1 z2 z3,
  tc_subroot_rep dim plnode plclk tc z1 z2 z3 *
    tc_rep_noroot dim plnode plclk tc |--
  EX z1' z2' z3' ,
  (* TODO is this enough? or reuse the position to pose stronger constraints? *)
  !! (l = nil -> z1 = z1' /\ z2 = z2' /\ z3 = z3') &&
  tc_subroot_rep dim plnode plclk sub z1' z2' z3' *
    tc_rep_noroot dim plnode plclk sub *
  (* (ALL sub',  *)
  (* TODO or use implication? *)
  (ALL chn_sub', 
    (tc_subroot_rep dim plnode plclk (Node (tc_rootinfo sub) chn_sub') z1' z2' z3' *
      tc_rep_noroot dim plnode plclk (Node (tc_rootinfo sub) chn_sub')) -*
    tc_subroot_rep dim plnode plclk (tc_locate_update tc l (Node (tc_rootinfo sub) chn_sub')) z1 z2 z3 *
      tc_rep_noroot dim plnode plclk (tc_locate_update tc l (Node (tc_rootinfo sub) chn_sub'))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  destruct l as [ | x l ].
  - hnf in Hsub. injection Hsub as <-.
    Exists z1 z2 z3.
    entailer!.
    simpl.
    apply allp_right. intros chn_sub'.
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
    apply allp_right. intros chn_sub'.
    (* hint. *)
    allp_left chn_sub'.
    fold fold_right_sepcon.
    apply wand_frame_intro'.
    (*
    (* ? *) 
    pose proof (eq_refl (tc_rep_noroot dim plnode plclk (Node (tc_rootinfo sub) chn_sub'))) as Htmp.
    unfold tc_rep_noroot in Htmp at 1.
    fold tc_rep_noroot in Htmp. rewrite Htmp. entailer!.
    *)
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
    assert (tc_roottid (tc_locate_update ch l (Node (tc_rootinfo sub) chn_sub')) = tc_roottid ch) as Eid.
    {
      destruct l.
      - simpl in Hsub |- *. now injection Hsub as <-.
      - destruct ch as [ni chn]. simpl in Hsub |- *. destruct (nth_error chn n); eqsolve.
    }
    rewrite -> ! Eid.
    entailer!.
    destruct pre; unfold tc_headch_Z; simpl; now try rewrite Eid.
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

Definition node_struct_get_headch (np : reptype t_struct_node) :=
  match np with (_, (_, (_, res))) => res end.

Definition get_updated_nodes_join_chn_spec :=
  DECLARE _get_updated_nodes_join_chn
  WITH dim : Z, 
    (* plnode is not used here *)
    tc : (@treeclock nat), plclk : val, plnode : val, plstk : val, top : nat, p : val,
    v1 : val, plclk' : val, plnode' : val, v2 : val, v3 : val, p' : val,
    par' : nat, chn' : list (@treeclock nat), 
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
      0 <= Z.of_nat (tc_getclk par' tc) <= Int.max_signed;
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
      Z.of_nat (top + length (tc_get_updated_nodes_join_aux tc par' chn')) <= dim)
    PARAMS (p; p'; Vint (Int.repr (Z.of_nat par')); Vint (Int.repr (Z.of_nat (tc_getclk par' tc))))
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
            (map tc_roottid (tc_get_updated_nodes_join_aux tc par' chn'))) ++
          skipn (top + length (tc_get_updated_nodes_join_aux tc par' chn')) lstk) plstk;
      data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tc_roottid tc)) 
        plclk plnode plstk (Z.of_nat (top + length (tc_get_updated_nodes_join_aux tc par' chn')) - 1)) p).

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

(*

Section Dim_Bounds.

Variables (dim : Z) (tc : (@treeclock nat)) (plclk plnode plstk : val) (top : Z) (p : val).
Hypothesis (Hdim_short : is_pos_tshort dim).

(* TODO if nth list returns none then tc is single *)

Lemma dim_bounds_treeclock_rep_root : 

*)

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

(*
Local Corollary array_with_hole_intro_alt : forall (sh : Share.t) (t : type) (i n : Z) 
    (al : list (reptype t)) (p : val),
  0 <= i < n ->
  data_at sh (tarray t n) al p
  |-- data_at sh t (Znth i al) (field_address (tarray t n) (SUB i) p)
        * SingletonHole.array_with_hole sh t i n al p.
Proof SingletonHole.array_with_hole_intro.
*)

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
      apply tc_getnode_has_tid in E. destruct E as (Hin & Eid).
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
      Forall (fun tc' => ((tc_getclk par' tc) < tc_rootaclk tc' \/ (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc')%nat) (firstn i chn');
      (* ... *)
      is_tc_nodearray_proj_chnaux par' lnode' prev (skipn i chn'))
    LOCAL (temp _vprime_tid (Vint (Int.repr (tcs_head_Z (skipn i chn')))); (* changed *)
      (* temp _nd_par (offset_val (sizeof (Tstruct _Node noattr) * Z.of_nat par') plnode'); *)
      temp _self p; temp _tc p';
      temp _par_clock (Vint (Int.repr (Z.of_nat (tc_getclk par' tc)))))
    SEP (data_at Tsh (tarray t_struct_node dim) lnode' plnode';
      data_at Tsh (tarray t_struct_clock dim) lclk' plclk';
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (v1, (plclk', (plnode', (v2, v3))))) p';
      data_at Tsh (tarray t_struct_clock dim) lclk plclk;
      data_at Tsh (tarray tint dim) 
        (firstn top lstk ++
          (map (fun y : nat => Vint (Int.repr (Z.of_nat y)))
            (map tc_roottid (tc_get_updated_nodes_join_aux tc par' (firstn i chn')))) ++
        skipn (top + length (tc_get_updated_nodes_join_aux tc par' (firstn i chn'))) lstk) plstk;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim),
          (Vint (Int.repr (Z.of_nat (tc_roottid tc))),
          (plclk, (plnode, (plstk, Vint (Int.repr 
            (Z.of_nat (top + length (tc_get_updated_nodes_join_aux tc par' (firstn i chn'))) - 1))))))) p))%assert.  (* this %assert really helps. *)
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
  epose proof (tc_get_updated_nodes_join_aux_app tc par' (firstn i chn') (skipn i chn') ?[Goalq]) as Haux.
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
  (* TODO streamline this? *)
  assert (0 <= (Z.of_nat (tc_getclk v' tc)) <= Int.max_signed) as _Hyp12.
  {
    unfold tc_getclk. destruct (tc_getnode v' tc) as [ res | ] eqn:Eres; try lia.
    eapply tc_getnode_res_Foralltc in Eres. 2: apply Hcb_tc. simpl in Eres. lia.
  }
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
    assert (Z.of_nat (top + length (tc_get_updated_nodes_join_aux tc par' (firstn i chn'))) < dim) as Htop1 
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
      destruct (aclk_v' <=? tc_getclk par' tc)%nat eqn:Eaclk_le.
      2: apply Nat.leb_gt in Eaclk_le; lia.
      rewrite app_nil_r in Haux.
      forward. entailer!.
      rewrite ! Haux. entailer!.
    }
    destruct (aclk_v' <=? tc_getclk par' tc)%nat eqn:Eaclk_le.
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

(* single tree removal *)
(*
Fact tc_chn_focus tc (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  ch (Hin : In ch (tc_rootchn tc)) sub (Hsub : subtc sub ch) :
  exists pre suf, 
    (tc_rootchn tc) = pre ++ (ch :: suf) /\
    .
Proof.
  destruct tc as [ni chn]. simpl in *.
  induction chn as [ | ch' chn IH ].
  1: now simpl in Hin.
  simpl in Hnodup_chn. rewrite NoDup_cons_iff in Hnodup_chn.
  destruct Hnodup_chn as (Hnotin & Hnodup_chn).
  simpl in Hin. destruct Hin as [ -> | Hin ].
  - exists nil, chn. simpl. split; auto.
    symmetry in Eid. rewrite <- Eid in Hnotin.
    rewrite <- has_same_tid_true in Eid. rewrite -> Eid. simpl. 
    (* TODO this is ... *)
    clear -Hnotin.
    induction chn as [ | ch' chn IH ]; simpl in *; auto.
    apply Decidable.not_or in Hnotin.
    destruct Hnotin as (Hneq & Hnotin).
    specialize (IH Hnotin).
    assert (has_same_tid idx ch' = false) as -> by (apply has_same_tid_false; eqsolve).
    simpl. eqsolve.
  - specialize (IH Hnodup_chn Hin).
    destruct IH as (pre & suf & -> & E).
    exists (ch' :: pre), suf.
    split; auto.
    rewrite -> map_app, -> in_app_iff in Hnotin.
    simpl in Hnotin. 
    assert (idx <> tc_roottid ch') as Hneq by eqsolve.
    rewrite <- has_same_tid_false in Hneq. 
    simpl. rewrite -> Hneq. simpl. eqsolve.
Qed.

Fact tc_remove_ch_presuf tc idx (Hnodup_chn : NoDup (map tc_roottid (tc_rootchn tc)))
  ch (Eid : tc_roottid ch = idx) (Hin : In ch (tc_rootchn tc)) :
  exists pre suf, 
    (tc_rootchn tc) = pre ++ (ch :: suf) /\
    (tc_rootchn (tc_remove_ch tc idx)) = pre ++ suf.
Proof.
  destruct tc as [ni chn]. simpl in *.
  induction chn as [ | ch' chn IH ].
  1: now simpl in Hin.
  simpl in Hnodup_chn. rewrite NoDup_cons_iff in Hnodup_chn.
  destruct Hnodup_chn as (Hnotin & Hnodup_chn).
  simpl in Hin. destruct Hin as [ -> | Hin ].
  - exists nil, chn. simpl. split; auto.
    symmetry in Eid. rewrite <- Eid in Hnotin.
    rewrite <- has_same_tid_true in Eid. rewrite -> Eid. simpl. 
    (* TODO this is ... *)
    clear -Hnotin.
    induction chn as [ | ch' chn IH ]; simpl in *; auto.
    apply Decidable.not_or in Hnotin.
    destruct Hnotin as (Hneq & Hnotin).
    specialize (IH Hnotin).
    assert (has_same_tid idx ch' = false) as -> by (apply has_same_tid_false; eqsolve).
    simpl. eqsolve.
  - specialize (IH Hnodup_chn Hin).
    destruct IH as (pre & suf & -> & E).
    exists (ch' :: pre), suf.
    split; auto.
    rewrite -> map_app, -> in_app_iff in Hnotin.
    simpl in Hnotin. 
    assert (idx <> tc_roottid ch') as Hneq by eqsolve.
    rewrite <- has_same_tid_false in Hneq. 
    simpl. rewrite -> Hneq. simpl. eqsolve.
Qed.
*)

(*
Fact tc_getnode_single has_same_tid

Fact tc_detach_single_node_simplify (idx : nat) tc :
  tc_detach_nodes (Node (mkInfo idx 0%nat 0%nat) nil) tc =
  let: Node ni chn := tc in
  let: (new_chn, res) := List.split (map (tc_detach_nodes (Node (mkInfo idx 0%nat 0%nat) nil)) chn) in
  let: (res', new_chn') := List.partition (fun tc' => tc_getnode (tc_roottid tc') subtree_tc')
    new_chn in
  (Node ni new_chn', (List.concat res) ++ res').
*)

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

(*
    pose proof Enth as Hin_ch. apply nth_error_In in Hin_ch.

    


    rewrite -> filter_all_false in Eres'.


  pose proof Hin_ch as Hpresuf. apply in_split in

  

  destruct l as [ | x l ].
  - hnf in Hsub. simpl in Hsub. injection Hsub as <-. simpl in Hin.
    (* cbn delta [tc_locate_update] beta iota. *)
    pose proof (tc_remove_ch_presuf (Node (mkInfo u clk aclk) chn)) as Hpresuf.
    simpl in Hpresuf. 
    specialize (Hpresuf _ (proj1 (tid_nodup_root_chn_split _ Hnodup)) _ eq_refl Hin).
    destruct Hpresuf as (pre & suf & Echn & Efil).
    simpl. rewrite -> Efil, -> ! Echn, -> map_app. simpl.
    (* tc_roottid res not in pre/suf *)
    assert (forall ch', In ch' pre \/ In ch' suf -> ~ In (tc_roottid res) (map tc_roottid (tc_flatten ch'))) as Hnotin'.
    {
      (* tedious *)
      intros ch' H Hn.
      subst chn. rewrite <- flat_map_app, -> map_app in Hnodup.
      simpl in Hnodup. rewrite -> map_app in Hnodup.
      apply NoDup_app in Hnodup. destruct Hnodup as (_ & Hnodup & Hdj1).
      apply NoDup_app in Hnodup. destruct Hnodup as (_ & _ & Hdj2).
      specialize (Hdj1 (tc_roottid res)). specialize (Hdj2 (tc_roottid res)).
      rewrite -> map_flat_map_In, -> in_app_iff in Hdj1.
      rewrite -> map_flat_map_In in Hdj2.
      pose proof (tc_flatten_self_in res) as Hself.
      apply in_map with (f:=tc_roottid) in Hself.
      destruct H as [ H | H ].
      - apply Hdj1; auto. eauto.
      - apply Hdj2 in Hself. apply Hself. eauto.
    }
    erewrite -> map_ext_Forall with (l:=pre).
    2:{ 
      rewrite -> Forall_forall. intros ch H. specialize (Hnotin' _ (or_introl H)). 
      apply tc_detach_nodes_intact. simpl. intros. eqsolve.
    }
    erewrite -> map_ext_Forall with (l:=suf).
    2:{ 
      rewrite -> Forall_forall. intros ch H. specialize (Hnotin' _ (or_intror H)). 
      apply tc_detach_nodes_intact. simpl. intros. eqsolve.
    }

    admit.
  - hnf in Hsub. simpl in Hsub.
    destruct (nth_error chn x) as [ ch | ] eqn:Enth; try eqsolve.
    pose proof Enth as Hin_ch. apply nth_error_In in Hin_ch.


    rewrite -> Forall_forall in IH. specialize (IH _ Hin_ch).


    tc_detach_nodes
      

      
      
      rewrite <- Efil in H. apply filter_In in H.
      rewrite -> negb_true_iff, -> has_same_tid_false in H.
      rewrite -> in_map_iff. intros ().
      destruct 
      



    rewrite -> Echn, -> map_app, -> in_app_iff in Hnotin'. 

    tc_detach_nodes


    simpl. 

    simpl.

  simpl.
*)

(* rather customized *)

(*
Fact is_tc_nodearray_proj_chnaux_congr chn : forall lnode par prev chn' 
  (Hcong : map tc_rootinfo chn = map tc_rootinfo chn')
  (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn),
  is_tc_nodearray_proj_chnaux par lnode prev chn'.
Proof.
  induction chn as [ | ch chn IH ]; intros.
  - destruct chn'; simpl in Hcong; try eqsolve.
  - destruct chn' as [ | ch' chn' ]; simpl in Hcong; try eqsolve.
    inversion Hcong.
    simpl in Hproj |- *. destruct Hproj as (HH & Hproj).
    eapply IH in H1. 2: apply Hproj.
    apply tc_rootinfo_tid_inj in H0. 
    split; try eqsolve. 
*)

(*
Fact is_tc_nodearray_proj_chnaux_congr lnode par 

Fact tc_locate_update_remove_ch_rootinfo_intact ch l tc_par idx
  (Hsub : tc_locate ch l = Some tc_par) :
  (tc_rootinfo (tc_locate_update ch l (tc_remove_ch tc_par idx))) = 
  (tc_rootinfo ch).
Proof.
*)

(*

Definition node_struct_upd_next (next : Z) (np : reptype t_struct_node) :=
  match np with (_, (z2, (z3, z4))) => (Vint (Int.repr next), (z2, (z3, z4))) end.

Definition node_struct_upd_prev (prev : Z) (np : reptype t_struct_node) :=
  match np with (z1, (_, (z3, z4))) => (z1, (Vint (Int.repr prev), (z3, z4))) end.

Definition node_struct_upd_par (par : Z) (np : reptype t_struct_node) :=
  match np with (z1, (z2, (_, z4))) => (z1, (z2, (Vint (Int.repr par), z4))) end.

Definition node_struct_upd_headch (headch : Z) (np : reptype t_struct_node) :=
  match np with (z1, (z2, (z3, _))) => (z1, (z2, (z3, Vint (Int.repr headch)))) end.

Fact is_tc_nodearray_proj_chnaux_indom_preserve chn : forall lnode par prev
  (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn)
  lnode' (Hlen : Zlength lnode = Zlength lnode')
  (Hpre : forall idx, In idx (map tc_roottid chn) -> 
    Znth (Z.of_nat idx) lnode = Znth (Z.of_nat idx) lnode'),
  is_tc_nodearray_proj_chnaux par lnode' prev chn.
Proof.
  induction chn as [ | ch chn IH ]; intros; simpl in *; auto.
  destruct Hproj as (HH & Hproj). split.
  - apply Znth_nth_error_result.
    1: rewrite <- ZtoNat_Zlength, <- Hlen, -> ZtoNat_Zlength; 
      now apply nth_error_some_inrange in HH.
    apply nth_error_Znth_result in HH.
    rewrite <- Hpre; auto. 
  - eapply IH; eauto.
Qed.

Fact is_tc_nodearray_proj_chnaux_upd_preserve chn : forall lnode par prev
  (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn)
  idx (Hnotin : ~ In idx (map tc_roottid chn)) np,
  is_tc_nodearray_proj_chnaux par (upd_Znth (Z.of_nat idx) lnode np) prev chn.
Proof.
  intros. eapply is_tc_nodearray_proj_chnaux_indom_preserve. 
  - apply Hproj.
  - now rewrite -> Zlength_upd_Znth.
  - intros idx' Hin. destruct (Nat.eq_dec idx idx') as [ <- | Hneq ]; try eqsolve.
    rewrite -> Znth_upd_Znth_diff; auto; try lia.
Qed.

(*
Fact is_tc_nodearray_proj_chnaux_upd_preserve chn : forall lnode par prev
  (Hproj : is_tc_nodearray_proj_chnaux par lnode prev chn)
  idx (Hnotin : ~ In idx (map tc_roottid chn)) np, 
  is_tc_nodearray_proj_chnaux par (upd_Znth (Z.of_nat idx) lnode np) prev chn.
Proof.
  induction chn as [ | ch chn IH ]; intros; simpl in *; auto.
  destruct Hproj as (HH & Hproj). split.
  - apply Znth_nth_error_result.
    1: rewrite <- ZtoNat_Zlength, -> Zlength_upd_Znth, -> ZtoNat_Zlength; 
      now apply nth_error_some_inrange in HH.
    apply nth_error_Znth_result in HH.
    rewrite <- HH. rewrite -> Znth_upd_Znth_diff; auto; lia.
  - apply IH; eqsolve.
Qed.
*)

Fact is_tc_nodearray_proj_indom_preserve lnode tc (Hproj : is_tc_nodearray_proj lnode tc) :
  forall lnode' (Hlen : Zlength lnode = Zlength lnode')
  (Hpre : forall idx, In idx (map tc_roottid (tc_flatten tc)) -> 
    Znth (Z.of_nat idx) lnode = Znth (Z.of_nat idx) lnode'),
  is_tc_nodearray_proj lnode' tc.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in Hpre.
  setoid_rewrite -> map_flat_map_In in Hpre.
  hnf in Hproj |- *. rewrite -> Foralltc_cons_iff in Hproj. destruct Hproj as (H & Hproj).
  constructor.
  - eapply is_tc_nodearray_proj_chnaux_indom_preserve; eauto.
    simpl. setoid_rewrite in_map_iff. intros idx (ch & <- & Hin). apply Hpre. right. 
    exists ch. split; auto. apply in_map, tc_flatten_self_in.
  - rewrite -> Forall_forall in IH, Hproj |- *.
    intros ch Hin. apply IH; auto. 1: apply Hproj; auto.
    intros idx HH. apply Hpre. right. eauto.
Qed.

Fact is_tc_nodearray_proj_upd_preserve lnode tc (Hproj : is_tc_nodearray_proj lnode tc)
  idx (Hnotin : ~ In idx (map tc_roottid (tc_flatten tc))) np :
  is_tc_nodearray_proj (upd_Znth (Z.of_nat idx) lnode np) tc.
Proof.
  eapply is_tc_nodearray_proj_indom_preserve. 
  - apply Hproj.
  - now rewrite -> Zlength_upd_Znth.
  - intros idx' Hin. destruct (Nat.eq_dec idx idx') as [ <- | Hneq ]; try eqsolve.
    rewrite -> Znth_upd_Znth_diff; auto; try lia.
Qed.

(*
Fact is_tc_nodearray_proj_upd_preserve lnode tc (Hproj : is_tc_nodearray_proj lnode tc) :
  forall idx (Hnotin : ~ In idx (map tc_roottid (tc_flatten tc))) np, 
  is_tc_nodearray_proj (upd_Znth (Z.of_nat idx) lnode np) tc.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in Hnotin.
  apply Decidable.not_or in Hnotin. destruct Hnotin as (Hneq & Hnotin).
  rewrite -> map_flat_map_In in Hnotin.
  hnf in Hproj |- *. rewrite -> Foralltc_cons_iff in Hproj. destruct Hproj as (H & Hproj).
  constructor.
  - apply is_tc_nodearray_proj_chnaux_upd_preserve; auto.
    simpl. rewrite in_map_iff. intros (ch & <- & Hin). apply Hnotin.
    exists ch. split; auto. apply in_map, tc_flatten_self_in.
  - rewrite -> Forall_forall in IH, Hproj |- *.
    intros ch Hin. apply IH; auto. 1: apply Hproj; auto.
    intros HH. apply Hnotin. eauto.
Qed.
*)

Definition tc_detach_par_upd idx (pre suf : list (@treeclock nat)) lnode :=
  match pre with 
  | nil => upd_Znth (Z.of_nat idx) lnode 
    (node_struct_upd_headch (tcs_head_Z suf) (Znth (Z.of_nat idx) lnode))
  | _ :: _ => lnode 
  end.

Definition tc_detach_prev_upd (pre suf : list (@treeclock nat)) lnode :=
  (* may use last instead, but now keep aligned with (tcs_head_Z (rev pre)) below? *)
  match rev pre with 
  | nil => lnode
  | prev :: _ => upd_Znth (Z.of_nat (tc_roottid prev)) lnode 
    (node_struct_upd_next (tcs_head_Z suf) (Znth (Z.of_nat (tc_roottid prev)) lnode))
  end.

Definition tc_detach_next_upd (pre suf : list (@treeclock nat)) lnode :=
  match suf with 
  | nil => lnode
  | next :: _ => upd_Znth (Z.of_nat (tc_roottid next)) lnode 
    (node_struct_upd_prev (tcs_head_Z (rev pre)) (Znth (Z.of_nat (tc_roottid next)) lnode))
  end.

(* regular alternation; at most one footprint? *)

Inductive lnode_regalter : (list (reptype t_struct_node) -> list (reptype t_struct_node)) -> option nat -> Prop :=
  | LNAlterId : forall f o, (forall x, f x = x) -> lnode_regalter f o
  | LNAlterOne : forall f idx, (forall x, exists np, f x = upd_Znth (Z.of_nat idx) x np) -> lnode_regalter f (Some idx).

Fact tc_detach_par_upd_regalter idx pre suf :
  lnode_regalter (tc_detach_par_upd idx pre suf) (Some idx).
Proof.
  unfold tc_detach_par_upd. destruct pre.
  - apply LNAlterOne. intros l. eauto.
  - now apply LNAlterId.
Qed.

Fact tc_detach_prev_upd_regalter pre suf :
  lnode_regalter (tc_detach_prev_upd pre suf) (base.fmap tc_roottid (hd_error (rev pre))).
Proof.
  unfold tc_detach_prev_upd. destruct pre as [ | q pre' ] eqn:E.
  - now apply LNAlterId.
  - assert (pre <> nil) as Htmp by eqsolve. rewrite <- E. clear E q pre'.
    apply exists_last in Htmp. destruct Htmp as (pre' & prev & E).
    rewrite -> E, -> rev_app_distr. simpl. 
    apply LNAlterOne. intros l. eauto.
Qed.

Fact tc_detach_next_upd_regalter pre suf :
  lnode_regalter (tc_detach_next_upd pre suf) (base.fmap tc_roottid (hd_error suf)).
Proof.
  unfold tc_detach_next_upd. destruct suf as [ | next suf' ] eqn:E.
  - now apply LNAlterId.
  - apply LNAlterOne. intros l. eauto.
Qed.

Fact nodearray_proj_lnode_regalter_preserve 
  lnode tc (Hproj : is_tc_nodearray_proj lnode tc)
  lf lo (H : Forall2 lnode_regalter lf lo)
  (* guess this form of notin is more suitable here *)
  (Hnotin : forall idx, In (Some idx) lo -> ~ In idx (map tc_roottid (tc_flatten tc))) :
  is_tc_nodearray_proj (fold_right (fun f l => f l) lnode lf) tc.
Proof.
  revert lnode Hproj.
  induction H as [ | f o lf lo Hrega H IH ]; intros; simpl; auto.
  simpl in Hnotin.
  inversion Hrega; subst.
  - rewrite H0. apply IH; auto.
  - match goal with |- context[f ?l] => specialize (H0 l) end.
    destruct H0 as (np & ->). 
    apply is_tc_nodearray_proj_upd_preserve; auto.
Qed.

Fact tc_remove_ch_chnaux_proj_pre : forall pre res lnode par suf
  (Hnodup : NoDup (map tc_roottid (pre ++ res :: suf)))
  prev (Hproj : is_tc_nodearray_proj_chnaux par lnode prev (pre ++ res :: suf))
  f_prev_upd (Efprev : f_prev_upd = tc_detach_prev_upd pre suf)
  f_next_upd (Efnext : f_next_upd = fun lnodee => match suf with
    | [] => lnodee
    | next :: _ =>
        upd_Znth (Z.of_nat (tc_roottid next)) lnodee
          (node_struct_upd_prev (match (rev pre) with nil => prev 
            | ch :: _ => Z.of_nat (tc_roottid ch) end)
            (Znth (Z.of_nat (tc_roottid next)) lnodee))
    end)
  lnode'
  (Elnode' : lnode' = (fold_right (fun f l => f l) lnode [f_next_upd; f_prev_upd])),
  is_tc_nodearray_proj_chnaux par lnode' prev (pre ++ suf).
Proof.
  intros pre res lnode par. 
  induction pre as [ | q pre IH ]; intros; simpl.
  - unfold tc_detach_prev_upd in Efprev. simpl in Efprev. 
    subst f_prev_upd f_next_upd. simpl in Elnode'.
    simpl in Hproj. apply proj2 in Hproj.
    destruct suf as [ | next suf ]; auto.
    simpl in Hproj |- *. destruct Hproj as (Hnext & Hproj). split.
    + (* the length is so ... *)
      pose proof Hnext as Htmp1. apply nth_error_some_inrange in Htmp1.
      pose proof Hnext as Htmp2. apply nth_error_some_inrange_Z in Htmp2.
      apply Znth_nth_error_result.  
      1: subst lnode'; rewrite <- ZtoNat_Zlength, -> Zlength_upd_Znth, -> ZtoNat_Zlength; auto.
      subst lnode'. rewrite -> upd_Znth_same; auto; try lia.
      apply nth_error_Znth_result in Hnext. now rewrite Hnext.
    + subst lnode'. apply is_tc_nodearray_proj_chnaux_upd_preserve; auto.
      simpl in Hnodup. rewrite -> ! NoDup_cons_iff in Hnodup. tauto.
  - simpl in Hnodup. rewrite -> NoDup_cons_iff in Hnodup.
    destruct Hnodup as (Hdj & Hnodup).
    simpl in Hproj. destruct Hproj as (Hq & Hproj).
    (* ! *)
    pose proof Hq as Htmp1. apply nth_error_some_inrange in Htmp1.
    pose proof Hq as Htmp2. apply nth_error_some_inrange_Z in Htmp2.
    apply nth_error_Znth_result in Hq. 
    destruct pre eqn:Epre.
    + simpl in Hq, Hproj |- *. apply proj2 in Hproj.
      unfold tc_detach_prev_upd in Efprev. simpl in Efprev. subst f_prev_upd.
      split.
      (* destruct suf as [ | next suf ]. *)
      * (* TODO repeat? *)
        subst f_next_upd. 
        apply Znth_nth_error_result.
        1: destruct suf; simpl in Elnode'; subst lnode'; 
          rewrite <- ZtoNat_Zlength, -> ! Zlength_upd_Znth, -> ZtoNat_Zlength; auto.
        subst lnode'.
        destruct suf as [ | next suf ]; simpl. 
        --rewrite -> ! upd_Znth_same; auto; try lia. now rewrite Hq.
        --simpl in Hdj. assert (tc_roottid next <> tc_roottid q) as Hneq by eqsolve.
          rewrite -> Znth_upd_Znth_diff; try lia.
          rewrite -> ! upd_Znth_same; auto; try lia. now rewrite Hq.
      * destruct suf as [ | next suf ]; auto.
        subst f_next_upd. simpl in Elnode'.
        (* still repeat? *)
        simpl in Hdj. assert (tc_roottid next <> tc_roottid q) as Hneq by eqsolve.
        rewrite -> Znth_upd_Znth_diff in Elnode'; try lia.
        simpl in Hproj |- *. destruct Hproj as (Hnext & Hproj).
        (* ! *)
        pose proof Hnext as Htmp1'. apply nth_error_some_inrange in Htmp1'.
        pose proof Hnext as Htmp2'. apply nth_error_some_inrange_Z in Htmp2'.
        apply nth_error_Znth_result in Hnext. split. 
        --apply Znth_nth_error_result.
          1: destruct suf; simpl in Elnode'; subst lnode'; 
            rewrite <- ZtoNat_Zlength, -> ! Zlength_upd_Znth, -> ZtoNat_Zlength; auto.
          subst lnode'.
          rewrite -> upd_Znth_same; auto; try lia. 2: rewrite -> ! Zlength_upd_Znth; lia.
          now rewrite Hnext.
        --subst lnode'. 
          apply is_tc_nodearray_proj_chnaux_upd_preserve; auto.
          2: simpl in Hnodup; rewrite -> ! NoDup_cons_iff in Hnodup; tauto.
          apply is_tc_nodearray_proj_chnaux_upd_preserve; auto.
    + rewrite <- ! Epre in *. assert (pre <> nil) as Htmp by eqsolve. 
      apply exists_last in Htmp. destruct Htmp as (pre' & prev' & Epre').
      rewrite Epre at 1. simpl.
      rewrite Epre in Hq at 1. simpl in Hq.
      unfold tc_detach_prev_upd in Efprev. 
      rewrite -> Epre' in Efnext, Efprev. simpl in Efnext, Efprev.
      rewrite -> rev_app_distr in Efnext, Efprev. simpl in Efnext, Efprev.
      

      split.
      * rewrite <- Hq. 

      erewrite -> IH with (suf:=suf). 2: reflexivity.
      
Admitted.
          
          now rewrite Hq.

          
          
        rewrite -> ! upd_Znth_same; auto; try lia. now rewrite Hq.

        


        

      * (* TODO repeat? *)
        simpl in Hproj |- *. destruct Hproj as (Hnext & Hproj). split.
        pose proof Hnext as Htmp1. apply nth_error_some_inrange in Htmp1.
        pose proof Hnext as Htmp2. apply nth_error_some_inrange_Z in Htmp2.
        apply Znth_nth_error_result.  
        1: subst lnode'; rewrite <- ZtoNat_Zlength, -> Zlength_upd_Znth, -> ZtoNat_Zlength; auto.
        subst lnode'. rewrite -> upd_Znth_same; auto; try lia.
        apply nth_error_Znth_result in Hnext. now rewrite Hnext.
      split.
      * admit.
      * destruct
        subst lnode'. simpl. apply is_tc_nodearray_proj_chnaux_upd_preserve; auto.
        simpl in Hnodup. rewrite -> ! NoDup_cons_iff in Hnodup. tauto.


    split.
    + 
    + 
      eapply IH. 2: apply  
  
    remember (q :: pre) 

      
      Zlength_upd_Znth; now 


  2: destruct pre eqn:E.
  1-2: simpl in Echn; subst chn; simpl in *; now apply nth_error_Znth_result.
  rewrite <- ! E in *. assert (pre <> nil) as Htmp by eqsolve. clear E.
  subst chn. simpl in Hproj. destruct Hproj as (_ & Hproj).
  erewrite -> IH with (suf:=suf). 2: reflexivity.
  2: simpl; rewrite -> in_app; simpl; tauto.
  2: apply Hproj.
  f_equal. apply exists_last in Htmp. destruct Htmp as (pre' & prev' & E).
  simpl. rewrite -> E, -> rev_app_distr. now simpl.

Fact tc_locate_update_remove_ch_proj l :
  forall res tc
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  (* this should be a derived conclusion from Hnodup, but for now ignore it *)
  (* (Hneq : tc_roottid res <> tc_roottid tc)  *)
  tc_par (Hsub : subtc_witness l tc_par tc) 
  (* (Hin : In res (tc_rootchn tc_par)) *)
  pre suf (Echn_par : (tc_rootchn tc_par) = pre ++ res :: suf)
  tc_pivot (Etc_pivot : tc_pivot = tc_locate_update tc l (tc_remove_ch tc_par (tc_roottid res)))
  (* (E : tc_detach_nodes (Node (mkInfo (tc_roottid res) 0%nat 0%nat) nil) tc = 
    (tc_pivot, (res :: nil))) *)
  lnode (Hlen : Z.of_nat (tc_roottid res) < Zlength lnode) 
  (* (Hproj : is_tc_nodearray_proj_full lnode tc) *)
  (Hproj : is_tc_nodearray_proj lnode tc)
  f_par_upd
  (* (Efpar : f_par_upd = match pre with _ :: _ => id | nil => (fun lnodee => upd_Znth (Z.of_nat (tc_roottid tc_par)) lnodee
    (node_struct_upd_headch (match suf with nil => default_nodefield | ch :: _ => Z.of_nat (tc_roottid ch) end) 
      (Znth (Z.of_nat (tc_roottid tc_par)) lnodee))) end) *)
  (Efpar : f_par_upd = tc_detach_par_upd (tc_roottid tc_par) pre suf)
  f_prev_upd
  (* (Efprev : f_prev_upd = match (rev pre) with nil => id | prev :: _ => (fun lnodee => upd_Znth (Z.of_nat (tc_roottid prev)) lnodee
    (node_struct_upd_next (match suf with nil => default_nodefield | ch :: _ => Z.of_nat (tc_roottid ch) end) 
      (Znth (Z.of_nat (tc_roottid prev)) lnodee))) end) *)
  (Efprev : f_prev_upd = tc_detach_prev_upd pre suf)
  f_next_upd
  (* (Efnext : f_next_upd = match suf with nil => id | next :: _ => (fun lnodee => upd_Znth (Z.of_nat (tc_roottid next)) lnodee
    (node_struct_upd_prev (match (rev pre) with nil => default_nodefield | ch :: _ => Z.of_nat (tc_roottid ch) end)
      (Znth (Z.of_nat (tc_roottid next)) lnodee))) end) *)
  (Efnext : f_next_upd = tc_detach_next_upd pre suf)
  lnode'
  (* (Elnode' : lnode' = f_next_upd (f_prev_upd (f_par_upd lnode))), *)
  (Elnode' : lnode' = (fold_right (fun f l => f l) lnode [f_next_upd; f_prev_upd; f_par_upd])),
  (* is_tc_nodearray_proj_full lnode' tc_pivot /\ is_tc_nodearray_proj lnode' res. *)
  (* TODO no update on res, so may ignore it? *)
  is_tc_nodearray_proj lnode' tc_pivot /\ is_tc_nodearray_proj lnode' res.
Proof.
  induction l as [ | x l IH ]; intros.
  - hnf in Hsub. simpl in Hsub. injection Hsub as <-.
    destruct tc as [ni chn] eqn:Etc.
    (* TODO still repeating the proof in tc_detach_nodes_single? *)
    simpl in Echn_par. rewrite Echn_par in Hnodup.
    simpl in Hnodup. rewrite -> NoDup_cons_iff, <- ! flat_map_app, -> ! map_app, -> ! in_app_iff in Hnodup. 
    simpl in Hnodup. rewrite -> map_app, -> ! in_app_iff in Hnodup. destruct Hnodup as (Hnotin_tc & Hnodup).
    apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_pre & Hnodup & Hdj1).
    apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_ch & Hnodup_suf & Hdj2).
    setoid_rewrite -> in_app_iff in Hdj1.
    assert (forall ch', In ch' pre \/ In ch' suf -> ~ In (tc_roottid res) (map tc_roottid (tc_flatten ch'))) as Hnotin'.
    {
      intros ch' H Hn.
      specialize (Hdj1 (tc_roottid res)). specialize (Hdj2 (tc_roottid res)).
      rewrite -> map_flat_map_In in Hdj1, Hdj2.
      rewrite -> 1 in_map_iff in Hdj1, Hdj2.
      destruct H as [ H | H ].
      - apply Hdj1. 1: eauto. left. 
        exists res. split; auto. apply tc_flatten_self_in.
      - apply Hdj2; eauto.
        exists res. split; auto. apply tc_flatten_self_in.
    }
    assert (forall ch' : treeclock, In ch' pre \/ In ch' suf -> 
      tc_roottid ch' <> tc_roottid res) as Hnotin''.
    {
      intros ch' Hin'. apply Hnotin' in Hin'.
      intros E. rewrite <- E in Hin'. 
      (* TODO why this is repeating? *)
      apply False_ind, Hin', in_map, tc_flatten_self_in.
    }
    assert (tc_remove_ch (Node ni chn) (tc_roottid res) = Node ni (pre ++ suf)) as Eremovech.
    {
      simpl. f_equal. rewrite -> Echn_par, -> filter_app. simpl. 
      rewrite -> ! filter_all_true; auto.
      2-3: intros ch' Hin'; apply negb_true_iff, has_same_tid_false.
      3: specialize (Hnotin' _ (or_introl Hin')).
      2: specialize (Hnotin' _ (or_intror Hin')).
      2-3: intros EE; rewrite -> EE in Hnotin'; apply Hnotin', in_map, tc_flatten_self_in.
      unfold has_same_tid. 
      now destruct (eqdec (tc_roottid res) (tc_roottid res)).
    }
    rewrite -> Eremovech in Etc_pivot. simpl in Echn_par, Etc_pivot. subst tc_pivot.

    pose (lo:=[base.fmap tc_roottid (hd_error suf); base.fmap tc_roottid (hd_error (rev pre)); Some (tc_roottid tc)]).
    assert (Forall2 lnode_regalter [f_next_upd; f_prev_upd; f_par_upd] lo) as Hrega.
    {
      subst. subst lo.
      constructor. 1: apply tc_detach_next_upd_regalter.
      constructor. 1: apply tc_detach_prev_upd_regalter.
      constructor; auto. apply tc_detach_par_upd_regalter.
    }

    rewrite -> Echn_par in Hproj. hnf in Hproj.
    rewrite -> Foralltc_cons_iff, -> List.Forall_app, -> Forall_cons_iff in Hproj.
    split.
    + constructor.
      * simpl. apply proj1 in Hproj. simpl in Hproj.

      * admit.
    + rewrite Elnode'. eapply nodearray_proj_lnode_regalter_preserve. 
      2: apply Hrega. 1: tauto.
      (* strengthen *)
      assert (forall idx, In (Some idx) lo -> In idx (map tc_roottid (flat_map tc_flatten pre)) \/
        In idx (map tc_roottid (flat_map tc_flatten suf)) \/ idx = tc_roottid tc) as Htmp.
      {
        (* changed compared with below ... *)
        intros idx Hin. subst lo.
        simpl in Hin. destruct Hin as [ H | [H | [H | []]] ]; try eqsolve.
        1: destruct (hd_error suf) as [ next | ] eqn:E; simpl in H; try eqsolve.
        2: destruct (hd_error (rev pre)) as [ prev | ] eqn:E; simpl in H; try eqsolve.
        all: injection H as <-.
        1: right; left.
        2: left.
        all: apply in_map. 
        - destruct suf; simpl in E; try eqsolve. injection E as ->. 
          simpl. apply in_app, or_introl, tc_flatten_self_in.
        - destruct pre eqn:E'. 1: simpl in E; try eqsolve. 
          rewrite <- E' in *. assert (pre <> nil) as Htmp by eqsolve. clear E'.
          apply exists_last in Htmp. destruct Htmp as (pre'' & prev' & Htmp).
          rewrite -> Htmp, -> rev_app_distr in E. simpl in E. injection E as ->.
          rewrite -> Htmp, <- flat_map_app, -> in_app_iff.
          simpl. rewrite app_nil_r. apply or_intror, tc_flatten_self_in.
      }
      intros idx Hin. apply Htmp in Hin.
      destruct Hin as [ H | [ H | -> ]].
      * apply Hdj1 in H. eqsolve.
      * intros Hq. apply Hdj2 in Hq. eqsolve.
      * subst tc. destruct ni as (u, ?, ?). simpl in *. eqsolve.
  - destruct tc as [ni chn] eqn:Etc.
    hnf in Hsub. simpl in Hsub, Etc_pivot.
    destruct (nth_error chn x) as [ ch | ] eqn:Enth; try eqsolve.
    rewrite -> Etc_pivot.
    enough (is_tc_nodearray_proj lnode' (tc_locate_update ch l (tc_remove_ch tc_par (tc_roottid res))) /\
      is_tc_nodearray_proj lnode' res) as Hcon.
    + split; try tauto. destruct Hcon as (Hcon & _).
      constructor.
      * (* as long as the list of ni does not change ... *)
        simpl.
        admit.
      * apply nth_error_split in Enth.
        destruct Enth as (pre' & suf' & Echn & Elen).
        rewrite -> Echn, -> upd_Znth_char, -> List.Forall_app, -> Forall_cons_iff; auto.
        2: subst x; apply Zlength_correct.
        (*
        assert (Zlength pre' = Z.of_nat x) as Elen'.
        {
          (* list_solve is really useful here *)
          match goal with |- ?a = ?b => enough (Z.to_nat a = Z.to_nat b) by list_solve end.
          rewrite -> Nat2Z.id, <- Elen. apply ZtoNat_Zlength.
        }
        rewrite -> Echn, -> upd_Znth_char, -> List.Forall_app, -> Forall_cons_iff; auto.
        *)

        (* non-disjoint *)
        (* FIXME: so much repeat! *)
        pose (lo:=[base.fmap tc_roottid (hd_error suf); base.fmap tc_roottid (hd_error (rev pre)); Some (tc_roottid tc_par)]).
        assert (Forall2 lnode_regalter [f_next_upd; f_prev_upd; f_par_upd] lo) as Hrega.
        {
          subst. subst lo.
          constructor. 1: apply tc_detach_next_upd_regalter.
          constructor. 1: apply tc_detach_prev_upd_regalter.
          constructor; auto. apply tc_detach_par_upd_regalter.
        }

        (* strengthen *)
        assert (forall idx, In (Some idx) lo -> In idx (map tc_roottid (tc_flatten tc_par))) as Htmp.
        {
          intros idx Hin. subst lo.
          simpl in Hin. destruct Hin as [ H | [H | [H | []]] ]; try eqsolve.
          3: injection H as <-; apply in_map, tc_flatten_self_in.
          1: destruct (hd_error suf) as [ next | ] eqn:E; simpl in H; try eqsolve.
          2: destruct (hd_error (rev pre)) as [ prev | ] eqn:E; simpl in H; try eqsolve.
          all: injection H as <-; apply in_map.
          all: destruct tc_par; simpl in *; rewrite -> Echn_par.
          all: right; rewrite <- ! flat_map_app; simpl; rewrite -> ! in_app_iff; simpl.
          - right. right.
            destruct suf; simpl in E; try eqsolve. injection E as ->.
            simpl. apply in_app, or_introl, tc_flatten_self_in.
          - left.
            destruct pre eqn:E'. 1: simpl in E; try eqsolve. 
            rewrite <- E' in *. assert (pre <> nil) as Htmp by eqsolve. clear E'.
            apply exists_last in Htmp. destruct Htmp as (pre'' & prev' & Htmp).
            rewrite -> Htmp, -> rev_app_distr in E. simpl in E. injection E as ->.
            rewrite -> Htmp, <- flat_map_app, -> in_app_iff.
            simpl. rewrite app_nil_r. apply or_intror, tc_flatten_self_in.
        }
(*
        assert (forall idx,
          (forall next suf', suf = next :: suf' -> idx = tc_roottid next) \/
          (forall prev pre', pre = pre' ++ (prev :: nil) -> idx = tc_roottid prev) \/
          idx = tc_roottid tc_par -> In (Some idx) lo) as Htmp.
        {
          intros idx HH. subst lo. simpl.
*)
        assert (forall idx, In (Some idx) lo -> 
          ~ In idx (map tc_roottid (flat_map tc_flatten pre')) /\ 
          ~ In idx (map tc_roottid (flat_map tc_flatten suf'))) as Hnotin'.
        {
          intros idx HH. apply Htmp, in_map_iff in HH.
          destruct HH as (sub' & <- & HH).
          assert (In sub' (tc_flatten ch)) as Hsub'.
          { eapply subtc_trans. apply HH. apply subtc_witness_iff. eauto. }
          apply in_map with (f:=tc_roottid) in Hsub'.
          
          (* TODO this may be reusable, actually? *)
          assert (In tc_par (tc_flatten tc)) as Hsub''.
          { 
            eapply subtc_trans. 1: apply subtc_witness_iff; eauto. 
            apply subtc_chn. rewrite Etc, Echn. simpl. rewrite -> in_app_iff. simpl. eqsolve.
          }
          (*
          (* ouch. *)
          apply tid_nodup_Foralltc_id in Hnodup.
          eapply Foralltc_subtc in Hnodup. 2: subst tc; apply Hsub''.
          destruct tc_par as [ni0 chn0].
          (* TODO still repeating the proof in tc_detach_nodes_single? *)
          simpl in Echn_par. rewrite Echn_par in Hnodup.
          simpl in Hnodup. rewrite -> NoDup_cons_iff, <- ! flat_map_app, -> ! map_app, -> ! in_app_iff in Hnodup. 
          simpl in Hnodup. rewrite map_app in Hnodup. destruct Hnodup as (Hnotin_tc & Hnodup).
          apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_pre & Hnodup & Hdj1).
          apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_ch & Hnodup_suf & Hdj2).
          *)
          rewrite Echn in Hnodup.
          simpl in Hnodup. rewrite -> NoDup_cons_iff, <- ! flat_map_app, -> ! map_app, -> ! in_app_iff in Hnodup. 
          simpl in Hnodup. rewrite map_app in Hnodup. destruct Hnodup as (Hnotin_tc & Hnodup).
          apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_pre & Hnodup & Hdj1).
          apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_ch & Hnodup_suf & Hdj2).
          setoid_rewrite -> in_app_iff in Hdj1.
          split.
          - intros Hq. apply Hdj1 in Hq. eqsolve.
          - now apply Hdj2. 
        }
        hnf in Hproj. rewrite <- Foralltc_idempotent in Hproj.
        split; [ | split ]; auto.
        --apply Forall_forall. intros ch0 Hin0.
          subst lnode'. eapply nodearray_proj_lnode_regalter_preserve. 
          2: apply Hrega. 1: eapply Foralltc_subtc; [ | apply Hproj ].
          1: apply subtc_chn; subst chn; simpl; rewrite in_app_iff; auto.
          intros idx Hinlo HH. 
          pose proof (map_flat_map_In_conv _ _ _ _ _ Hin0 HH). 
          now apply Hnotin' in H.
        --apply Forall_forall. intros ch0 Hin0.
          subst lnode'. eapply nodearray_proj_lnode_regalter_preserve. 
          2: apply Hrega. 1: eapply Foralltc_subtc; [ | apply Hproj ].
          1: apply subtc_chn; subst chn; simpl; rewrite in_app_iff; simpl; auto.
          intros idx Hinlo HH. 
          pose proof (map_flat_map_In_conv _ _ _ _ _ Hin0 HH). 
          now apply Hnotin' in H.
    + eapply IH.
      2: apply Hsub.
      2: apply Echn_par.
      all: eauto.
      all: apply nth_error_In in Enth.
      * simpl in Hnodup. rewrite -> NoDup_cons_iff in Hnodup.
        apply tid_nodup_chn_ch with (chn:=chn); eqsolve.
      * hnf in Hproj. rewrite -> Foralltc_cons_iff in Hproj.
        eapply proj2, Forall_forall in Hproj. 2: apply Enth.
        auto.
Admitted.

*)

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

(*
Fact tc_detach_update_proj tc 
  (* (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))  *)
  (idx : nat) 
  tc_pivot tc_sub
  (Hres : tc_detach_nodes (Node (mkInfo idx 0%nat 0%nat) nil) tc = 
    (tc_pivot, (tc_sub :: nil)))
  (Hneq : idx <> tc_roottid tc) 
  res (Hres : tc_getnode idx tc = Some res) :
  exists tc_par, subtc tc_par tc /\ In res (tc_rootchn tc_par).
Proof.
*)  

(*

Lemma body_detach_from_neighbors: 
  semax_body Vprog Gprog f_detach_from_neighbors detach_from_neighbors_spec.
Proof.
  saturate_lemmas.

  start_function.
  (* preprocess *)
  match goal with HH : context[tc_getnode idx tc] |- _ =>
    rename HH into Hres; pose proof (tc_getnode_has_tid _ _ _ Hres) as (Hin_res & <-) end.
  pose proof Hres as Hpar. apply subtc_has_parent in Hpar; auto.
  destruct Hpar as (tc_par & Hin_par & Hres_ch).
  pose proof (subtc_subtc_witness _ _ Hin_par) as (l & Hin_par').
  match goal with HH : context[tc_detach_nodes] |- _ =>
    rename HH into Edetach; pose proof Edetach as Etc_pivot end.
  erewrite -> tc_detach_nodes_single in Etc_pivot.
  3: apply Hin_par'. all: auto.
  (* ... later, can use the tc_locate_update_remove_ch_proj *)
  apply f_equal with (f:=fst) in Etc_pivot. simpl in Etc_pivot.
  match goal with H1 : context[is_tc_nodearray_proj_full], 
    H2 : context[nodearray_emptypart] |- _ => 
    rename H1 into Hproj1; rename H2 into Hproj2; 
    pose proof (nodearray_proj_regular _ _ Hproj1 Hproj2) as Hreg end.
  rewrite -> Forall_forall_Znth, -> H1 in Hreg.
  (* obtain node_payload *)
  epose proof (Hreg (Z.of_nat (tc_roottid tc_sub)) ?[Goalq]) as 
    (next & prev & par & ? & Es & Hnext & Hprev & Hpar & ?).
  [Goalq]: lia.
  repable_signed_gen (next :: prev :: par :: nil).
  (* read correct *)
  pose proof (in_split _ _ Hres_ch) as (pre & suf & Echn_par).
  destruct Hproj1 as (Hroot & Hproj1). 
  assert (is_tc_nodearray_proj lnode tc_par) as Hprojchn_par.
  { 
    hnf in Hproj1. rewrite <- Foralltc_idempotent,
      -> Foralltc_Forall_subtree, -> Forall_forall in Hproj1.
    now apply Hproj1 in Hin_par.
  }
  pose proof Hprojchn_par as Es'. eapply Foralltc_self, nodearray_proj_read_correct in Es'.
  2: apply Echn_par. 2: auto.
  rewrite -> Es, -> node_payload_cmp with (dim:=dim) in Es'; try lia.
  2-5: admit.
  (* destruct Es' as (Elch & Erch & Epar & ?). *)
  destruct Es' as (-> & -> & -> & ->).
  (* TODO would certainly need id distinction *)
  (* obtain parent's node_payload *)
  epose proof (Hreg (Z.of_nat (tc_roottid tc_par)) ?[Goalq]) as 
    (x & x0 & x1 & headch_par & Es_par & ? & ? & ? & Hheadch_par).
  [Goalq]: lia.
  (* read correct *)
  assert (headch_par = tcs_head_Z (pre ++ tc_sub :: suf)) as Eheadch_par.
  {
    (* TODO extract this? *)
    destruct tc as [ni chn]. hnf in Hin_par. destruct Hin_par as [ <- | Hin_par ].
    - simpl in Echn_par. subst chn. 
      apply nth_error_Znth_result in Hroot. 
      rewrite -> Hroot, -> node_payload_cmp with (dim:=dim) in Es_par; try lia.
      1: simpl in Es_par; unfold tc_headch_Z, tcs_head_Z in *; eqsolve.
      simpl. admit.
    - admit.
  }
  repable_signed_gen (headch_par :: nil).

  (* now forward *)
  array_focus (Z.of_nat (tc_roottid tc_sub)) plnode witheqn Etmp.
  rewrite -> Etmp.
  rewrite -> Es.
  unfold node_payload.
  forward. forward. forward. forward.
  forward. 
  rewrite_sem_add_ptr_int. 
  array_unfocus witheqn Etmp. 2: now rewrite -> Es.
  array_focus (Z.of_nat (tc_roottid tc_par)) plnode witheqn Etmp.
  rewrite -> Etmp.
  rewrite -> Es_par.
  unfold node_payload.
  forward.

  (* try exhaustive discussion first *)
  apply semax_if_seq. forward_if.
  {
    (* update headch of par *)
    assert (pre = nil) as Epre.
    {
      admit.
    }
    forward. 
    fold (tcs_head_Z suf). fold (node_payload x x0 x1 (tcs_head_Z suf)).
    replace (node_payload x x0 x1 (tcs_head_Z suf)) with
      (node_struct_upd_headch (tcs_head_Z suf) (Znth (Z.of_nat (tc_roottid tc_par)) lnode)).
    2: now rewrite Es_par.
    array_unfocus' witheqn Etmp.

    forward_if.
    {
      fold (tcs_head_Z suf) in H9.
      rewrite -> neg_repr in H9. apply repr_inj_signed' in H9; auto.
      destruct suf as [ | next suf' ] eqn:E.
      1: simpl in *; unfold default_nodefield; contradiction.

      rewrite <- ! E in *.
      assert (tcs_head_Z suf = Z.of_nat (tc_roottid next)) as Enext by now rewrite E.
      (* assert (0 <= tcs_head_Z suf) as Hnext' by lia. *)
      forward. forward.
      array_focus (tcs_head_Z suf) plnode witheqn Etmp2.
      rewrite -> Etmp2.
      (* obtain next's node_payload *)
      epose proof (Hreg (tcs_head_Z suf) ?[Goalq]) as 
        (y & prev_next & y0 & y1 & Es_next & ? & Hprev_next & ? & ?).
      [Goalq]: lia.
      rewrite -> Znth_upd_Znth_diff. 2: admit.
      rewrite -> Es_next.
      unfold node_payload.
      rewrite_sem_add_ptr_int.
      forward.
      fold (tcs_head_Z (rev pre)). fold (node_payload y (tcs_head_Z (rev pre)) y0 y1).
      replace (node_payload y (tcs_head_Z (rev pre)) y0 y1) with
        (node_struct_upd_prev (tcs_head_Z (rev pre)) (Znth (tcs_head_Z suf) lnode)).
      2: now rewrite Es_next.

      EExists.
      entailer!. (* expecting eauto refl *)
      2: array_unfocus' witheqn Etmp2; apply derives_refl.
      split. 1: list_solve.
      unfold is_tc_nodearray_proj_full.
      match goal with |- ?A /\ (?BB /\ ?B) /\ ?C => enough (BB /\ ((B /\ A) /\ C)) by tauto end.
      split; [ | split ].
      - admit.
      - evar (lnode' : list (reptype t_struct_node)).
        enough (is_tc_nodearray_proj lnode' tc_pivot /\ is_tc_nodearray_proj lnode' tc_sub).
        2:{
          subst lnode'. eapply tc_locate_update_remove_ch_proj; eauto.
          admit.
        }
        match goal with |- (is_tc_nodearray_proj ?lnode'' _) /\ _ => 
          enough (lnode'' = lnode') by (subst lnode'; eqsolve) end.
        subst pre suf lnode'.
        simpl. unfold tc_detach_prev_upd. simpl. f_equal. f_equal.
        rewrite -> Znth_upd_Znth_diff; auto.
        admit.
      - admit.
    }
    {
      fold (tcs_head_Z suf) in H9.
      rewrite -> neg_repr in H9. apply repr_inj_signed in H9; auto.
      destruct suf as [ | next suf' ] eqn:E.
      2: simpl in *; unfold default_nodefield; lia.
      forward.

      match goal with |- context[data_at Tsh (tarray t_struct_node dim) ?lnode' plnode] =>
        Exists lnode' end.
      entailer!.
      match goal with |- context[tc_locate_update ?a ?b ?c] => 
        remember (tc_locate_update a b c) as tc_pivot eqn:Etc_pivot | _ => idtac end.
      unfold is_tc_nodearray_proj_full.
      match goal with |- ?A /\ (?BB /\ ?B) /\ ?C => enough (BB /\ ((B /\ A) /\ C)) by tauto end.
      split; [ | split ].
      - admit.
      - evar (lnode' : list (reptype t_struct_node)).
        enough (is_tc_nodearray_proj lnode' tc_pivot /\ is_tc_nodearray_proj lnode' tc_sub).
        2:{
          subst lnode'. eapply tc_locate_update_remove_ch_proj; eauto.
          (* TODO why no admit here? *)
        }
        match goal with |- (is_tc_nodearray_proj ?lnode'' _) /\ _ => 
          enough (lnode'' = lnode') by (subst lnode'; eqsolve) end.
        subst lnode'. subst.
        simpl. unfold tc_detach_prev_upd. now simpl.
      - admit.
    }
  }
  {
    (* unfocus first *)
    fold (node_payload x x0 x1 headch_par).
    rewrite <- Es_par.
    array_unfocus witheqn Etmp.

    assert (pre <> nil) as Hpre by (destruct pre; auto).
    apply exists_last in Hpre. destruct Hpre as (pre' & prev & Epre).
    assert (exists q' pre'', q' :: pre'' = pre' ++ [prev]) as (q' & pre'' & Epre').
    { destruct pre as [ | q pre'' ]; try contradiction. eauto. }
    assert (tcs_head_Z (rev pre) = Z.of_nat (tc_roottid prev)) as Eprev
      by (now rewrite -> Epre, -> rev_app_distr). 
    forward. forward.
    array_focus (tcs_head_Z (rev pre)) plnode witheqn Etmp2.
    rewrite -> Etmp2.
    (* obtain prev's node_payload *)
    epose proof (Hreg (tcs_head_Z (rev pre)) ?[Goalq]) as 
      (next_prev & z & z0 & z1 & Es_prev & Hnext_prev & ? & ? & ?).
    [Goalq]: lia.
    rewrite -> Es_prev.
    unfold node_payload.
    rewrite_sem_add_ptr_int. fold (tcs_head_Z (rev pre)).
    (* update and unfocus *)
    forward.
    fold (tcs_head_Z suf). fold (node_payload (tcs_head_Z suf) z z0 z1).
    replace (node_payload (tcs_head_Z suf) z z0 z1) with
      (node_struct_upd_next (tcs_head_Z suf) (Znth (tcs_head_Z (rev pre)) lnode)).
    2: now rewrite Es_prev.
    array_unfocus' witheqn Etmp2. clear Etmp2.

    (* TODO much repeating as expected *)
    forward_if.
    {
      fold (tcs_head_Z suf) in H12.
      rewrite -> neg_repr in H12. apply repr_inj_signed' in H12; auto.
      destruct suf as [ | next suf' ] eqn:E.
      1: simpl in *; unfold default_nodefield; contradiction.

      rewrite <- ! E in *.
      assert (tcs_head_Z suf = Z.of_nat (tc_roottid next)) as Enext by now rewrite E.
      (* assert (0 <= tcs_head_Z suf) as Hnext' by lia. *)
      forward. forward.
      array_focus (tcs_head_Z suf) plnode witheqn Etmp2.
      rewrite -> Etmp2.
      (* obtain next's node_payload *)
      epose proof (Hreg (tcs_head_Z suf) ?[Goalq]) as 
        (y & prev_next & y0 & y1 & Es_next & ? & Hprev_next & ? & ?).
      [Goalq]: lia.
      rewrite -> Znth_upd_Znth_diff. 2: admit.
      rewrite -> Es_next.
      unfold node_payload.
      rewrite_sem_add_ptr_int.
      forward.
      fold (tcs_head_Z (rev pre)). fold (node_payload y (tcs_head_Z (rev pre)) y0 y1).
      replace (node_payload y (tcs_head_Z (rev pre)) y0 y1) with
        (node_struct_upd_prev (tcs_head_Z (rev pre)) (Znth (tcs_head_Z suf) lnode)).
      2: now rewrite Es_next.

      EExists.
      entailer!. (* expecting eauto refl *)
      2: array_unfocus' witheqn Etmp2; apply derives_refl.
      split. 1: list_solve.
      unfold is_tc_nodearray_proj_full.
      match goal with |- ?A /\ (?BB /\ ?B) /\ ?C => enough (BB /\ ((B /\ A) /\ C)) by tauto end.
      split; [ | split ].
      - admit.
      - evar (lnode' : list (reptype t_struct_node)).
        enough (is_tc_nodearray_proj lnode' tc_pivot /\ is_tc_nodearray_proj lnode' tc_sub).
        2:{
          subst lnode'. eapply tc_locate_update_remove_ch_proj; eauto.
          admit.
        }
        match goal with |- (is_tc_nodearray_proj ?lnode'' _) /\ _ => 
          enough (lnode'' = lnode') by (subst lnode'; eqsolve) end.
        subst pre suf lnode'.
        simpl. unfold tc_detach_prev_upd, tc_detach_par_upd, tc_detach_next_upd. 
        rewrite -> ! rev_app_distr. simpl. rewrite <- ! Epre'. f_equal. f_equal.
        rewrite -> Znth_upd_Znth_diff; auto.
        admit.
      - admit.
    }
    {
      fold (tcs_head_Z suf) in H12.
      rewrite -> neg_repr in H12. apply repr_inj_signed in H12; auto.
      destruct suf as [ | next suf' ] eqn:E.
      2: simpl in *; unfold default_nodefield; lia.
      forward.

      match goal with |- context[data_at Tsh (tarray t_struct_node dim) ?lnode' plnode] =>
        Exists lnode' end.
      entailer!.
      match goal with |- context[tc_locate_update ?a ?b ?c] => 
        remember (tc_locate_update a b c) as tc_pivot eqn:Etc_pivot | _ => idtac end.
      unfold is_tc_nodearray_proj_full.
      match goal with |- ?A /\ (?BB /\ ?B) /\ ?C => enough (BB /\ ((B /\ A) /\ C)) by tauto end.
      split; [ | split ].
      - admit.
      - evar (lnode' : list (reptype t_struct_node)).
        enough (is_tc_nodearray_proj lnode' tc_pivot /\ is_tc_nodearray_proj lnode' tc_sub).
        2:{
          subst lnode'. eapply tc_locate_update_remove_ch_proj; eauto.
          (* TODO why no admit here? *)
        }
        match goal with |- (is_tc_nodearray_proj ?lnode'' _) /\ _ => 
          enough (lnode'' = lnode') by (subst lnode'; eqsolve) end.
        subst lnode'.
        simpl. unfold tc_detach_prev_upd, tc_detach_par_upd, tc_detach_next_upd. 
        rewrite -> ! rev_app_distr. simpl. rewrite <- ! Epre'. reflexivity.
      - admit.
    }
  }
Admitted.

*)

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
    (* tc.join(tc') = tc *)
    assert (tc_join tc tc' = tc) as Ejoin.
    { 
      destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
      unfold tc_join. simpl.
      simpl in Erootid, H3. subst z.
      unfold tc_getclk in *.
      simpl in H3 |- *. destruct (eqdec z' z'); try eqsolve.
      simpl in H3 |- *. apply Nat.leb_le in H3. now rewrite -> H3.
    }
    (* do some grouping *)
    (* seems like doing two freeze will be troublesome *)
    freeze (4 :: 5 :: 6 :: 7 :: nil) group'.
    gather_SEP' (1 :: 2 :: 3 :: 4 :: nil).
    (* freeze (1 :: 2 :: 3 :: 4 :: nil) group. *)
    forward.
    apply sepcon_derives.
    - unfold treeclock_rep, treeclock_payload.
      Exists lclk lnode lstk.
      entailer!.
      all: now rewrite -> ! Ejoin.
    - thaw group'. simpl.
      unfold treeclock_rep, treeclock_payload.
      Exists lclk' lnode' lstk'.
      entailer!.
  }

  match goal with H : _ |- _ => rewrite -> Nat2Z.inj_iff in H; rename H into Hrootid end.
  forward. forward. forward.

  (* 1:{ entailer!. unfold is_pos_tshort, short_max_signed in *. 
    rewrite Int.signed_repr; try lia. 
    rewrite -> ! two_power_pos_nat. simpl. lia.
  } *)

  array_focus (Z.of_nat (tc_roottid tc')) plclk' witheqn Etmp.
  (* replacing the following thing *)
  (* 
  sep_apply (SingletonHole.array_with_hole_intro Tsh _ 
    (Z.of_nat (tc_roottid tc')) dim lclk'); try lia.
  match goal with |- context[field_address (tarray ?a ?size) (SUB ?b) ?c] => 
    assert (field_address (tarray a size) (SUB b) c = offset_val (sizeof a * b) c) as Etmp
    by (apply arr_field_address; try lia; try assumption) end. 
  *)

  (* match goal with |- context[field_address (tarray ?a ?size) (SUB ?b) ?c] => 
    remember (field_address a b c) as ad eqn:Earroff end.
  pose proof Earroff as Etmp.
  (* need compatible *)
  rewrite arr_field_address in Etmp; try lia; try assumption. *)

  rewrite_sem_add_ptr_int.
  (*
  simpl sem_binary_operation'.
  (* pre *) assert_PROP (isptr plclk') as Hip by entailer.
  (* need isptr *)
  rewrite -> sem_add_pi'; auto; try lia.
  *)

  (*
  unfold sem_add_ptr_int.
  replace (complete_type cenv_cs (Tstruct _Clock noattr)) with true by now compute.

  (* ? *)
  assert_PROP (isptr plclk') as Hip by entailer.
  destruct plclk' eqn:Eplclk' in Etmp, Hip |- *; hnf in Hip; try contradiction. clear Hip.
  simpl.
  unfold Ptrofs.of_ints.
  rewrite Int.signed_repr; try lia.
  2:{ unfold is_pos_tint in *. split; try lia. 
    pose proof Int.min_signed_neg. transitivity 0; lia.
  }
  rewrite ptrofs_mul_repr.
  simpl in Etmp.
  *)
  (* Intros. *)
  pose proof (Foralltc_self _ _ Hca_tc') as Etmp2. cbn in Etmp2.
  rewrite -> Etmp.
  read_clock witheqn Etmp2. clear Etmp2.
  (* replacing *)
  (*
  unfold clock_payload in Etmp2.
  rewrite -> Etmp2.
  (* unfold clock_payload. *)
  (* if do rewrite -> Etmp earlier then simpl will unfold "sizeof", which is troublesome *)
  (* here, temp _zprime_clocks must be the shape of offset_val; otherwise it cannot forward *)
  forward.
  rewrite <- Etmp2.
  fold (clock_payload (Z.of_nat (tc_rootclk tc')) (Z.of_nat (tc_rootaclk tc'))) in Etmp2.
  *)
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

  (*
  simpl.
  (* pre *) assert_PROP (isptr plnode) as Hip0 by entailer.
  (* pre *) assert_PROP (isptr plclk) as Hip1 by entailer.
  rewrite -> ! sem_add_pi'; auto; try lia.
  *)

  (* forward_if is really tedious. *)
  (*
  forward_if (temp _t'1 (Val.of_bool (ssrbool.isSome (tc_getnode (tc_roottid tc') tc)))).
  { forward.
    entailer!.
    apply Nat2Z.inj in H18.
    destruct tc as [(?, ?, ?) ?]. simpl in H18. rewrite -> H18.
    simpl. destruct (eqdec (tc_roottid tc') (tc_roottid tc')); simpl; auto; try contradiction.
  }
  { forward_call.
    Intros vret.
    forward.
    destruct vret; entailer!.
    - destruct (tc_getnode (tc_roottid tc') tc) as [ res | ] eqn:E; simpl; auto.
      destruct tc as [ (u, ?, ?) [ | ] ]; simpl in E, H19; try eqsolve.
      destruct (eqdec u (tc_roottid tc')) as [ -> | ]; simpl in E; eqsolve.
    - destruct (tc_getnode (tc_roottid tc') tc) as [ res | ] eqn:E; simpl; auto.
      rewrite -> orb_true_r in H19. eqsolve.
  }
  *)

  pose proof Hcb_tc' as Hcb_tc'root. 
  apply Foralltc_self, proj1 in Hcb_tc'root.
  assert (Z.of_nat (tc_getclk (tc_roottid tc') tc) <= Int.max_signed) as Hcb_tc'root_getclk.
  {
    unfold tc_getclk.
    destruct (tc_getnode (tc_roottid tc') tc) as [ res | ] eqn:E; try lia.
    eapply tc_getnode_res_Foralltc in E. 2: apply Hcb_tc. lia.
  }

  forward_if.
  {
    (* inrange request *)
    match goal with HH : _ >= _ |- _ => rename HH into Hge end.
    (* early return; TODO repeating above? maybe still need to move root eq check here *)
    (* tc.join(tc') = tc *)
    assert (tc_join tc tc' = tc) as Ejoin.
    { 
      destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
      unfold tc_join. simpl.
      simpl in Hge. 
      match type of Hge with (Z.of_nat ?a >= Z.of_nat ?b) => assert (b <= a)%nat as Hle by lia end.
      apply Nat.leb_le in Hle. now rewrite -> Hle.
    }
    (* made shorter *)
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
  2:{ subst vret. unfold node_is_null_as_bool. destruct tc as [(u, ?, ?) [ | ]]; simpl; auto.
    simpl in Hrootid. apply Nat.eqb_neq in Hrootid. now rewrite -> Nat.eqb_sym, -> Hrootid.
  }

  (* before going forward, prepare for the node to be detached and change the representation format *)
  pose (pureroot_tc':=Node (tc_rootinfo tc') nil).
  pose (sub:=(match tc_getnode (tc_roottid tc') tc with Some res => res | None => Node (mkInfo (tc_roottid tc') 0%nat 0%nat) nil end)).
  assert (tc_roottid sub = tc_roottid tc') as Eid.
  {
    destruct (tc_getnode (tc_roottid tc') tc) as [ res | ] eqn:Eres; auto.
    now apply tc_getnode_has_tid in Eres.
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
    pose proof (tc_detach_nodes_single _ Hnodup res _ _ Hsub) as Htmp.
    (* TODO maybe streamline this specialize? *)
    simpl tc_rootchn in Htmp. rewrite -> in_app_iff in Htmp. simpl In in Htmp.
    specialize (Htmp (or_intror (or_introl eq_refl))).
    rewrite -> tc_remove_ch_when_nodup in Htmp.
    (* TODO streamline this *)
    2: rewrite -> tid_nodup_Foralltc_id in Hnodup; eapply Foralltc_subtc in Hsub'; [ | apply Hnodup ]; assumption.
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
    unfold tc_roottid. rewrite <- 2 map_map with (g:=info_tid) (f:=tc_rootinfo).
    apply Permutation_map.
    etransitivity. 1: apply tc_detach_nodes_dom_partition.
    rewrite Htmp. simpl. rewrite app_nil_r.
    rewrite ! map_app. apply Permutation_app_comm.
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
      now rewrite -> tc_getnode_subtc_iff, -> Eres in Hin'.
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
  (* cbv delta [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] beta iota. *)
  deadvars. clear vret.
  unfold tc_subroot_rep, clock_rep, clock_payload. rewrite -> ! Eid. Intros.
  forward. forward. forward. 
  rewrite_sem_add_ptr_int.
  (* since the representation format is not array, it is not very easy to read (tc_rootclk tc) ... *)
  unfold tc_rep, tc_root_rep, clock_rep, clock_payload.
  Intros.
  pose proof (tc_detach_nodes_fst_rootinfo_same (pureroot_tc' :: nil) tc) as Htmp.
  pose proof (tc_rootinfo_tid_inj _ _ Htmp) as Htmp_tid.
  pose proof (tc_rootinfo_clk_inj _ _ Htmp) as Htmp_clk.
  pose proof (tc_rootinfo_aclk_inj _ _ Htmp) as Htmp_aclk.
  subst tc_d.
  rewrite Htmp_tid. forward. rewrite Htmp_clk. forward.

  (* we may possibly use the local spec here, but anyway *)
  pose (sub':=Node (mkInfo (tc_roottid tc') (tc_rootclk tc') (tc_rootclk tc)) (tc_rootchn sub)).
  (* have to change clk & aclk of sub *)
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

  (* turn to the initial partial join, and fold *)
  thaw Fr. 
  cbv delta [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] beta iota.
  deadvars.
  simpl tc_locate_update.
  subst sub'.
  remember (Node _ (_ :: _)) as tc_join0 eqn:E0.
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
  unfold tc_rep.
  sep_apply tc_rep_and_bag2array.
  1:{
    admit.
  }
  Intros lnode0 lclk0.

(*
  
*)

  (*
  forward_if.
  { destruct vret.
    1:{ unfold eval_unop in H24. simpl in H24. apply typed_true_tint_Vint in H24. eqsolve. }
    destruct (tc_getnode (tc_roottid tc') tc) as [ res | ] eqn:Eres; try eqsolve.
    array_focus (Z.of_nat (tc_roottid tc')) plclk witheqn Etmp.
    rewrite -> Etmp.
    pose proof Eres as Eclock.
    apply (tc_getnode_res_Foralltc Hca_tc) in Eclock.
    destruct Eclock as (Eclock & Eid_res). 
    rewrite -> Eid_res in Eclock.
    read_clock witheqn Eclock. clear Eclock.
    array_unfocus witheqn Etmp.

    forward_if.
    {
      pose proof Eres as Ecb.
      apply (tc_getnode_res_Foralltc Hcb_tc) in Ecb.
      pose proof (Foralltc_self _ _ Hcb_tc') as Hcb_tc'root. simpl in Hcb_tc'root.
      rewrite -> ! Int.signed_repr, <- Nat2Z.inj_ge in H25; try lia.
      replace (tc_rootclk res) with (tc_getclk (tc_roottid tc') tc) in H25
        by (unfold tc_getclk; now rewrite Eres).
      (* early return; TODO repeating above? maybe still need to move root eq check here *)
      (* tc.join(tc') = tc *)
      assert (tc_join tc tc' = tc) as Ejoin.
      { 
        destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
        unfold tc_join. simpl.
        (* ..? *)
        unfold tc_getclk in H25 |- *. simpl in H25, Eres |- *. rewrite -> Eres in H25 |- *.
        assert (clk_z' <= tc_rootclk res)%nat as Hle by lia.
        apply Nat.leb_le in Hle. now rewrite -> Hle.
      }
      (* do some grouping *)
      (* seems like doing two freeze will be troublesome *)
      freeze (3 :: 5 :: 6 :: 7 :: nil) group'.
      gather_SEP' (1 :: 2 :: 3 :: 4 :: nil).
      (* freeze (1 :: 2 :: 3 :: 4 :: nil) group. *)
      forward.
      apply sepcon_derives.
      - unfold treeclock_rep, treeclock_payload.
        Exists lclk_ptrs lnode_ptrs lclk lnode lstk.
        entailer!.
        all: now rewrite -> ! Ejoin.
      - thaw group'. simpl.
        unfold treeclock_rep, treeclock_payload.
        Exists lclk_ptrs' lnode_ptrs' lclk' lnode' lstk'.
        entailer!.
    }
    { Show.
  }
  *)

  (* change into another lnode *)

Abort.

End Main_Proof.
