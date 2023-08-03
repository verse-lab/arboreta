Require Import VST.floyd.proofauto.
Require Import distributedclocks.clocks.treeclock.
From distributedclocks.vst Require Import treeclock_clight util_vst.
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

Definition is_pos_tint z : Prop := 0 <= z <= Int.max_signed.
(* planned not to use *)
(* Definition is_pos_tshort z : Prop := 0 <= z <= short_max_signed. *)

Definition clock_payload (clk aclk : Z) : reptype t_struct_clock :=
  (Vint (Int.repr clk), Vint (Int.repr aclk)).

Definition clock_rep (clk aclk : Z) (p : val) : mpred :=
  !! (is_pos_tint clk) && !! (is_pos_tint aclk) &&
  data_at Tsh t_struct_clock (clock_payload clk aclk) p.

Definition node_payload (lch rch par headch : Z) : reptype t_struct_node :=
  (Vint (Int.repr rch), 
    (Vint (Int.repr lch), 
      (Vint (Int.repr par), Vint (Int.repr headch)))).

Definition node_rep (lch rch par headch : Z) (p : val) : mpred :=
  (* !! (is_pos_tshort lch) && !! (is_pos_tshort rch) &&
  !! (is_pos_tshort par) && !! (is_pos_tshort headch) && *)
  !! (is_pos_tint lch) && !! (is_pos_tint rch) &&
  !! (is_pos_tint par) && !! (is_pos_tint headch) &&
  data_at Tsh t_struct_node (node_payload lch rch par headch) p.

(* from tree to its array presentation *)
(* Fixpoint tc_clockarray_proj (tc : treeclock)  *)

(* descriptive? *)

#[export] Instance nat_EqDec : EqDec nat.
Proof. constructor. apply Nat.eq_dec. Qed.

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

Definition is_tc_clockarray_proj (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  Foralltc (fun t => nth_error l (tc_roottid t) = 
    Some (clock_payload (Z.of_nat (tc_rootclk t)) (Z.of_nat (tc_rootaclk t)))) tc.

Definition clockarray_emptypart (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  forall n np, tc_getnode n tc = None -> nth_error l n = Some np -> 
    np = clock_payload 0%Z 0%Z.

(* TODO could also be per-field description so that there will be only one branch *)

(* typically requires that default_nodefield <= 0 *)
Definition default_nodefield := (-1)%Z.

Definition default_nodestruct := node_payload default_nodefield default_nodefield default_nodefield default_nodefield.

Definition tc_headch_Z (tc : @treeclock nat) : Z := 
  match tc_rootchn tc with nil => default_nodefield | ch :: _ => Z.of_nat (tc_roottid ch) end.

Global Arguments tc_headch_Z _/.

Definition is_tc_nodearray_proj_chnaux (par : nat) (l : list (reptype t_struct_node)) :
  forall (lch : Z) (chn : list treeclock), Prop := 
  fix aux lch chn {struct chn} : Prop := 
  match chn with
  | nil => True
  | ch :: chn' => 
    (* let tmp := aux (Z.of_nat (tc_roottid ch)) chn' in  *)
    nth_error l (tc_roottid ch) = 
    Some (node_payload lch 
      (match chn' with nil => default_nodefield | ch' :: _ => (Z.of_nat (tc_roottid ch')) end) 
      (Z.of_nat par) (tc_headch_Z ch)) /\
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

Definition nodearray_emptypart (l : list (reptype t_struct_node)) (tc : @treeclock nat) : Prop :=
  forall n np, tc_getnode n tc = None -> nth_error l n = Some np -> np = default_nodestruct.

Definition treeclock_payload (dim rootid : Z) (clockarr nodearr : val) 
  (stk : val) (top : Z) : reptype t_struct_treeclock :=
  (Vint (Int.repr dim), (Vint (Int.repr rootid), (clockarr, (nodearr, 
    (stk, Vint (Int.repr top)))))).

(* sometimes the treeclock corresponds to an empty tree, but do not consider it for now *)

(* factor the dim out; it should not change during the operation? *)
Definition treeclock_rep (dim : Z) (tc : @treeclock nat) (plclk plnode : val) 
  (plstk : val) (top : Z) p : mpred :=
  (* EX dim : Z,  *)
  EX lclk_ptrs : list val, 
  EX lnode_ptrs : list val, 
  EX lclk : list (reptype t_struct_clock), 
  EX lnode : list (reptype t_struct_node), 

  EX lstk : list val, 

  (* this is necessary in the current setting, since the root may not appear in the node array *)
  !! (Z.of_nat (tc_roottid tc) < dim) &&
  !! (Zlength lclk_ptrs = dim) && !! (Zlength lclk = dim) &&
  !! (Zlength lnode_ptrs = dim) && !! (Zlength lnode = dim) &&
  !! (is_tc_clockarray_proj lclk tc) && !! (clockarray_emptypart lclk tc) &&
  !! (is_tc_nodearray_proj_full lnode tc) && !! (nodearray_emptypart lnode tc) &&
  (* TODO this should be subsumed? *)
  (* !! (Foralltc (fun t => Z.of_nat (tc_roottid t) < dim) tc) && *)
  data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tc_roottid tc)) 
    plclk plnode plstk top) p * 
  data_at Tsh (tarray t_struct_clock dim) lclk plclk *
  data_at Tsh (tarray t_struct_node dim) lnode plnode *
  (* data_at Tsh (tarray tshort dim) lstk plstk. *)
  data_at Tsh (tarray tint dim) lstk plstk.

(* simple bounded properties *)
(* TODO should I use Z.< instead? *)

Fact is_tc_nodearray_proj_chnaux_tid_bounded lnode par lch chn (Hproj : is_tc_nodearray_proj_chnaux par lnode lch chn) :
  Forall (fun tc' => Z.of_nat (tc_roottid tc') < Zlength lnode) chn.
Proof.
  revert lnode lch Hproj.
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
  revert lnode Hproj HH.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in HH.
  apply Foralltc_cons_iff in Hproj. destruct Hproj as (Hchn & Hproj). 
  constructor; simpl; auto.
  apply is_tc_nodearray_proj_chnaux_tid_bounded in Hchn.
  rewrite -> Forall_forall in IH, Hproj, Hchn |- *.
  intros ch Hin. specialize (Hproj _ Hin). specialize (Hchn _ Hin). apply IH; auto.
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

Fact is_tc_nodearray_proj_chnaux_regular lnode par lch chn (Hproj : is_tc_nodearray_proj_chnaux par lnode lch chn)
  (* dim (Hlen : Zlength lnode = dim)  *)
  (Hu : Z.of_nat par < Zlength lnode) (Hlch : default_nodefield <= lch < Zlength lnode)
  (Hchn : Forall (fun ch => default_nodefield <= tc_headch_Z ch < Zlength lnode) chn) :
  Forall (fun tc' => node_struct_regular (Zlength lnode) (Znth (Z.of_nat (tc_roottid tc')) lnode)) chn.
Proof.
  revert lch lnode Hu Hproj Hlch Hchn. 
  induction chn as [ | ch chn IH ]; intros; constructor; simpl in Hproj.
  - hnf.
    match type of Hproj with _ = Some (node_payload ?z1 ?z2 ?z3 ?z4) /\ _ => 
      exists z1, z2, z3, z4 end.
    split. 1: now apply proj1, nth_error_Znth_result in Hproj.
    split; auto. split. 2: split; [ unfold default_nodefield; lia | now inversion Hchn ].
    destruct chn. 
    2: apply proj2, is_tc_nodearray_proj_chnaux_tid_bounded in Hproj.
    2: rewrite -> Forall_cons_iff in Hproj; destruct Hproj as (Hproj & _).
    all: unfold default_nodefield; lia.
  - destruct Hproj as (Htmp & Hproj). apply nth_error_some_inrange_Z in Htmp.
    inversion_clear Hchn.
    apply IH with (lch:=(Z.of_nat (tc_roottid ch))); auto; unfold default_nodefield; try lia; try tauto.
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
  destruct tc as [ ? [ | ] ]; simpl; unfold default_nodefield; simpl; try lia.
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
  (Hproj2 : nodearray_emptypart lnode tc) :
  (* dim (Hlen : Zlength lnode = dim)  *)
  Forall (node_struct_regular_wk (Zlength lnode)) lnode.
Proof.
  (* revert lnode Hproj1 Hproj2.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros. *)
  apply Forall_Znth.
  intros n Hr. destruct (tc_getnode (Z.to_nat n) tc) as [ res | ] eqn:E.
  - apply is_tc_nodearray_proj_full_regular_wk, Foralltc_Forall_subtree in Hproj1.
    rewrite -> Forall_forall in Hproj1.
    assert (Datatypes.is_true (ssrbool.isSome (tc_getnode (Z.to_nat n) tc))) as H by now rewrite E.
    apply tc_getnode_subtc_iff, in_map_iff in H.
    destruct H as (sub & Eid & Hin). apply Hproj1 in Hin.
    rewrite -> Eid, -> Z2Nat.id in Hin; auto; try lia.
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
    tc : (@treeclock nat), plclk : val, plnode : val, plstk : val, top : Z, p : val,
    tc' : (@treeclock nat), plclk' : val, plnode' : val, plstk' : val, top' : Z, p' : val
  PRE [ tptr t_struct_treeclock, tptr t_struct_treeclock ]
    (* PROP (is_pos_tshort dim) *)
    PROP (is_pos_tint dim)
    PARAMS (p; p')
    SEP (treeclock_rep dim tc plclk plnode plstk top p * treeclock_rep dim tc' plclk' plnode' plstk' top' p')
  POST [ tvoid ]
    EX top_ : Z, 
    PROP () 
    RETURN ()
    (* nothing should change for p' *)
    SEP (treeclock_rep dim (tc_join tc tc') plclk plnode plstk top_ p * treeclock_rep dim tc' plclk' plnode' plstk' top' p').

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

Definition node_is_null_spec :=
  DECLARE _node_is_null
  WITH dim : Z, idx : nat, lnode : list (reptype t_struct_node),
    tc : (@treeclock nat), v1 : val, plnode : val, v2 : val, v3 : val, p : val
  PRE [ tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; Z.of_nat idx < dim; 
      Z.of_nat (tc_roottid tc) < dim; 
      Zlength lnode = dim; 
      nodearray_emptypart lnode tc; is_tc_nodearray_proj_full lnode tc)
    PARAMS (offset_val (sizeof t_struct_node * Z.of_nat idx) plnode)
    SEP (data_at Tsh (tarray t_struct_node dim) lnode plnode;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tc_roottid tc))), 
          (v1, (plnode, (v2, v3))))) p)
  POST [ tint ]
    (* use a tmp var to avoid bad type checking; see the subsumption proof for reason *)
    EX tmp : bool,
    PROP (tmp = (
      (match tc with Node (mkInfo idx' _ _) nil => Nat.eqb idx idx' | _ => false end) ||
      (match tc_getnode idx tc with None => true | _ => false end)
    )%bool) 
    RETURN (Val.of_bool tmp)
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
    node_is_null_spec
  ]).

Section Main_Proof.

Local Tactic Notation "saturate_lemmas" :=
  let simplegen lm := (let Hq := fresh "_Hyp" in pose proof lm as Hq) in
  (* gen short_max_signed_le_int_max_signed; 
  gen short_max_signed_gt_0;  *)
  simplegen Int.min_signed_neg.

(* TODO two design choices: make a pair of tactics (with aux equations), 
  or make a customized Corollary *)

Local Tactic Notation "array_focus" constr(idx) constr(lstruct) "witheqn" ident(Hy) :=
  (* TODO this part may be extracted to be a compatible generator *)
  match goal with |- context[data_at Tsh (tarray ?ty ?size) lstruct ?plstruct] => 
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

Local Tactic Notation "read_clock" "witheqn" hyp(Eclock_payload) :=
  match type of Eclock_payload with 
  Znth ?n ?lclk = clock_payload ?clk ?aclk => 
    unfold clock_payload in Eclock_payload; 
    rewrite -> Eclock_payload; 
    forward; 
    rewrite <- Eclock_payload;
    fold (clock_payload clk aclk) in Eclock_payload
  end.

Local Tactic Notation "array_unfocus" "witheqn" hyp(Hy) :=
  rewrite <- Hy; 
  sep_apply SingletonHole.array_with_hole_elim;
  rewrite upd_Znth_triv; try lia; try reflexivity; clear Hy.

Local Tactic Notation "rewrite_sem_add_ptr_int" :=
  simpl sem_binary_operation';
  repeat match goal with |- context[force_val (sem_add_ptr_int ?ty Signed ?p ?v)] => 
    ((match goal with _ : isptr p |- _ => idtac end) +
    (let Hisptr := fresh "_Hisptr" in
      assert_PROP (isptr p) as Hisptr by entailer));
    rewrite -> sem_add_pi'; auto; try lia
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
      (let Hq := fresh "_Hyp" in assert (repable_signed x) as Hq by (hnf; lia));
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
  remember ((Z.eqb z2 (-1)) && (Z.eqb z1 (-1)))%bool as b1.
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
  entailer!. f_equal. now rewrite -> andb_comm with (b1:=(z1 =? -1)).
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
    unfold default_nodefield in *.
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

Lemma subsume_node_is_null : funspec_sub (snd node_is_null_spec_local) (snd node_is_null_spec).
Proof.
  saturate_lemmas.

  do_funspec_sub.
  destruct w as ((((((((dim, idx), lnode), tc), ?), plnode), ?), ?), p).
  entailer!.
  array_focus (Z.of_nat idx) lnode witheqn Etmp.
  match goal with H1 : context[is_tc_nodearray_proj_full], 
    H2 : context[nodearray_emptypart] |- _ => 
    pose proof (nodearray_proj_regular _ _ H1 H2) as Hreg end.
  rewrite -> Forall_forall_Znth in Hreg. 
  specialize (Hreg _ (conj (Zle_0_nat idx) H1)).
  destruct Hreg as (z1 & z2 & z3 & z4 & Es & Hz1 & Hz2 & Hz3 & Hz4).
  rewrite -> Es.
  match type of Etmp with _ = ?v => Exists (((((Zlength lnode, v), z1), z2), z3), z4) end.
  match goal with |- (_ * ?a * ?b) |-- _ => Exists (a * b)%logic end.
  rewrite -> Etmp. (* ? *)
  entailer!.
  intros.
  EExists. entailer!. (* eauto for tmp *)
  2: array_unfocus witheqn Etmp; auto.

  (* pure proof *)
  split. 2: match goal with |- Val.of_bool ?b <> _ => now destruct b end.
  match goal with HH : _ = ?b |- _ = ?b => rewrite <- HH; clear HH end.
  f_equal.
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
      assert (Datatypes.is_true (ssrbool.isSome (tc_getnode idx tc))) as HH by now rewrite Etc, E.
      apply tc_getnode_subtc_iff, in_map_iff in HH.
      destruct HH as (sub & Eid & Hin). rewrite Etc in Hin.
      simpl in Hin. destruct Hin as [ <- | Hin ].
      * simpl in Eid. subst u.
        hnf in Hca. simpl in Hca.
        apply nth_error_Znth_result in Hca. rewrite -> Hca, -> Echn in Es.
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

Lemma body_node_is_null: 
  semax_body Vprog Gprog f_node_is_null node_is_null_spec.
Proof.
  eapply semax_body_funspec_sub.
  1: apply body_node_is_null_pre.
  1: apply subsume_node_is_null.
  compute. (* ? *)
  repeat constructor; simpl; lia.
Qed.

Theorem body_join: 
  semax_body Vprog Gprog f_join join_spec.
Proof.
  saturate_lemmas.

  start_function.
  unfold treeclock_rep.
  Intros. Intros lclk_ptrs lnode_ptrs lclk lnode lstk.
  (* TODO cannot customize the name? *)
  Intros. Intros lclk_ptrs' lnode_ptrs' lclk' lnode' lstk'.
  unfold treeclock_payload.
  unfold is_pos_tint in *.
  match goal with HH : context [is_tc_clockarray_proj _ tc] |- _ =>
    pose proof (is_tc_clockarray_proj_nth _ _ HH) as Hca_tc end.
  match goal with HH : context [is_tc_clockarray_proj _ tc'] |- _ =>
    pose proof (is_tc_clockarray_proj_nth _ _ HH) as Hca_tc' end.

  forward. forward. forward. forward.
  (* 1:{ entailer!. unfold is_pos_tshort, short_max_signed in *. 
    rewrite Int.signed_repr; try lia. 
    rewrite -> ! two_power_pos_nat. simpl. lia.
  } *)

  array_focus (Z.of_nat (tc_roottid tc')) lclk' witheqn Etmp.
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

  forward. forward. forward. forward. forward.
  rewrite_sem_add_ptr_int.
  (*
  simpl.
  (* pre *) assert_PROP (isptr plnode) as Hip0 by entailer.
  (* pre *) assert_PROP (isptr plclk) as Hip1 by entailer.
  rewrite -> ! sem_add_pi'; auto; try lia.
  *)


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

Abort.

End Main_Proof.
