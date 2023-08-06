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

Definition node_payload (next prev par headch : Z) : reptype t_struct_node :=
  (Vint (Int.repr next), 
    (Vint (Int.repr prev), 
      (Vint (Int.repr par), Vint (Int.repr headch)))).

Definition node_rep (next prev par headch : Z) (p : val) : mpred :=
  (* !! (is_pos_tshort next) && !! (is_pos_tshort prev) &&
  !! (is_pos_tshort par) && !! (is_pos_tshort headch) && *)
  !! (is_pos_tint next) && !! (is_pos_tint prev) &&
  !! (is_pos_tint par) && !! (is_pos_tint headch) &&
  data_at Tsh t_struct_node (node_payload next prev par headch) p.

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

Definition tcs_head_Z (tcs : list (@treeclock nat)) : Z := 
  match tcs with nil => default_nodefield | ch :: _ => Z.of_nat (tc_roottid ch) end.

Definition tc_headch_Z (tc : @treeclock nat) : Z := tcs_head_Z (tc_rootchn tc).

Global Arguments tcs_head_Z _/.
Global Arguments tc_headch_Z _/.

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

(* sometimes the treeclock corresponds to an empty tree, but do not consider it for now *)

(* factor the dim out; it should not change during the operation? *)
(* seems like top should be consistently -1 *)
Definition treeclock_rep (dim : Z) (tc : @treeclock nat) (plclk plnode : val) 
  (plstk : val) p : mpred :=
  (* EX dim : Z,  *)
  EX lclk_ptrs : list val, 
  EX lnode_ptrs : list val, 
  (* TODO should this be raw (reptype t_struct_clock) or the result of some (map list)? *)
  EX lclk : list (reptype t_struct_clock), 
  EX lnode : list (reptype t_struct_node), 

  EX lstk : list val, 

  (* TODO the clk and aclk must become bounded somewhere.
      if they are bounded with a Foralltc, then we may simply bound tid as well 
        so that we do not need the tid_bounded lemmas and nth_error 
    but for now, we only bound clk and aclk to avoid premature optimization
  *)
  !! (Foralltc (fun sub => Z.of_nat (tc_rootclk sub) < Int.max_signed /\ 
    Z.of_nat (tc_rootaclk sub) < Int.max_signed) tc) &&
  (* this is necessary in the current setting, since the root may not appear in the node array *)
  !! (Z.of_nat (tc_roottid tc) < dim) &&
  !! (Zlength lclk_ptrs = dim) && !! (Zlength lclk = dim) &&
  !! (Zlength lnode_ptrs = dim) && !! (Zlength lnode = dim) &&
  !! (is_tc_clockarray_proj lclk tc) && !! (clockarray_emptypart lclk tc) &&
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
    SEP (treeclock_rep dim tc plclk plnode plstk p * treeclock_rep dim tc' plclk' plnode' plstk' p')
  POST [ tvoid ]
    PROP () 
    RETURN ()
    (* nothing should change for p' *)
    SEP (treeclock_rep dim (tc_join tc tc') plclk plnode plstk p * treeclock_rep dim tc' plclk' plnode' plstk' p').

Definition detach_from_neighbors_spec :=
  DECLARE _detach_from_neighbors
  WITH dim : Z, idx : nat, lnode : list (reptype t_struct_node),
    tc : (@treeclock nat), v1 : val, plnode : val, v2 : val, v3 : val, p : val,
    tc_sub : (@treeclock nat), tc_pivot : (@treeclock nat)
  PRE [ tptr t_struct_treeclock, tint, tptr t_struct_node ]
    PROP (0 <= dim <= Int.max_signed; Z.of_nat idx < dim;
      Zlength lnode = dim; 
      is_tc_nodearray_proj_full lnode tc;
      nodearray_emptypart lnode (tc_flatten tc);
      NoDup (map tc_roottid (tc_flatten tc));
      (* condition for getting parent *)
      idx <> tc_roottid tc; tc_getnode idx tc = Some tc_sub;
      (* result guarantee; however artificial *)
      tc_detach_nodes (Node (mkInfo idx 0%nat 0%nat) nil) tc = (tc_pivot, (tc_sub :: nil)))
    PARAMS (p; Vint (Int.repr (Z.of_nat idx)); 
      offset_val (sizeof t_struct_node * Z.of_nat idx) plnode)
    SEP (data_at Tsh (tarray t_struct_node dim) lnode plnode;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tc_roottid tc))), 
          (v1, (plnode, (v2, v3))))) p)
  POST [ tvoid ]
    EX lnode' : list (reptype t_struct_node),
    PROP (Zlength lnode' = dim;
      (* TODO does the root of tc_sub need to be specified? *)
      is_tc_nodearray_proj lnode' tc_sub;
      is_tc_nodearray_proj_full lnode' tc_pivot;
      nodearray_emptypart lnode' ((tc_flatten tc_sub) ++ (tc_flatten tc_pivot)))
    RETURN ()
    SEP (data_at Tsh (tarray t_struct_node dim) lnode' plnode;
      data_at Tsh t_struct_treeclock
        (Vint (Int.repr dim), (Vint (Int.repr (Z.of_nat (tc_roottid tc))), 
          (v1, (plnode, (v2, v3))))) p).

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
    detach_from_neighbors_spec
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

Local Tactic Notation "read_clock" "witheqn" hyp(Eclock_payload) :=
  match type of Eclock_payload with 
  Znth ?n ?lclk = clock_payload ?clk ?aclk => 
    unfold clock_payload in Eclock_payload; 
    rewrite -> Eclock_payload; 
    forward; 
    rewrite <- Eclock_payload;
    fold (clock_payload clk aclk) in Eclock_payload
  end.

Local Tactic Notation "array_unfocus'" "witheqn" hyp(Hy) :=
  rewrite <- Hy; 
  sep_apply SingletonHole.array_with_hole_elim.

Local Tactic Notation "array_unfocus" "witheqn" hyp(Hy) :=
  array_unfocus' witheqn Hy;
  rewrite upd_Znth_triv; try lia; try reflexivity; clear Hy.

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
  match type of Etmp with _ = ?v => Exists (((((Zlength lnode, v), z1), z2), z3), z4) end.
  match goal with |- (_ * ?a * ?b) |-- _ => Exists (a * b)%logic end.
  rewrite -> Etmp. (* ? *)
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

(* temporary *)

(* proof-relevant witness of subtree? *)

Fixpoint tc_locate (tc : @treeclock nat) (pos : list nat) : option (@treeclock nat) :=
  match pos with
  | nil => Some tc
  | x :: pos' => 
    match nth_error (tc_rootchn tc) x with
    | Some ch => tc_locate ch pos'
    | None => None
    end
  end.

Definition subtc_witness (l : list nat) (sub tc : @treeclock nat) :=
  tc_locate tc l = Some sub.

Fact subtc_trans (tc tc' tc'' : @treeclock nat) :
  subtc tc'' tc' -> subtc tc' tc -> subtc tc'' tc.
Proof.
  revert tc'' tc'.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  hnf in H, H0. destruct H0 as [ <- | H0 ]; auto.
  rewrite -> in_flat_map in H0.
  destruct H0 as (ch & Hin_ch & H0).
  rewrite -> Forall_forall in IH. specialize (IH _ Hin_ch _ _ H H0).
  hnf. right. apply in_flat_map. now exists ch.
Qed.

Fact subtc_chn (tc ch : @treeclock nat) :
  In ch (tc_rootchn tc) -> subtc ch tc.
Proof.
  intros. destruct tc as [(u, clk, aclk) chn]. simpl in *.
  hnf. right. apply in_flat_map. exists ch. split; auto. apply tc_flatten_self_in.
Qed.

Lemma subtc_witness_subtc l :
  forall sub tc, subtc_witness l sub tc -> subtc sub tc.
Proof.
  induction l as [ | x l IH ]; intros; hnf in H; simpl in H.
  - injection H as <-. apply tc_flatten_self_in.
  - destruct (nth_error (tc_rootchn tc) x) as [ res | ] eqn:E; try eqsolve.
    apply IH in H.
    apply nth_error_In in E.
    eapply subtc_trans. 1: apply H.
    now apply subtc_chn.
Qed.

Lemma subtc_subtc_witness tc :
  forall sub, subtc sub tc -> exists l, subtc_witness l sub tc.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  hnf in H. destruct H as [ <- | ].
  - now exists nil.
  - apply in_flat_map in H.
    destruct H as (ch & Hin_ch & Hin).
    rewrite -> Forall_forall in IH. specialize (IH _ Hin_ch).
    apply IH in Hin. destruct Hin as (l & H).
    apply In_nth_error in Hin_ch. destruct Hin_ch as (n & E).
    exists (n :: l). hnf. simpl. now rewrite E.
Qed. 

Corollary subtc_witness_iff sub tc :
  subtc sub tc <-> exists l, subtc_witness l sub tc.
Proof.
  split.
  - intros H. now apply subtc_subtc_witness in H.
  - intros (l & H). now apply subtc_witness_subtc in H.
Qed.

(* TODO there is no list update function in stdlib, so use upd_Znth here as a trick? *)

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
  Node ni (List.filter (fun tc' => negb (has_same_tid idx tc')) chn).

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
Fact filter_all_true {A : Type} (f : A -> bool) (l : list A) 
  (H : forall x, In x l -> f x = true) : filter f l = l.
Proof.
  induction l as [ | y l IH ]; simpl in *; auto.
  pose proof (H _ (or_introl eq_refl)) as ->.
  f_equal. apply IH. apply (fun x Hi => H x (or_intror Hi)).
Qed.

Fact filter_all_false {A : Type} (f : A -> bool) (l : list A) 
  (H : forall x, In x l -> f x = false) : filter f l = nil.
Proof. now apply invariants.filter_none. Qed. (* be lazy *)

Fact tc_detach_nodes_intact (subtree_tc' tc : @treeclock nat) 
  (* (Hdj : forall t, In t (map tc_roottid (tc_flatten tc)) ->  *)
  (Hdj : forall t, In t (map tc_roottid (flat_map tc_flatten (tc_rootchn tc))) -> 
    In t (map tc_roottid (tc_flatten subtree_tc')) -> False) :
  tc_detach_nodes subtree_tc' tc = (tc, nil).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in *.
  erewrite -> map_ext_Forall.
  2:{ 
    rewrite -> Forall_forall in IH |- *.
    intros ch H. apply IH; auto.
    intros t Hin. apply Hdj.
    apply map_flat_map_In. exists ch. split; auto. 
    destruct ch. simpl in *. eqsolve.
  }
  (* TODO repeat the typical proof steps related with tc_detach_nodes *)
  destruct (List.split (map (fun ch : treeclock => (ch, [])) chn))
    as (new_chn, forest) eqn:Esplit, 
    (partition (fun tc' : treeclock => ssrbool.isSome (tc_getnode (tc_roottid tc') subtree_tc')) new_chn)
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
  simpl.
  match type of Enew_chn' with filter ?f ?l = _ => 
    assert (forall ch, In ch l -> f ch = true) as HH end.
  { 
    intros ch Hin.
    destruct (tc_getnode (tc_roottid ch) subtree_tc') as [ res | ] eqn:E; auto.
    exfalso. eapply Hdj. 2: apply tc_getnode_subtc_iff; now rewrite -> E.
    apply map_flat_map_In. 
    exists ch. split; auto. apply in_map with (f:=tc_roottid). apply tc_flatten_self_in.
  }
  simpl in HH.
  rewrite -> filter_all_true in Enew_chn'; auto.
  rewrite -> filter_all_false in Eres'.
  2: intros; now apply negb_true_iff, HH.
  eqsolve.
Qed.

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

Fact split_app {A B : Type} (l1 l2 : list (A * B)) :
  List.split (l1 ++ l2) = 
  let (l1a, l1b) := List.split l1 in let (l2a, l2b) := List.split l2 in
  (l1a ++ l2a, l1b ++ l2b).
Proof.
  revert l2. induction l1 as [ | (a, b) l1 IH ]; intros; simpl in *.
  - now destruct (List.split l2).
  - rewrite -> IH. now destruct (List.split l1), (List.split l2).
Qed.

(* FIXME: this is way too long. need revise.
    for example, consider induction on tc or l? *)

Fact par_subtc_trace tc res l tc_par (Hsub : subtc_witness l tc_par tc) (Hin : In res (tc_rootchn tc_par)) :
  exists ch, In ch (tc_rootchn tc) /\ subtc res ch.
Proof.
  destruct tc as [(u, clk, aclk) chn].
  destruct l as [ | x l ].
  - hnf in Hsub. simpl in Hsub. injection Hsub as <-. simpl in Hin.
    exists res. split; auto. hnf. apply tc_flatten_self_in.
  - hnf in Hsub. simpl in Hsub.
    destruct (nth_error chn x) as [ ch | ] eqn:Enth; try eqsolve.
    pose proof Enth as Hin_ch. apply nth_error_In in Hin_ch.
    exists ch. split; auto. eapply subtc_trans.
    + apply subtc_chn, Hin.
    + apply subtc_witness_iff. eauto.
Qed.

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

Fact tc_detach_nodes_single tc
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  forall res 
  (* this should be a derived conclusion from Hnodup, but for now ignore it *)
  (* (Hneq : tc_roottid res <> tc_roottid tc)  *)
  l tc_par (Hsub : subtc_witness l tc_par tc) (Hin : In res (tc_rootchn tc_par)),
  tc_detach_nodes (Node (mkInfo (tc_roottid res) 0%nat 0%nat) nil) tc = 
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
  remember (Node (mkInfo (tc_roottid res) 0%nat 0%nat) nil) as snd eqn:Esnd.
  rewrite -> Esnd at 1.
  simpl. rewrite -> ! Echn, -> map_app. simpl.
  erewrite -> map_ext_Forall with (l:=pre).
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
      (partition (fun tc' : treeclock => ssrbool.isSome (tc_getnode (tc_roottid tc') snd)) new_chn)
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
    all: subst snd; simpl.
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
      (partition (fun tc' : treeclock => ssrbool.isSome (tc_getnode (tc_roottid tc') snd)) (new_chn_pre ++ res' :: new_chn_suf))
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
    all: subst snd; simpl.
    2-3,5-6: intros ch'' Hin''; destruct (eqdec (tc_roottid res) (tc_roottid ch'')) as [ EE | ]; 
      simpl; try eqsolve.
    2-5: eapply False_ind, Hnotin''; eauto.
    all: destruct (eqdec (tc_roottid res) (tc_roottid res')); simpl; try eqsolve.
    rewrite -> upd_Znth_char; auto.
    subst x. apply Zlength_correct.
Qed.

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
    (* TODO still repeat *)
    (*
    simpl in Echn_par. rewrite Echn in Hnodup. rewrite <- flat_map_app, -> map_app in Hnodup.
    simpl in Hnodup. rewrite -> map_app in Hnodup.
    apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_pre & Hnodup & Hdj1).
    apply NoDup_app in Hnodup. destruct Hnodup as (Hnodup_ch & Hnodup_suf & Hdj2).
    *)
    
    assert (tc_remove_ch (Node ni chn) (tc_roottid res) = Node ni (pre ++ suf)) as Eremovech.
    {
      (* TODO will repeat here? *)
      (* rewrite -> Echn_par, -> filter_app in Etc_pivot. simpl in Etc_pivot. *)
      admit.
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
    + admit.
    + rewrite Elnode'. eapply nodearray_proj_lnode_regalter_preserve. 
      2: apply Hrega. 1: tauto.
      subst lo. simpl.
      (* tedious *)
      admit.
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
        split; [ | split ]; auto.
        all: admit.
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
  (* avoid discontinuous hyp naming *)
  match goal with HH : context [Foralltc ?a tc] |- _ => 
    match a with context[tc_rootclk] => rename HH into Hcb_tc; pose proof True as HH end end.
  match goal with HH : context [Foralltc ?a tc'] |- _ => 
    match a with context[tc_rootclk] => rename HH into Hcb_tc'; pose proof True as HH end end.
  match goal with HH : context [is_tc_clockarray_proj _ tc] |- _ =>
    pose proof (is_tc_clockarray_proj_nth _ _ HH) as Hca_tc end.
  match goal with HH : context [is_tc_clockarray_proj _ tc'] |- _ =>
    pose proof (is_tc_clockarray_proj_nth _ _ HH) as Hca_tc' end.

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
      Exists lclk_ptrs lnode_ptrs lclk lnode lstk.
      entailer!.
      all: now rewrite -> ! Ejoin.
    - thaw group'. simpl.
      unfold treeclock_rep, treeclock_payload.
      Exists lclk_ptrs' lnode_ptrs' lclk' lnode' lstk'.
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

  forward. forward. forward. forward. forward.
  rewrite_sem_add_ptr_int.
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
  forward_call.
  (* retract *)
  remember (match tc_getnode (tc_roottid tc') tc with None => true | _ => false end) as vret eqn:Evret.
  replace (node_is_null_as_bool tc (tc_roottid tc')) with vret.
  2:{ subst vret. unfold node_is_null_as_bool. destruct tc as [(u, ?, ?) [ | ]]; simpl; auto.
    simpl in Hrootid. apply Nat.eqb_neq in Hrootid. now rewrite -> Nat.eqb_sym, -> Hrootid.
  }

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

  (* change into another lnode *)

Abort.

End Main_Proof.
