Require Import VST.floyd.proofauto.
Require Import distributedclocks.vst.treeclock_clight.
Require Import distributedclocks.clocks.treeclock.

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

Definition short_max_signed := two_power_nat 15 - 1.

(* TODO why so tedious *)
Fact Zpower_nat_gt_0 b n : b > 0 -> 0 < Zpower_nat b n.
Proof. induction n; intros; simpl; try nia. Qed.

Fact short_max_signed_le_int_max_signed : short_max_signed <= Int.max_signed.
Proof. 
  unfold Int.max_signed, Int.half_modulus, Int.modulus, short_max_signed, Int.wordsize, Wordsize_32.wordsize.
  unfold two_power_nat. 
  rewrite -> ! shift_nat_correct, -> ! Z.mul_1_r.
  rewrite -> Zaux.Zpower_nat_S with (e:=31%nat), -> Z.mul_comm, -> Z_div_mult; try lia.
  replace 31%nat with (16+15)%nat by lia.
  rewrite -> Zpower_nat_is_exp.
  pose proof (Zpower_nat_gt_0 2%Z 15) as H. removehead H; try lia.
  pose proof (Zpower_nat_gt_0 2%Z 16) as H0. removehead H0; try lia.
  nia.
Qed.

Fact short_max_signed_gt_0 : 0 < short_max_signed.
Proof. 
  unfold short_max_signed, two_power_nat. 
  rewrite -> shift_nat_correct, -> Zaux.Zpower_nat_S.
  pose proof (Zpower_nat_gt_0 2%Z 14) as H. removehead H; try lia.
Qed.

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

#[export] Instance Z_EqDec : EqDec Z.
Proof. constructor. apply Z.eq_dec. Qed.

Definition is_tc_clockarray_proj (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  Foralltc (fun t => nth_error l (tc_roottid t) = 
    Some (clock_payload (Z.of_nat (tc_rootclk t)) (Z.of_nat (tc_rootaclk t)))) tc.

Definition clockarray_emptypart (l : list (reptype t_struct_clock)) (tc : treeclock) : Prop :=
  forall n, tc_getnode n tc = None -> nth_error l n = Some (clock_payload 0%Z 0%Z).

(* TODO could also be per-field description so that there will be only one branch *)

Definition is_tc_nodearray_proj_chnaux (par headch : nat) (l : list (reptype t_struct_node)) :
  nat -> list treeclock -> Prop := 
  fix aux lch chn {struct chn} : Prop := 
  match chn with
  | nil => True (* hopefully will not enter this *)
  | ch :: chn' => 
    let tmp := aux (tc_roottid ch) chn' in 
    match chn' with
    | nil =>
      nth_error l (tc_roottid ch) = 
      Some (node_payload (Z.of_nat lch) 0%Z (Z.of_nat par) (Z.of_nat headch))
    | ch' :: _ =>
      nth_error l (tc_roottid ch) = 
      Some (node_payload (Z.of_nat lch) (Z.of_nat (tc_roottid ch')) (Z.of_nat par) (Z.of_nat headch))
      /\ tmp
    end
  end.

Definition is_tc_nodearray_proj_aux (l : list (reptype t_struct_node)) (tc : @treeclock nat): Prop :=
  let: Node _ chn := tc in 
  match chn with
  | nil => True
  | ch :: _ => is_tc_nodearray_proj_chnaux (tc_roottid tc) (tc_roottid ch) l 0%nat chn
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

Definition is_tc_nodearray_proj (l : list (reptype t_struct_node)) (tc : @treeclock nat) : Prop :=
  Foralltc (is_tc_nodearray_proj_aux l) tc.

Definition nodearray_emptypart (l : list (reptype t_struct_node)) (tc : @treeclock nat) : Prop :=
  forall n, tc_getnode n tc = None -> nth_error l n = Some (node_payload 0%Z 0%Z 0%Z 0%Z).

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
  !! (is_tc_nodearray_proj lnode tc) && !! (nodearray_emptypart lnode tc) &&
  (* TODO this should be subsumed? *)
  (* !! (Foralltc (fun t => Z.of_nat (tc_roottid t) < dim) tc) && *)
  data_at Tsh t_struct_treeclock (treeclock_payload dim (Z.of_nat (tc_roottid tc)) 
    plclk plnode plstk top) p * 
  data_at Tsh (tarray t_struct_clock dim) lclk plclk *
  data_at Tsh (tarray t_struct_node dim) lnode plnode *
  (* data_at Tsh (tarray tshort dim) lstk plstk. *)
  data_at Tsh (tarray tint dim) lstk plstk.

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

(*

Section Dim_Bounds.

Variables (dim : Z) (tc : (@treeclock nat)) (plclk plnode plstk : val) (top : Z) (p : val).
Hypothesis (Hdim_short : is_pos_tshort dim).

(* TODO if nth list returns none then tc is single *)

Lemma dim_bounds_treeclock_rep_root : 

*)

Definition Gprog : funspecs :=
  ltac:(with_library prog [
    join_spec
  ]).

Section Main_Proof.

Local Tactic Notation "saturate_lemmas" :=
  let gen lm := (let Hq := fresh "_Hyp" in pose proof lm as Hq) in
  (* gen short_max_signed_le_int_max_signed; 
  gen short_max_signed_gt_0;  *)
  gen Int.min_signed_neg.

(*
Local Corollary array_with_hole_intro_alt : forall (sh : Share.t) (t : type) (i n : Z) 
    (al : list (reptype t)) (p : val),
  0 <= i < n ->
  data_at sh (tarray t n) al p
  |-- data_at sh t (Znth i al) (field_address (tarray t n) (SUB i) p)
        * SingletonHole.array_with_hole sh t i n al p.
Proof SingletonHole.array_with_hole_intro.
*)

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

  forward.
  (* 1:{ entailer!. unfold is_pos_tshort, short_max_signed in *. 
    rewrite Int.signed_repr; try lia. 
    rewrite -> ! two_power_pos_nat. simpl. lia.
  } *)
  forward.
  forward.
  forward.

  (* pre *) assert_PROP (field_compatible (tarray t_struct_clock dim) [] plclk') as Hcomp by entailer.
  sep_apply (SingletonHole.array_with_hole_intro Tsh _ 
    (Z.of_nat (tc_roottid tc')) dim lclk'); try lia.
  match goal with |- context[field_address (tarray ?a ?size) (SUB ?b) ?c] => 
    assert (field_address (tarray a size) (SUB b) c = offset_val (sizeof a * b) c) as Etmp
    by (apply arr_field_address; try lia; try assumption) end.
  (* match goal with |- context[field_address (tarray ?a ?size) (SUB ?b) ?c] => 
    remember (field_address a b c) as ad eqn:Earroff end.
  pose proof Earroff as Etmp.
  (* need compatible *)
  rewrite arr_field_address in Etmp; try lia; try assumption. *)

  simpl.
  (* pre *) assert_PROP (isptr plclk') as Hip by entailer.
  (* need isptr *)
  rewrite -> sem_add_pi'; auto; try lia.
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
  Intros.
  pose proof (Foralltc_self _ _ Hca_tc') as Etmp2.
  rewrite -> Etmp2.
  unfold clock_payload.
  rewrite -> Etmp.
  (* here, temp _zprime_clocks must be the shape of offset_val; otherwise it cannot forward *)
  forward.
  rewrite <- Etmp.
  fold (clock_payload (Z.of_nat (tc_rootclk tc')) (Z.of_nat (tc_rootaclk tc'))).
  rewrite <- Etmp2.
  clear Etmp Etmp2.
  sep_apply SingletonHole.array_with_hole_elim.
  rewrite upd_Znth_triv; try lia; try reflexivity.

  forward.
  forward.
  forward.
  forward.
  forward.

  deadvars.
(*
  forward_if (temp _t'1 (Val.of_bool (orb
    (Nat.eqb (tc_roottid tc) (tc_roottid tc'))
    ()))).

  forward.
*)
Abort.

End Main_Proof.
