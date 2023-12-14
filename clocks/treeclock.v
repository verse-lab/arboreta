From Coq Require Import List Bool Lia PeanoNat Sorting RelationClasses Permutation.
From Coq Require ssreflect.
From arboreta.utils Require Export util libtac rosetree.
Import ssreflect.SsrSyntax.

From stdpp Require list.

Section TreeClock.

(* Sometimes using auto with * is affordable. *)
Local Ltac intuition_solver ::= auto with *.

Variable thread : Type.

Context `{thread_eqdec : EqDec thread}.

Record nodeinfo : Type := mkInfo {
  info_tid : thread;
  info_clk : nat;
  info_aclk : nat
}.

Definition nodeinfo_eqdec (ni ni' : nodeinfo) : {ni = ni'} + {ni <> ni'}.
Proof.
  decide equality.
  1-2: apply Nat.eq_dec.
Qed.

Instance EqDec_nodeinfo : EqDec nodeinfo := nodeinfo_eqdec.

Instance nodeinfo_IdGetter : IdGetter nodeinfo thread := info_tid.

(*
  Currently, define "treeclock" as a notation instead of a definition. 
  The reason is that if "treeclock" is an alias of "tree nodeinfo", 
    then sometimes unification (including rewriting/destructing/...) will
    fail, since the type inference will usually return "tree nodeinfo", but
    "treeclock" is not syntactically equivalent to "tree nodeinfo". 

  The line containing "rewrite <- (map_ext_Forall _ _ IH)." is an example. 
  One may "Set Printing All" to see the "tree nodeinfo" inside 
    "(map_ext_Forall _ _ IH)" clear. 

  There are several possible ways to work around this: 
  (1) use "setoid_rewrite" whenever possible; 
  (2) use the variant of "rewrite" in mathcomp; 
  (3) "Set Keyed Unification" (suggested in https://github.com/coq/coq/issues/16786); 
  (4) ...

  However, at this stage, possibly the most convenient solution is to
    force this alias not to be a definition. 

  FIXME: for now, there are several issues reporting the problem on Github. 
    See if this problem will be addressed in the future. 
*)

Local Notation treeclock := (tree nodeinfo).

Definition tc_init t : treeclock := Node (mkInfo t 0 0) nil.

Definition tc_incr (tc : treeclock) amount : treeclock := 
  let: Node (mkInfo t clk aclk) chn := tc in Node (mkInfo t (Nat.add clk amount) aclk) chn.

Definition info_partial ni := (info_tid ni, info_clk ni).

Definition tc_rootinfo_partial (tc : treeclock) := info_partial (tr_rootinfo tc).

(* "tc_roottid" is just an alias of "tr_rootid"; should stick to "tr_rootid" only to avoid some unification issues *)
(* Definition tc_roottid (tc : treeclock) := Eval unfold tr_rootid in tr_rootid tc. *)

Definition tc_rootclk (tc : treeclock) := info_clk (tr_rootinfo tc).

Definition tc_rootaclk (tc : treeclock) := info_aclk (tr_rootinfo tc).

(* Global Arguments tc_roottid !_ /. *)
Global Arguments tc_rootclk !_ /.
Global Arguments tc_rootaclk !_ /.
Global Arguments info_partial !_ /.
Global Arguments tc_rootinfo_partial !_ /.

Section Inj_Lemmas.

Context [x y : treeclock].

Local Tactic Notation "go" := destruct x as [(?, ?, ?) ?], y as [(?, ?, ?) ?].

(* FIXME: can we use some meta-programming to avoid such boilerplates? *)
Fact tc_rootinfo_clk_inj : tr_rootinfo x = tr_rootinfo y -> tc_rootclk x = tc_rootclk y.
Proof. go. simpl. congruence. Qed.

Fact tc_partialinfo_tid_inj : tc_rootinfo_partial x = tc_rootinfo_partial y -> tr_rootid x = tr_rootid y.
Proof. go. simpl. congruence. Qed.

Fact tc_partialinfo_clk_inj : tc_rootinfo_partial x = tc_rootinfo_partial y -> tc_rootclk x = tc_rootclk y.
Proof. go. simpl. congruence. Qed.

Fact tc_rootinfo_aclk_inj : tr_rootinfo x = tr_rootinfo y -> tc_rootaclk x = tc_rootaclk y.
Proof. go. simpl. congruence. Qed.

End Inj_Lemmas.
(*
Fact map_map_rootinfo2partialinfo (tcs : list treeclock) :
  map tc_rootinfo_partial tcs = map info_partial (map tr_rootinfo tcs).
Proof.
  rewrite <- map_map with (f:=tr_rootinfo) (g:=info_partial).
  reflexivity.
Qed.
*)
Fact Permutation_rootinfo2partialinfo [tcs1 tcs2 : list treeclock]
  (H : Permutation (map tr_rootinfo tcs1) (map tr_rootinfo tcs2)) :
  Permutation (map tc_rootinfo_partial tcs1) (map tc_rootinfo_partial tcs2).
Proof.
  unfold tc_rootinfo_partial.
  rewrite <- ! (map_map tr_rootinfo info_partial).
  now apply Permutation_map.
Qed.

Fact Permutation_partialinfo2roottid [tcs1 tcs2 : list treeclock]
  (H : Permutation (map tc_rootinfo_partial tcs1) (map tc_rootinfo_partial tcs2)) :
  Permutation (map tr_rootid tcs1) (map tr_rootid tcs2).
Proof.
  rewrite <- 2 map_map with (f:=tc_rootinfo_partial) (g:=fst).
  now apply Permutation_map.
Qed.

(*
Tactic Notation "tc_getnode_unfold" :=
  repeat match goal with
  | |- context[find (has_same_id ?t) (tr_flatten ?ch ++ flat_map tr_flatten ?chn)] =>
    rewrite -> find_app; change (find (has_same_id t) (tr_flatten ch)) with (tr_getnode t ch)
  end.
*)

Definition tc_getclk t (tc : treeclock) :=
  match tr_getnode t tc with
  | Some res => tc_rootclk res
  | _ => 0 (* the default clock *)
  end.

Fact tc_getclk_as_fmap t tc : tc_getclk t tc = 
  match base.fmap tc_rootclk (tr_getnode t tc) with Some res => res | None => 0 end.
Proof. unfold tc_getclk. now destruct (tr_getnode t tc). Qed.

Fact tc_getclk_perm_congr_pre tcs1 tcs2 (Hnodup1 : trs_roots_NoDupId tcs1)
  (Hperm : Permutation (map tc_rootinfo_partial tcs1) (map tc_rootinfo_partial tcs2)) :
  forall t, base.fmap tc_rootclk (find (has_same_id t) tcs1) = base.fmap tc_rootclk (find (has_same_id t) tcs2).
Proof.
  intros.
  etransitivity.
  all: rewrite (option.option_fmap_ext tc_rootclk (Basics.compose snd tc_rootinfo_partial)); auto.
  rewrite ! option.option_fmap_compose.
  f_equal.
  apply id_nodup_find_congr_fmap with (h:=fst); auto.
Qed.

Section TC_Key_Procedures.

(*
  The following recursive functions correspond to the three sub-procedures of the tree clock paper: 
    "getUpdatedNodesJoin", "detachNodes" and "attachNodes". 

  While in the tree clock paper, "detachNodes" and "attachNodes" are implemented as loops with the 
    help of a stack, here they are implemented as recursive tree traversals, thereby avoiding
    the use of an explicit stack data structure. 
*)

Fixpoint tc_get_updated_nodes_join (tc tc' : treeclock) : treeclock :=
  let fix tc_get_updated_nodes_join_aux (tc : treeclock) clk (chn_u' : list treeclock) : list treeclock :=
  match chn_u' with
  | nil => nil
  | tc' :: chn_u'' => 
    let: Node (mkInfo v' clk_v' aclk_v') chn_v' := tc' in
    (* <? is slightly hard to use *)
    if clk_v' <=? (tc_getclk v' tc)
    then 
      (if aclk_v' <=? clk
        then nil
        else (tc_get_updated_nodes_join_aux tc clk chn_u''))
    else (tc_get_updated_nodes_join tc tc') :: (tc_get_updated_nodes_join_aux tc clk chn_u'')
  end in
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (tc_getclk (info_tid info_u') tc) chn_u')
.

(*
  The auxiliary function have to be inside "tc_get_updated_nodes_join" since implementing 
    it as a mutual recursion does not pass the arg decrease check. 

  As a trick, define a same function with the same name outside, so that we can reason about
    the auxiliary function in lemmas. 
*)
(* FIXME: is there any better approach than writing the same code twice? *)

Fixpoint tc_get_updated_nodes_join_aux (tc : treeclock) clk (chn_u' : list treeclock) : list treeclock :=
  match chn_u' with
  | nil => nil
  | tc' :: chn_u'' => 
    let: Node (mkInfo v' clk_v' aclk_v') chn_v' := tc' in
    if clk_v' <=? (tc_getclk v' tc)
    then 
      (if aclk_v' <=? clk
        then nil
        else (tc_get_updated_nodes_join_aux tc clk chn_u''))
    else (tc_get_updated_nodes_join tc tc') :: (tc_get_updated_nodes_join_aux tc clk chn_u'')
  end.

Fact tc_get_updated_nodes_join_eta tc tc' : 
  tc_get_updated_nodes_join tc tc' = 
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (tc_getclk (info_tid info_u') tc) chn_u').
Proof. destruct tc'. reflexivity. Qed.

(* The recursive version of "detachNodes" will return a pair: the resulting tree after detaching
    all subtrees, and also the list of detached subtrees. *)

Fixpoint tc_detach_nodes (tcs : list treeclock) (tc : treeclock) : treeclock * list treeclock :=
  let: Node ni chn := tc in
  let: (new_chn, res) := List.split (map (tc_detach_nodes tcs) chn) in
  let: (res', new_chn') := List.partition (fun tc' => isSome (find (has_same_id (tr_rootid tc')) tcs))
    new_chn in
  (Node ni new_chn', (List.concat res) ++ res').

(* The recursive version of "attachNodes" will be given a list of subtrees and a tree; this function
    will traverse the tree and try attaching subtrees from the list to the tree. *)

Fixpoint tc_attach_nodes (forest : list treeclock) (tc' : treeclock) : treeclock :=
  let: Node info_u' chn' := tc' in
  let: u_pre := List.find (has_same_id (info_tid info_u')) forest in
  let: chn_u := (match u_pre with Some u => tr_rootchn u | None => nil end) in
  Node info_u' ((map (tc_attach_nodes forest) chn') ++ chn_u).

(*
  "tc_join_partial" is the core of the join operation. It shows how to use the two
    auxiliary operations "detachNodes" and "attachNodes" to implement the join operation. 

  "getUpdatedNodesJoin" is used in "tc_join", and its return value will be supplied to 
    "tc_join_partial". 
*)

Definition tc_join_partial (tc subtree_tc' : treeclock) :=
  let: (pivot, forest) := tc_detach_nodes (tr_flatten subtree_tc') tc in
  let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
  let: Node info_z chn_z := pivot in 
  Node info_z ((Node (mkInfo w clk_w (info_clk info_z)) chn_w) :: chn_z).

Definition tc_join (tc tc' : treeclock) := Eval unfold tc_join_partial in
  let: mkInfo z' clk_z' aclk_z' := tr_rootinfo tc' in
  if clk_z' <=? (tc_getclk z' tc)
  then tc
  else tc_join_partial tc (tc_get_updated_nodes_join tc tc').

End TC_Key_Procedures.

Section TC_Respect_Theory.

(*
  Both of the two monoticity conditions require to state something like "the clock of the nodes in a tree is
    no more than another tree", as captured by "tc_ge". 

  Note that it is defined as "tc_ge" instead of "tc_le" since we want the "larger"
    tree to be the first argument, so that the definition of "tc_respect" will look better. 
*)

Definition tc_ge (tc_larger tc : treeclock) : Prop := 
  Foralltr (fun tc0 => tc_rootclk tc0 <= tc_getclk (tr_rootid tc0) tc_larger) tc.

Definition dmono_single (tc_larger tc : treeclock) : Prop :=
  tc_rootclk tc <= (tc_getclk (tr_rootid tc) tc_larger) -> tc_ge tc_larger tc.

Definition imono_single (tc_larger tc : treeclock) : Prop :=
  Forall (fun tc_v =>
    tc_rootaclk tc_v <= (tc_getclk (tr_rootid tc) tc_larger) -> tc_ge tc_larger tc_v) (tr_rootchn tc). 

(* Define the respect condition to be the conjunction of direct monoticity and indirect monoticity. *)

Record tc_respect (tc tc' : treeclock) : Prop := {
  dmono : Foralltr (dmono_single tc') tc;
  imono : Foralltr (imono_single tc') tc
}.

Global Arguments dmono [_ _] _.
Global Arguments imono [_ _] _.

Fact tc_respect_nochn_trivial ni tc' : tc_respect (Node ni nil) tc'.
Proof.
  constructor.
  - constructor; auto.
    hnf.
    intros.
    constructor; simpl; auto.
  - constructor; auto.
    hnf.
    constructor.
Qed.

Fact tc_ge_all_getclk_ge [tc tc_larger] (H : tc_ge tc_larger tc) 
  t : tc_getclk t tc <= tc_getclk t tc_larger.
Proof.
  unfold tc_getclk at 1.
  destruct (tr_getnode t tc) as [ res | ] eqn:E.
  - apply trs_find_has_id in E.
    destruct E as (Hin & <-).
    eapply Foralltr_subtr in Hin.
    2: apply H.
    assumption.
  - apply Nat.le_0_l.
Qed.

Fact all_getclk_ge_tc_ge [tc tc_larger] (Hnodup : tr_NoDupId tc)
  (H : forall t, tc_getclk t tc <= tc_getclk t tc_larger) :
  tc_ge tc_larger tc.
Proof.
  hnf.
  pose proof (id_nodup_find_self Hnodup) as Hself%Foralltr_Forall_subtree.
  eapply Foralltr_impl; eauto.
  simpl.
  intros tc0 E.
  specialize (H (tr_rootid tc0)).
  unfold tc_getclk, tr_getnode in H |- *.
  now rewrite E in H.
Qed.

#[export] Instance tc_ge_trans : Transitive tc_ge.
Proof.
  hnf.
  intros tc_x tc_y tc_z Hge1 Hge2.
  hnf in Hge2 |- *.
  rewrite -> Foralltr_Forall_subtree, List.Forall_forall in Hge2 |- *.
  intros [(t, clk, aclk) chn] Hin.
  specialize (Hge2 _ Hin).
  simpl in Hge2 |- *.
  pose proof (tc_ge_all_getclk_ge Hge1 t).
  etransitivity; eauto.
Qed.

Fact tc_ge_info_subset_preserve [tc tc' : treeclock]
  (Hincl : incl (map tr_rootinfo (tr_flatten tc')) (map tr_rootinfo (tr_flatten tc)))
  [tc_larger] (Hge : tc_ge tc_larger tc) : tc_ge tc_larger tc'.
Proof.
  hnf in Hge |- *.
  rewrite Foralltr_Forall_subtree in Hge |- *.
  unfold tc_rootclk, tr_rootid in Hge |- *.
  pose proof (Forall_map tr_rootinfo (fun ni => info_clk ni <= tc_getclk (info_tid ni) tc_larger)) as Htmp.
  simpl in Htmp.
  rewrite <- Htmp in Hge |- *.
  eapply incl_Forall; eauto.
Qed.

Fact tc_ge_prefix_preserve [tc tc' : treeclock] (Hprefix : prefixtr tc' tc)
  [tc_larger] (Hge : tc_ge tc_larger tc) : tc_ge tc_larger tc'.
Proof.
  eapply tc_ge_info_subset_preserve; eauto.
  apply prefixtr_flatten_info_incl; auto.
Qed.

Section Pointwise_Treeclock.

  Context [tc1 tc2 tc_max : treeclock].
  Hypotheses (Hpmax : forall t, tc_getclk t tc_max = Nat.max (tc_getclk t tc1) (tc_getclk t tc2))
    (Hnodup1 : tr_NoDupId tc1) (Hnodup2 : tr_NoDupId tc2).

  Fact tc_ge_from_pointwise_max : tc_ge tc_max tc1 /\ tc_ge tc_max tc2.
  Proof.
    eapply all_getclk_ge_tc_ge with (tc_larger:=tc_max) in Hnodup1, Hnodup2.
    2-3: intros t; rewrite -> Hpmax; lia.
    intuition.
  Qed.

  Lemma dmono_single_pointwise_max_preserve [tc] 
    (Hdmono1 : dmono_single tc1 tc)
    (Hdmono2 : dmono_single tc2 tc) :
    dmono_single tc_max tc.
  Proof.
    hnf in Hdmono1, Hdmono2 |- *.
    intros Hle.
    pose proof tc_ge_from_pointwise_max as Hge.
    rewrite -> Hpmax in Hle.
    apply Nat.max_le in Hle.
    destruct Hle as [ Hle | Hle ].
    1: specialize (Hdmono1 Hle); transitivity tc1; auto.
    2: specialize (Hdmono2 Hle); transitivity tc2; auto.
    all: intuition.
  Qed.

  Lemma imono_single_pointwise_max_preserve [tc] 
    (Himono1 : imono_single tc1 tc)
    (Himono2 : imono_single tc2 tc) :
    imono_single tc_max tc.
  Proof.
    hnf in Himono1, Himono2 |- *.
    destruct tc as [(u, clk_u, aclk_u) chn].
    rewrite -> List.Forall_forall in Himono1, Himono2 |- *.
    intros [(v, clk_v, aclk_v) chn_v] Hin Hle.
    pose proof tc_ge_from_pointwise_max as Hge.
    rewrite -> Hpmax in Hle.
    apply Nat.max_le in Hle.
    destruct Hle as [ Hle | Hle ].
    1: specialize (Himono1 _ Hin Hle); transitivity tc1; auto.
    2: specialize (Himono2 _ Hin Hle); transitivity tc2; auto.
    all: intuition.
  Qed.

  Corollary tc_respect_pointwise_max_preserve [tc] 
    (Hrespect1 : tc_respect tc tc1)
    (Hrespect2 : tc_respect tc tc2) :
    tc_respect tc tc_max.
  Proof.
    destruct Hrespect1 as (Hdmono1 & Himono1), Hrespect2 as (Hdmono2 & Himono2).
    constructor.
    - rewrite -> Foralltr_Forall_subtree, List.Forall_forall in Hdmono1, Hdmono2 |- *.
      intros sub Hin.
      apply dmono_single_pointwise_max_preserve; firstorder.
    - rewrite -> Foralltr_Forall_subtree, List.Forall_forall in Himono1, Himono2 |- *.
      intros sub Hin.
      apply imono_single_pointwise_max_preserve; firstorder.
  Qed.

End Pointwise_Treeclock.

Fact tc_respect_sub [tc tc'] (H : tc_respect tc tc') :
  Foralltr (fun sub => tc_respect sub tc') tc.
Proof.
  pose proof (conj (dmono H) (imono H)) as HH.
  rewrite <- Foralltr_and, <- Foralltr_idempotent in HH.
  eapply Foralltr_impl.
  2: apply HH.
  setoid_rewrite -> Foralltr_and.
  intros. 
  now constructor.
Qed.

Fact tc_respect_chn [tc tc'] (H : tc_respect tc tc') :
  Forall (fun ch => tc_respect ch tc') (tr_rootchn tc).
Proof. now apply Foralltr_chn_selves, tc_respect_sub. Qed.

Lemma dmono_prefix_preserve [tc tc' : treeclock] (Hprefix : prefixtr tc' tc) :
  forall [tc_larger] (Hdmono : Foralltr (dmono_single tc_larger) tc),
  Foralltr (dmono_single tc_larger) tc'.
Proof.
  induction Hprefix as [ni chn1 chn2_sub chn2 Hsub Hprefix IH] using prefixtr_ind_2; intros.
  rewrite -> Foralltr_cons_iff in Hdmono |- *.
  destruct Hdmono as (Hdmono & Hdmono_chn).
  split.
  - hnf in Hdmono |- *.
    intros Hle.
    eapply tc_ge_prefix_preserve.
    1: econstructor; eauto.
    intuition.
  - eapply incl_Forall in Hdmono_chn.
    2: hnf; apply (sublist_In Hsub).
    pose proof (Forall2_forall_exists_l IH) as Hcorr_in.
    rewrite -> List.Forall_forall in Hdmono_chn |- *.
    intros ch' Hin'.
    destruct (Hcorr_in _ Hin') as (ch & Hin_ch & Htarg).
    now apply Htarg, Hdmono_chn.
Qed.

Lemma imono_prefix_preserve [tc tc' : treeclock] (Hprefix : prefixtr tc' tc) :
  forall [tc_larger] (Himono : Foralltr (imono_single tc_larger) tc),
  Foralltr (imono_single tc_larger) tc'.
Proof.
  induction Hprefix as [ni chn1 chn2_sub chn2 Hsub Hprefix IH] using prefixtr_ind_2; intros.
  rewrite -> Foralltr_cons_iff in Himono |- *.
  unfold imono_single in Himono |- *.
  rewrite <- list.Forall_and in Himono |- *.
  simpl in Himono |- *.
  pose proof (Forall2_forall_exists_l Hprefix) as Hcorr1.
  pose proof (Forall2_forall_exists_l IH) as Hcorr2.
  eapply incl_Forall in Himono.
  2: hnf; apply (sublist_In Hsub).
  rewrite -> List.Forall_forall in Himono |- *.
  intros ch' Hin'.
  destruct (Hcorr1 _ Hin') as (ch & Hin_ch & Hp), (Hcorr2 _ Hin') as (ch_ & Hin_ch_ & Hp_).
  rewrite (tc_rootinfo_aclk_inj (prefixtr_rootinfo_same Hp)).
  split.
  - intros Hq. 
    eapply tc_ge_prefix_preserve.
    1: apply Hp.
    revert Hq.
    eapply Himono; eauto.
  - eapply Hp_, Himono; eauto.
Qed.

Corollary tc_respect_prefix_preserve [tc tc'] (Hprefix : prefixtr tc' tc)
  [tc_larger] (Hrespect : tc_respect tc tc_larger) :
  tc_respect tc' tc_larger.
Proof.
  constructor.
  - apply dmono in Hrespect.
    eapply dmono_prefix_preserve; eauto.
  - apply imono in Hrespect.
    eapply imono_prefix_preserve; eauto.
Qed.

End TC_Respect_Theory.

Section TC_Shape_Invariant_Theory.

Definition tc_chn_aclk_decsorted tc := StronglySorted ge (map tc_rootaclk (tr_rootchn tc)). 

Definition tc_chn_aclk_ub tc: Prop :=
  Forall (fun tc' => tc_rootaclk tc' <= tc_rootclk tc) (tr_rootchn tc). 

Record tc_shape_inv (tc : treeclock) : Prop := {
  tid_nodup: tr_NoDupId tc;
  aclk_upperbound: Foralltr tc_chn_aclk_ub tc;
  aclk_decsorted: Foralltr tc_chn_aclk_decsorted tc
  (* this is only useful if we want to guarantee that the domain of join is the union of two operands *)
  (* clk_lowerbound: Foralltr (fun tc' => 0 < tc_rootclk tc') tc *)
}.

Global Arguments tid_nodup [_] _.
Global Arguments aclk_upperbound [_] _.
Global Arguments aclk_decsorted [_] _.

Fact tc_shape_inv_conj_iff tc : 
  tc_shape_inv tc <-> 
    (List.NoDup (map tr_rootid (tr_flatten tc))
    /\ Foralltr tc_chn_aclk_ub tc
    /\ Foralltr tc_chn_aclk_decsorted tc).
Proof.
  split.
  - now intros [? ? ?].
  - intros.
    now constructor.
Qed.

Fact tc_shape_inv_root_aclk_useless [u clk aclk aclk'] [chn : list treeclock]
  (Hshape : tc_shape_inv (Node (mkInfo u clk aclk) chn)) :
  tc_shape_inv (Node (mkInfo u clk aclk') chn).
Proof.
  constructor.
  - apply tid_nodup in Hshape.
    now simpl in *.
  - apply aclk_upperbound in Hshape.
    rewrite -> ! Foralltr_cons_iff in Hshape |- *.
    now simpl in *.
  - apply aclk_decsorted in Hshape.
    rewrite -> ! Foralltr_cons_iff in Hshape |- *.
    now simpl in *.
Qed.

Lemma tc_shape_inv_sub [tc] (Hshape : tc_shape_inv tc) : Foralltr tc_shape_inv tc.
Proof.
  apply tc_shape_inv_conj_iff in Hshape.
  rewrite -> ! Foralltr_Forall_subtree in Hshape.
  rewrite -> Foralltr_Forall_subtree.
  change tc_shape_inv with (fun tc' => tc_shape_inv tc').
  setoid_rewrite -> tc_shape_inv_conj_iff.
  repeat apply Forall_and.
  2-3: now apply Foralltr_Forall_subtree, Foralltr_idempotent, Foralltr_Forall_subtree.
  now apply Foralltr_Forall_subtree, id_nodup_Foralltr_id.
Qed.

Corollary tc_shape_inv_chn [tc] (Hshape : tc_shape_inv tc) : Forall tc_shape_inv (tr_rootchn tc).
Proof. now apply Foralltr_chn_selves, tc_shape_inv_sub. Qed.

(* prefix also have shape inv *)
Lemma tc_shape_inv_prefix_preserve [tc tc' : treeclock] (Hprefix : prefixtr tc tc') 
  (Hshape : tc_shape_inv tc') : tc_shape_inv tc.
Proof.
  rewrite tc_shape_inv_conj_iff in Hshape |- *.
  split.
  1: eapply id_nodup_prefix_preserve; eauto; tauto.
  apply proj2 in Hshape.
  rewrite <- Foralltr_and in Hshape |- *.

  induction Hprefix as [ni chn1 chn2_sub chn2 Hsub Hprefix IH] using prefixtr_ind_2; intros.
  rewrite -> Foralltr_cons_iff in Hshape |- *.
  split.
  - destruct Hshape as ((Hshape1 & Hshape2) & _).
    unfold tc_chn_aclk_ub, tc_chn_aclk_decsorted in Hshape1, Hshape2 |- *.
    simpl in Hshape1, Hshape2 |- *.
    assert (map tc_rootaclk chn1 = map tc_rootaclk chn2_sub) as Hq.
    {
      clear -Hprefix thread_eqdec.
      induction Hprefix; simpl; auto; f_equal; auto.
      eapply tc_rootinfo_aclk_inj, prefixtr_rootinfo_same; eauto.
    }
    eapply sublist_Forall in Hshape1.
    2: apply Hsub.
    eapply sublist_StronglySorted in Hshape2.
    2: apply sublist_map, Hsub.
    pose proof (Forall_map tc_rootaclk (fun a => a <= info_clk ni)) as Htmp.
    simpl in Htmp.
    rewrite <- Htmp in Hshape1 |- *.
    rewrite Hq.
    intuition.
  - pose proof (Forall2_forall_exists_l IH) as Hcorr.
    simpl in Hcorr.
    apply proj2 in Hshape.
    eapply sublist_Forall in Hshape.
    2: apply Hsub.
    rewrite Forall_forall in Hshape |- *.
    intros ch' Hin'.
    destruct (Hcorr _ Hin') as (ch & Hin & Hp).
    eapply Hp; eauto.
Qed.

(* exploit some simple cases, which may be not generalizable but simpler ... *)

Lemma tc_shape_inv_prepend_child [ni] [chn : list treeclock] (Hshape : tc_shape_inv (Node ni chn))
  [tc_new] (Hshape_new : tc_shape_inv tc_new)
  (* knowing that tid_nodup after prepending will be convenient *)
  (Hnodup : tr_NoDupId (Node ni (tc_new :: chn)))
  (Haclk_bounded : tc_rootaclk tc_new <= info_clk ni)
  (Haclk_ge : tc_rootaclk tc_new >= match chn with ch :: _ => tc_rootaclk ch | nil => 0 end) :
  tc_shape_inv (Node ni (tc_new :: chn)).
Proof.
  constructor.
  - assumption.
  - constructor.
    + apply aclk_upperbound, Foralltr_self in Hshape.
      hnf in Hshape |- *.
      now constructor.
    + apply aclk_upperbound in Hshape, Hshape_new.
      apply Foralltr_cons_iff in Hshape.
      now constructor.
  - constructor.
    + apply aclk_decsorted, Foralltr_self in Hshape.
      hnf in Hshape |- *.
      constructor.
      1: assumption.
      destruct chn as [ | ch chn ].
      * now simpl.
      * constructor.
        1: assumption.
        simpl in Hshape.
        apply StronglySorted_inv, proj2 in Hshape.
        rewrite -> List.Forall_forall in Hshape |- *.
        intros x Hin.
        specialize (Hshape _ Hin).
        lia.
    + apply aclk_decsorted in Hshape, Hshape_new.
      apply Foralltr_cons_iff in Hshape.
      now constructor.
Qed.

End TC_Shape_Invariant_Theory.

Section TC_Get_Updated_Nodes_Join.

Tactic Notation "tc_get_updated_nodes_join_unfold" :=
  cbn delta -[tc_get_updated_nodes_join] iota beta;
  rewrite -> tc_get_updated_nodes_join_eta.

Tactic Notation "tc_get_updated_nodes_join_unfold" "in_" hyp(H) :=
  cbn delta -[tc_get_updated_nodes_join] iota beta in H;
  rewrite -> tc_get_updated_nodes_join_eta in H.

(* purely computational, with minimal precondition *)

Fact tc_get_updated_nodes_join_aux_app tc clk chn1 chn2 
  (H : Forall (fun tc' => clk < tc_rootaclk tc' \/ (tc_getclk (tr_rootid tc') tc) < tc_rootclk tc') chn1) :
  tc_get_updated_nodes_join_aux tc clk (chn1 ++ chn2) =
  tc_get_updated_nodes_join_aux tc clk chn1 ++ tc_get_updated_nodes_join_aux tc clk chn2.
Proof.
  revert chn2. 
  induction chn1 as [ | [ (v', clk_v', aclk_v') ? ] chn1 IH ]; intros; simpl; auto.
  rewrite Forall_cons_iff in H.
  destruct H as (H1 & H2).
  simpl in H1.
  rewrite IH; auto.
  destruct (clk_v' <=? tc_getclk v' tc) eqn:E1, (aclk_v' <=? clk) eqn:E2; auto.
  apply Nat.leb_le in E1, E2; lia.
Qed.

(* if we only care about the roots ... *)
Fact tc_get_updated_nodes_join_aux_tc_congr tc tc' clk chn 
  (Hcong : Forall (fun sub => tc_getclk (tr_rootid sub) tc = tc_getclk (tr_rootid sub) tc') chn) :
  map tr_rootinfo (tc_get_updated_nodes_join_aux tc clk chn) = 
  map tr_rootinfo (tc_get_updated_nodes_join_aux tc' clk chn).
Proof.
  induction chn as [ | [ (v', clk_v', aclk_v') ? ] chn IH ]; intros; simpl; auto.
  apply Forall_cons_iff in Hcong.
  simpl in Hcong.
  rewrite -> (proj1 Hcong). 
  fold tc_get_updated_nodes_join_aux.
  destruct (clk_v' <=? tc_getclk v' tc')%nat, (aclk_v' <=? clk)%nat; simpl; auto.
  all: rewrite -> ! (IH (proj2 Hcong)); reflexivity.
Qed.

Lemma tc_get_updated_nodes_join_aux_result tc clk chn_u'
  (Haclk_impl_clk : forall tc', In tc' chn_u' -> 
    tc_rootaclk tc' <= clk -> 
    tc_rootclk tc' <= (tc_getclk (tr_rootid tc') tc)) 
  (Hsorted: StronglySorted ge (map tc_rootaclk chn_u')) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc clk chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => In tc' chn_u'' <-> 
      ((tc_getclk (tr_rootid tc') tc) < tc_rootclk tc' /\
        clk < tc_rootaclk tc')) chn_u').
Proof.
  induction chn_u' as [ | tc_v' chn_u' IH ].
  - exists nil.
    intuition.
  - simpl in Haclk_impl_clk, Hsorted.
    apply StronglySorted_inv in Hsorted.
    destruct Hsorted as (Hsorted & Hallle).
    destruct tc_v' as [(v', clk_v', aclk_v') chn_v'] eqn:Etc_v'.
    simpl in Hallle.
    rewrite <- Etc_v' in *.
    removehead IH.
    2:{
      intros tc' ?.
      specialize (Haclk_impl_clk tc').
      apply Haclk_impl_clk.
      intuition.
    }
    removehead IH.
    2: assumption.
    destruct IH as (chn_u'' & Hsub & Hres & Halllt).
    setoid_rewrite -> Forall_cons_iff.
    tc_get_updated_nodes_join_unfold.
    setoid_rewrite -> Etc_v' at 2.
    destruct (clk_v' <=? tc_getclk v' tc) eqn:Ecmp_clk_v'.
    + apply Nat.leb_le in Ecmp_clk_v'.
      destruct (aclk_v' <=? clk) eqn:Ecmp_aclk_v'.
      * (* chu_u'' is actually nil *)
        apply Nat.leb_le in Ecmp_aclk_v'.
        assert (chn_u'' = nil) as ->.
        {
          (* Oh, a long proof *)
          destruct chn_u'' as [ | tc_v'' chn_u'' ].
          1: auto. 
          apply sublist_cons_In in Hsub.
          rename Hsub into Hin'.
          rewrite -> Forall_map in Hallle.
          rewrite -> List.Forall_forall in Hallle, Halllt.
          specialize (Hallle _ Hin').
          specialize (Haclk_impl_clk _ (or_intror Hin')).
          removehead Haclk_impl_clk.
          2: lia.
          exfalso.
          revert Haclk_impl_clk.
          apply Nat.nle_gt, Halllt; simpl; intuition.
        }
        exists nil.
        rewrite -> Etc_v'.
        simpl.
        intuition (auto using list.sublist_nil_l).
        lia.
      * exists chn_u''.
        split.
        1: now constructor.
        split.
        1: assumption.
        split.
        2: assumption.
        transitivity False.
        2: rewrite -> Etc_v'; simpl; lia.
        split.
        2: intros [].
        intros Hin'.
        pose proof Hin' as Hin'_backup.
        eapply sublist_In in Hin'.
        2: apply Hsub.
        rewrite -> List.Forall_forall in Halllt.
        apply Halllt in Hin'.
        rewrite -> Hin', -> Etc_v' in Hin'_backup.
        simpl in Hin'_backup.
        lia.
    + pose proof Ecmp_clk_v' as Ecmp_clk_v'_lt.
      apply Nat.leb_gt in Ecmp_clk_v'_lt.
      specialize (Haclk_impl_clk _ (or_introl eq_refl)).
      rewrite <- ! Nat.nlt_ge, -> ! Etc_v' in Haclk_impl_clk.
      simpl in Haclk_impl_clk.
      exists (tc_v' :: chn_u'').
      split.
      1: now constructor.
      split; [ | split; [ split | ] ].
      * rewrite -> Etc_v'.
        tc_get_updated_nodes_join_unfold.
        now f_equal.
      * intros _.
        rewrite -> Etc_v'.
        simpl.
        intuition.
      * rewrite -> Etc_v'.
        now constructor.
      * simpl.
        eapply List.Forall_impl.
        2: apply Halllt.
        intros ch HH.
        rewrite <- HH.
        intuition.
        subst ch.
        rewrite -> Etc_v' in HH.
        simpl in HH.
        intuition.
Qed.

(* a weaker result; did not find a good way to combine with the statement above *)

Lemma tc_get_updated_nodes_join_aux_result_submap tc clk chn :
  exists chn', list.sublist chn' chn /\
    (tc_get_updated_nodes_join_aux tc clk chn) = map (tc_get_updated_nodes_join tc) chn'.
Proof.
  induction chn as [ | ch chn IH ]; intros.
  - now exists nil.
  - tc_get_updated_nodes_join_unfold.
    destruct ch as [(v, clk_v, aclk_v) chn_v] eqn:Ech.
    cbn.
    destruct IH as (chn' & Hsub & ->).
    rewrite <- Ech.
    destruct (clk_v <=? tc_getclk v tc) eqn:E.
    + destruct (aclk_v <=? clk) eqn:E2.
      * exists nil.
        split; [ apply list.sublist_nil_l | reflexivity ].
      * exists chn'.
        split; [ now constructor | reflexivity ].
    + exists (ch :: chn').
      split; [ now constructor | ].
      simpl.
      now subst ch.
Qed.

Fact tc_get_updated_nodes_join_trace [tc'] : forall [tc sub_prefix]
  (H : subtr sub_prefix (tc_get_updated_nodes_join tc tc')), 
  exists sub, subtr sub tc' /\ sub_prefix = tc_get_updated_nodes_join tc sub.
Proof.
  induction tc' as [(u', clk', aclk') chn' IH] using tree_ind_2; intros.
  tc_get_updated_nodes_join_unfold in_ H.
  cbn delta [tr_flatten In info_tid] beta iota in H.
  destruct H as [ <- | (ch & Hin_ch & H)%in_flat_map ].
  - eexists. 
    split; [ apply tr_flatten_self_in | ].
    reflexivity.
  - pose proof (tc_get_updated_nodes_join_aux_result_submap tc (tc_getclk u' tc) chn') 
      as (chn'' & Hsl & E).
    rewrite -> E in Hin_ch.
    apply in_map_iff in Hin_ch.
    destruct Hin_ch as (ch'' & <- & Hin_ch).
    pose proof (sublist_In Hsl Hin_ch) as Hin_ch'.
    eapply Forall_forall in IH.
    2: apply Hin_ch'.
    destruct (IH _ _ H) as (sub & Hsub & ->).
    exists sub.
    split; [ | reflexivity ].
    now eapply subtr_trans; [ | apply subtr_chn; simpl; apply Hin_ch' ].
Qed.

Corollary tc_get_updated_nodes_join_is_prefix tc tc' :
  prefixtr (tc_get_updated_nodes_join tc tc') tc'.
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using tree_ind_2; intros.
  tc_get_updated_nodes_join_unfold.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_submap tc (tc_getclk u' tc) chn')
    as (chn'' & Hsub & ->).
  econstructor.
  1: apply Hsub.
  apply Forall2_mapself_l.
  pose proof (sublist_In Hsub).
  rewrite -> List.Forall_forall in IH |- *.
  firstorder.
Qed.

Fact imono_single_aclk_impl_clk [tc u' clk_u' aclk_u' chn_u']
  (Himono : imono_single tc (Node (mkInfo u' clk_u' aclk_u') chn_u')) :
  forall tc', In tc' chn_u' -> 
    tc_rootaclk tc' <= (tc_getclk u' tc) -> 
    tc_rootclk tc' <= (tc_getclk (tr_rootid tc') tc).
Proof.
  intros tc_v' Hin' Hle.
  (* use imono *)
  hnf in Himono.
  rewrite -> List.Forall_forall in Himono.
  specialize (Himono _ Hin').
  destruct tc_v' as [(v', clk_v', aclk_v') chn_v'].
  simpl in Hle, Himono |- *.
  now apply Himono, Foralltr_self in Hle.
Qed.

(* subsumption? *)
Lemma tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn_u' 
  (Hshape_tc' : tc_shape_inv (Node (mkInfo u' clk_u' aclk_u') chn_u')) 
  (Hrespect : tc_respect (Node (mkInfo u' clk_u' aclk_u') chn_u') tc) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc (tc_getclk u' tc) chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => ~ In tc' chn_u'' <-> tc_ge tc tc') chn_u') /\
    (Forall (fun tc' => In tc' chn_u'' <-> (tc_getclk (tr_rootid tc') tc) < tc_rootclk tc') chn_u') /\
    (Forall (fun tc' => (tc_getclk u' tc) < tc_rootaclk tc') chn_u'').
Proof.
  pose proof (tc_get_updated_nodes_join_aux_result tc (tc_getclk u' tc) chn_u') as H.
  (* get aclk_impl_clk *)
  pose proof (imono Hrespect) as Himono.
  apply Foralltr_cons_iff, proj1 in Himono.
  pose proof (imono_single_aclk_impl_clk Himono) as Haclk_impl_clk.
  pose proof (fun tc' H => contra_not (Haclk_impl_clk tc' H)) as Haclk_impl_clk'.
  repeat setoid_rewrite -> Nat.nle_gt in Haclk_impl_clk'.
  removehead H.
  2: assumption.
  removehead H.
  2: now apply aclk_decsorted, Foralltr_cons_iff in Hshape_tc'.
  destruct H as (chn_u'' & Hsub & Hres & Halllt).
  exists chn_u''.
  split.
  1: assumption.
  split.
  1: assumption.
  (* the subsumption part *)
  rewrite -> List.Forall_forall in Halllt.
  assert (forall x : treeclock, In x chn_u' ->
    ~ In x chn_u'' <-> tc_rootclk x <= tc_getclk (tr_rootid x) tc) as Halllt'.
  {
    intros ch Hin.
    rewrite -> Halllt, <- Nat.nlt_ge; auto.
    pose proof (Haclk_impl_clk' _ Hin).
    intuition.
  }
  rewrite -> ! List.Forall_forall.
  split; [ | split ].
  - intros ch Hin.
    specialize (Halllt' _ Hin).
    rewrite -> Halllt'.
    split; intros H.
    2: apply Foralltr_self in H; now destruct ch as [(?, ?, ?) ?].
    (* use dmono *)
    apply dmono, Foralltr_cons_iff in Hrespect.
    destruct Hrespect as (_ & Hdmono).
    rewrite -> List.Forall_forall in Hdmono.
    specialize (Hdmono _ Hin).
    apply Foralltr_self in Hdmono.
    destruct ch as [(?, ?, ?) ?].
    firstorder.
  - firstorder.
  - intros ch Hin.
    pose proof (sublist_In Hsub Hin).
    firstorder.
Qed.

(* make it over the whole tree; also soundness *)

Corollary tc_get_updated_nodes_join_shape [tc'] (Hshape: tc_shape_inv tc') : 
  forall [tc] (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc'),
  Foralltr (fun tc' => tc_getclk (tr_rootid tc') tc < tc_rootclk tc') 
    (tc_get_updated_nodes_join tc tc') /\
  Foralltr (fun tc' => let: Node ni chn := tc' in
    Forall (fun tc' => tc_getclk (info_tid ni) tc < tc_rootaclk tc') chn) 
    (tc_get_updated_nodes_join tc tc').
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using tree_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  rewrite -> List.Forall_forall in IH.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & -> & _ & Halllt & Halllt').
  rewrite -> List.Forall_forall in Halllt, Halllt'.
  pose proof (sublist_In Hsub) as Hsub_in.
  pose proof (tc_shape_inv_chn Hshape) as Hshape_ch.
  pose proof (tc_respect_chn Hrespect) as Hrespect_ch.
  simpl in Hshape_ch, Hrespect_ch.
  rewrite -> List.Forall_forall in Hshape_ch, Hrespect_ch.
  split.
  - constructor.
    + now simpl.
    + rewrite -> Forall_map, -> List.Forall_forall.
      intros ch Hin.
      apply IH; auto.
      firstorder.
  - constructor.
    + rewrite -> Forall_map, -> List.Forall_forall.
      simpl.
      intros ch Hin.
      specialize (Halllt' _ Hin).
      now destruct ch as [(?, ?, aclk) ?].
    + rewrite -> Forall_map, -> List.Forall_forall.
      intros ch Hin.
      apply IH; auto.
      firstorder.
Qed.

Corollary tc_get_updated_nodes_join_sound [tc'] (Hshape: tc_shape_inv tc')
  [tc] (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') :
  forall t, isSome (tr_getnode t (tc_get_updated_nodes_join tc tc')) = true ->
    tc_getclk t tc < tc_getclk t tc'.
Proof.
  pose proof (tc_get_updated_nodes_join_shape Hshape Hrespect Hroot_clk_le) as H.
  apply proj1, Foralltr_Forall_subtree in H.
  intros t Hres.

  rewrite <- tr_getnode_in_iff, -> in_map_iff in Hres.
  destruct Hres as (sub & <- & Hin).
  pose proof Hin as Einfo.
  apply in_map with (f:=tr_rootinfo) in Einfo.
  eapply prefixtr_flatten_info_incl in Einfo.
  2: apply tc_get_updated_nodes_join_is_prefix.
  rewrite -> in_map_iff in Einfo.
  destruct Einfo as (sub' & Einfo & Hin').
  pose proof (tr_rootinfo_id_inj Einfo) as Et.
  pose proof (tc_rootinfo_clk_inj Einfo) as Eclk.
  pose proof (id_nodup_find_self (tid_nodup Hshape)) as Hself.
  rewrite -> List.Forall_forall in H, Hself.
  specialize (H _ Hin).
  specialize (Hself _ Hin').
  rewrite -> Et in Hself.
  unfold tc_getclk at 2.
  unfold tr_getnode.
  rewrite -> Hself.
  congruence.
Qed.

Corollary tc_get_updated_nodes_join_complete [tc'] (Hshape': tc_shape_inv tc') : 
  forall [tc] (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc')
  t (Hlt : tc_getclk t tc < tc_getclk t tc'),
    (* this equality can be from the prefix property; no need to repeat *)
    (* base.fmap tr_rootinfo (tr_getnode t (tc_get_updated_nodes_join tc tc')) = 
    base.fmap tr_rootinfo (tr_getnode t tc'). *)
    isSome (tr_getnode t (tc_get_updated_nodes_join tc tc')) = true.
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using tree_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  unfold tc_getclk in Hlt at 2.
  cbn in Hlt |- *.
  destruct (eqdec u' t) as [ <- | Htneq ] eqn:Etdec.
  1: intuition.
  (* get sub inv *)
  assert (NoDup (map tr_rootid (flat_map tr_flatten chn'))) as Hnodup_chn'
    by (now apply tid_nodup, NoDup_cons_iff in Hshape').
  (* get the result of tc_get_updated_nodes_join_aux *)
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & Hsubmap & Hgetjoinres & Halllt & Halllt').
  rewrite -> Hsubmap.
  rewrite -> List.Forall_forall in Hgetjoinres, Halllt.

  destruct (find (has_same_id t) (flat_map tr_flatten chn')) as [ res | ] eqn:E.
  2: now destruct (tr_getnode t tc).
  simpl.
  apply trs_find_has_id in E.
  destruct E as (Hin & Et).
  rewrite -> in_flat_map in Hin.
  destruct Hin as (ch & Hin_ch & Hin).

  (* tc_rootclk res --> getclk t ch *)
  pose proof (id_nodup_find_self (trs:=tr_flatten ch)) as Hres_ch.
  removehead Hres_ch.
  2: apply tid_nodup in Hshape'; eapply id_nodup_trs_each; eauto.
  rewrite -> List.Forall_forall in Hres_ch.
  specialize (Hres_ch _ Hin).
  assert (tc_rootclk res = tc_getclk t ch) as Eclk_ch.
  1: subst t; unfold tc_getclk, tr_getnode; now rewrite -> Hres_ch.
  rewrite -> Eclk_ch in Hlt.
  pose proof (tc_shape_inv_chn Hshape') as Hshape_chn.
  pose proof (tc_respect_chn Hrespect) as Hrespect_chn.
  simpl in Hshape_chn, Hrespect_chn.
  rewrite -> List.Forall_forall in IH, Hshape_chn, Hrespect_chn.
  (* now decide in or not? *)
  destruct (in_dec tr_eqdec ch chn_u'') as [ Hin_ch' | Hnotin ].
  + (* use IH *)
    pose proof Hin_ch' as Hlt_ch.
    rewrite -> Halllt in Hlt_ch.
    2: assumption.
    specialize (IH _ Hin_ch (Hshape_chn _ Hin_ch) _ (Hrespect_chn _ Hin_ch) Hlt_ch _ Hlt).
    destruct (tr_getnode t (tc_get_updated_nodes_join tc ch)) as [ res' | ] eqn:E.
    2: discriminate.
    apply trs_find_has_id in E.
    destruct E as (Hres' & Et'').
    destruct (find (has_same_id t)
      (flat_map tr_flatten (map (tc_get_updated_nodes_join tc) chn_u''))) as [ res'' | ] eqn:Efind.
    * auto.
    * eapply find_none in Efind.
      2:{
        eapply in_flat_map_conv.
        2: apply Hres'.
        now apply in_map.
      }
      rewrite -> has_same_id_false in Efind.
      congruence.
  + (* make contradiction by tc_ge *)
    rewrite -> Hgetjoinres in Hnotin.
    2: assumption.
    eapply Foralltr_Forall_subtree, List.Forall_forall in Hnotin.
    2: apply Hin.
    subst t.
    destruct res as [(?, ?, ?) ?].
    simpl in *.
    lia.
Qed.

Corollary tc_get_updated_nodes_join_adequacy tc' (Hshape: tc_shape_inv tc')
  tc (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') t :
  tc_getclk t tc < tc_getclk t tc' <->
  isSome (tr_getnode t (tc_get_updated_nodes_join tc tc')) = true.
Proof.
  split; intros H.
  - now apply tc_get_updated_nodes_join_complete.
  - now apply tc_get_updated_nodes_join_sound.
Qed.

End TC_Get_Updated_Nodes_Join.

Section TC_Detach_Nodes.

Fact tc_detach_nodes_eta ni chn tcs :
  exists new_chn res res' new_chn', 
    List.split (map (tc_detach_nodes tcs) chn) = (new_chn, res) /\
    partition (fun tc' : treeclock => isSome (find (has_same_id (tr_rootid tc')) tcs)) new_chn = (res', new_chn') /\
    map (fun x : treeclock => fst (tc_detach_nodes tcs x)) chn = new_chn /\
    map (fun x : treeclock => snd (tc_detach_nodes tcs x)) chn = res /\
    filter (fun tc' : treeclock => isSome (find (has_same_id (tr_rootid tc')) tcs)) new_chn = res' /\
    filter (fun tc' : treeclock => negb (isSome (find (has_same_id (tr_rootid tc')) tcs))) new_chn = new_chn' /\
    tc_detach_nodes tcs (Node ni chn) = (Node ni new_chn', concat res ++ res').
Proof.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs) chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' => isSome (find (has_same_id (tr_rootid tc')) tcs)) new_chn)
    as (res', new_chn') eqn:Epar.
  pose proof Esplit.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  pose proof Epar.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
  now exists new_chn, res, res', new_chn'.
Qed.

(* turn the properties of forest in snd to those on fst *)

Lemma tc_detach_nodes_snd2fst_pre tcs tc :
  Forall (fun tc' => exists sub, In sub (flat_map tr_flatten (tr_rootchn tc)) /\ 
    tc' = fst (tc_detach_nodes tcs sub))
  (snd (tc_detach_nodes tcs tc)).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach.
  simpl.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  rewrite -> List.Forall_app, ! List.Forall_forall.
  split.
  - subst res.
    setoid_rewrite -> in_concat.
    setoid_rewrite -> in_map_iff.
    intros res_ch (? & (ch & <- & Hin_ch) & Hin).
    specialize (IH _ Hin_ch _ Hin).
    destruct IH as (sub & Hin_sub & ->).
    exists sub.
    split; [ | reflexivity ].
    eapply in_flat_map_conv; [ apply Hin_ch | ].
    rewrite -> (tree_recons ch).
    simpl; tauto.
  - subst res' new_chn.
    setoid_rewrite -> filter_In.
    setoid_rewrite -> in_map_iff.
    intros ? ((ch & <- & Hin_ch) & _).
    exists ch.
    split. 
    2: reflexivity.
    eapply in_flat_map_conv in Hin_ch; eauto.
    destruct ch as [(?, ?, ?) ?].
    simpl.
    intuition.
Qed.

Corollary tc_detach_nodes_snd2fst tcs tc :
  Forall (fun tc' => exists sub, In sub (tr_flatten tc) /\ 
    tc' = fst (tc_detach_nodes tcs sub))
  (snd (tc_detach_nodes tcs tc)).
Proof.
  eapply Forall_impl.
  2: apply tc_detach_nodes_snd2fst_pre.
  simpl.
  intros ? (sub & Hin & ->).
  rewrite (tree_recons tc).
  simpl.
  eauto.
Qed.

Lemma tc_detach_nodes_dom_incl tcs tc :
  Forall (fun tc' => isSome (find (has_same_id (tr_rootid tc')) tcs) = true)
  (snd (tc_detach_nodes tcs tc)).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach.
  simpl.
  rewrite -> List.Forall_app, ! List.Forall_forall.
  split.
  - subst res.
    setoid_rewrite -> in_concat.
    setoid_rewrite -> in_map_iff.
    intros res_ch (? & (ch & <- & Hin_ch) & Hin).
    eapply IH; eauto.
  - subst res' new_chn.
    setoid_rewrite -> filter_In.
    setoid_rewrite -> in_map_iff.
    intros ? ((ch & <- & Hin_ch) & ?).
    intuition.
Qed.

Lemma tc_detach_nodes_tcs_congr tcs1 tcs2 
  (H : forall x, In x (map tr_rootid tcs1) <-> In x (map tr_rootid tcs2)) tc :
  tc_detach_nodes tcs1 tc = tc_detach_nodes tcs2 tc.
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  simpl.
  rewrite -> map_ext_Forall with (g:=(tc_detach_nodes tcs2)); auto.
  destruct (List.split (map (tc_detach_nodes tcs2) chn)) as (new_chn, res) eqn:Esplit.
  rewrite -> partition_ext_Forall with (g:=(fun tc' => isSome (find (has_same_id (tr_rootid tc')) tcs2))); auto.
  apply Forall_forall.
  intros tc' _.
  apply eq_iff_eq_true.
  now rewrite <- ! trs_find_in_iff.
Qed.

Lemma tc_detach_nodes_fst_is_prefix tcs tc :
  prefixtr (fst (tc_detach_nodes tcs tc)) tc.
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach.
  simpl.
  subst new_chn.
  rewrite -> map_filter_comm in Enew_chn'.
  match type of Enew_chn' with map _ (filter ?ff ?ll) = _ => 
    remember (filter ff ll) as chn_sub;
    remember ff as fb
  end.
  econstructor.
  1: apply filter_sublist with (f:=fb).
  subst new_chn'.
  apply Forall_filter with (f:=fb) in IH.
  rewrite <- Heqchn_sub in IH |- *.
  clear -IH.
  induction chn_sub as [ | ch chn ].
  - reflexivity.
  - simpl.
    rewrite -> List.Forall_cons_iff in IH. 
    constructor; firstorder.
Qed.

Corollary tc_detach_nodes_snd_is_subprefix tcs tc :
  Forall (fun tc' => exists sub, In sub (tr_flatten tc) /\
    prefixtr tc' sub) (snd (tc_detach_nodes tcs tc)).
Proof.
  pose proof (tc_detach_nodes_snd2fst tcs tc) as Hto.
  rewrite -> List.Forall_forall in Hto |- *.
  intros sub' Hin'.
  specialize (Hto sub' Hin').
  destruct Hto as (sub & Hin & ->).
  pose proof (tc_detach_nodes_fst_is_prefix tcs sub).
  eauto.
Qed.

Corollary tc_detach_nodes_fst_rootinfo_same tcs tc : 
  tr_rootinfo (fst (tc_detach_nodes tcs tc)) = tr_rootinfo tc.
Proof. erewrite prefixtr_rootinfo_same; [ reflexivity | apply tc_detach_nodes_fst_is_prefix ]. Qed.

Lemma tc_detach_nodes_tcs_app_fst tcs1 tcs2 tc :
  fst (tc_detach_nodes tcs2 (fst (tc_detach_nodes tcs1 tc))) =
  fst (tc_detach_nodes (tcs1 ++ tcs2) tc).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs1) as (new_chn1 & res1 & res1' & new_chn1' & _ & _ & Enew_chn1 & Eres1 & Eres1' & Enew_chn1' & Edetach1).
  pose proof (tc_detach_nodes_eta ni chn (tcs1 ++ tcs2)) as (new_chn & res & res' & new_chn' & _ & _ & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach1, Edetach.
  cbn delta [fst] beta iota.
  pose proof (tc_detach_nodes_eta ni new_chn1' tcs2) as (new_chn2 & res2 & res2' & new_chn2' & _ & _ & Enew_chn2 & Eres2 & Eres2' & Enew_chn2' & Edetach2).
  rewrite Edetach2.
  simpl.
  f_equal.
  subst.
  rewrite <- (map_ext_Forall _ _ IH).

  (* local induction to avoid too much manipulation *)
  clear Edetach1 Edetach2 Edetach ni IH. 
  induction chn as [ | ch chn IH ]; simpl; auto.
  pose proof (tc_detach_nodes_fst_is_prefix tcs1) as Hpf1.
  pose proof (tc_detach_nodes_fst_is_prefix tcs2) as Hpf2.
  rewrite ! (prefixtr_rootid_same (Hpf2 _)).
  rewrite ! (prefixtr_rootid_same (Hpf1 _)).
  rewrite find_app.
  destruct (find (has_same_id (tr_rootid ch)) tcs1) as [ res1 | ] eqn:E1 in |- *; simpl.
  - apply IH.
  - rewrite ! (prefixtr_rootid_same (Hpf2 _)).
    rewrite ! (prefixtr_rootid_same (Hpf1 _)).
    destruct (find (has_same_id (tr_rootid ch)) tcs2) as [ res2 | ] eqn:E2; simpl.
    + apply IH.
    + f_equal; apply IH.
Qed.

Lemma tc_detach_nodes_tcs_app_snd tcs1 tcs2 tc :
  Permutation (snd (tc_detach_nodes (tcs1 ++ tcs2) tc))
  (snd (tc_detach_nodes tcs2 (fst (tc_detach_nodes tcs1 tc))) ++
    map fst (map (tc_detach_nodes tcs2) (snd (tc_detach_nodes tcs1 tc))) ++
    flat_map snd (map (tc_detach_nodes tcs2) (snd (tc_detach_nodes tcs1 tc)))).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs1) as (new_chn1 & res1 & res1' & new_chn1' & _ & _ & Enew_chn1 & Eres1 & Eres1' & Enew_chn1' & Edetach1).
  pose proof (tc_detach_nodes_eta ni chn (tcs1 ++ tcs2)) as (new_chn & res & res' & new_chn' & _ & _ & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach1, Edetach.
  cbn delta [fst snd] beta iota.
  pose proof (tc_detach_nodes_eta ni new_chn1' tcs2) as (new_chn2 & res2 & res2' & new_chn2' & _ & _ & Enew_chn2 & Eres2 & Eres2' & Enew_chn2' & Edetach2).
  rewrite Edetach2.
  simpl.

  (* now, manipulate *)
  pose proof IH as Hperm.
  apply Permutation_Forall_flat_map in Hperm.
  rewrite -> flat_map_concat_map, -> Eres in Hperm at 1.
  rewrite -> ! Permutation_flat_map_innerapp_split in Hperm.
  rewrite -> flat_map_concat_map in Hperm at 1.
  rewrite <- map_map with (g:=fun x => snd (tc_detach_nodes tcs2 x)) in Hperm at 1.
  rewrite -> Enew_chn1, <- flat_map_concat_map in Hperm.
  (* split new_chn1, get res1' and res2 *)
  match type of Hperm with Permutation ?al ?bl => 
    eapply Permutation_trans with (l:=al) (l':=bl) in Hperm end.
  2: apply Permutation_app; [ | reflexivity ].
  2: apply Permutation_flat_map, Permutation_split_combine.
  rewrite -> Eres1' in Hperm.
  rewrite -> Enew_chn1' in Hperm.
  rewrite -> flat_map_app, -> 2 flat_map_concat_map, -> Eres2 in Hperm.
  rewrite <- map_map with (g:=snd), <- flat_map_concat_map in Hperm.

  (* TODO the following should be revised, but maybe not for now? *)

  rewrite -> ! flat_map_concat_map with (l:=chn) in Hperm.
  rewrite <- ! map_map with (f:=fun x => map (tc_detach_nodes tcs2) (snd (tc_detach_nodes tcs1 x))) in Hperm.
  rewrite <- ! map_map with (f:=fun x => (snd (tc_detach_nodes tcs1 x))) in Hperm.
  rewrite -> ! Eres1 in Hperm.
  rewrite <- ! concat_map in Hperm.

  (* ? *)
  assert (concat (map (flat_map snd) (map (map (tc_detach_nodes tcs2)) res1)) = 
    flat_map snd (map (tc_detach_nodes tcs2) (concat res1))) as EE.
  {
    clear.
    induction res1; auto.
    simpl. rewrite IHres1. now rewrite map_app, flat_map_app.
  }
  rewrite EE in Hperm.

  rewrite ! map_app, flat_map_app.
  match type of Hperm with Permutation _ ?al =>
    transitivity (al ++ (res2' ++ map fst (map (tc_detach_nodes tcs2) res1'))) end.
  2: list.solve_Permutation.
  apply Permutation_app; auto.

  subst.
  clear -chn.
  rewrite -> ! map_filter_comm, -> ! map_map.
  erewrite -> map_ext; [ | intros; now rewrite tc_detach_nodes_tcs_app_fst ].
  f_equal.
  erewrite -> filter_ext with (l:=filter _ _); [ | intros; now rewrite tc_detach_nodes_tcs_app_fst ].
  rewrite <- map_app.
  apply Permutation_map.
  repeat match goal with |- context[filter ?ff ?ll] => 
    match ff with context[fst] => 
    erewrite -> filter_ext with (f:=ff) (l:=ll); [ | intros x; unfold tr_rootid; 
      rewrite (prefixtr_rootinfo_same (tc_detach_nodes_fst_is_prefix _ _)); fold (tr_rootid x); reflexivity ]
    end
  end.
  induction chn as [ | ch chn IH ]; simpl; auto.
  rewrite find_app.
  destruct (find (has_same_id (tr_rootid ch)) tcs1) as [ res1 | ] eqn:E1, 
    (find (has_same_id (tr_rootid ch)) tcs2) as [ res2 | ] eqn:E2; 
    simpl; try rewrite E1; try rewrite E2; simpl; try rewrite IH.
  all: list.solve_Permutation.
Qed.

(* a niche case *)
Fact tc_detach_nodes_prepend_child ni ch chn tcs 
  (H : find (has_same_id (tr_rootid ch)) tcs = None) :
  let: (pivot_ch, forest_ch) := tc_detach_nodes tcs ch in
  let: (pivot_main, forest_main) := tc_detach_nodes tcs (Node ni chn) in
  let: Node ni' chn' := pivot_main in
  tc_detach_nodes tcs (Node ni (ch :: chn)) = 
  (Node ni' (pivot_ch :: chn'), forest_ch ++ forest_main).
Proof.
  destruct (tc_detach_nodes tcs ch) as (pivot_ch, forest_ch) eqn:Ech.
  pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & _ & _ & _ & _ & Edetach).
  rewrite Edetach.
  simpl.
  rewrite Ech, Esplit.
  simpl.
  rewrite -> Epar.
  unfold tr_rootid in H |- * at 1.
  replace pivot_ch with (fst (tc_detach_nodes tcs ch)) by now rewrite Ech.
  rewrite ! (prefixtr_rootinfo_same (tc_detach_nodes_fst_is_prefix tcs ch)), Ech, H.
  simpl.
  now rewrite app_assoc.
Qed.

(* permutation is much more clear than mutual In here *)

Lemma tc_detach_nodes_dom_partition tcs tc :
  Permutation (map tr_rootinfo (tr_flatten tc))
    (map tr_rootinfo (tr_flatten (fst (tc_detach_nodes tcs tc)) ++ 
      (flat_map tr_flatten (snd (tc_detach_nodes tcs tc))))).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & forest & forest' & new_chn' & _ & Epar & Enew_chn & Eres & _ & _ & Edetach).
  rewrite Edetach.
  simpl.
  constructor.
  rewrite -> flat_map_app, -> ! map_app.
  etransitivity.
  2:{
    rewrite -> Permutation_app_comm, <- app_assoc, <- map_app, <- flat_map_app.
    apply Permutation_app_head.
    match type of Epar with partition ?f ?l = (?a, ?b) => 
      replace a with (fst (partition f l)) by (rewrite -> Epar; now simpl);
      replace b with (snd (partition f l)) by (rewrite -> Epar; now simpl)
    end.
    rewrite <- Permutation_partition.
    reflexivity.
  }
  (* TODO seems a local induction is needed? *)
  clear -chn IH Enew_chn Eres.
  revert new_chn forest IH Enew_chn Eres.
  induction chn as [ | ch chn IH2 ]; intros.
  all: simpl in Enew_chn, Eres |- *; subst.
  - reflexivity.
  - apply Forall_cons_iff in IH.
    destruct IH as (HH & IH).
    specialize (IH2 _ _ IH eq_refl eq_refl).
    simpl.
    rewrite -> flat_map_app, -> ! map_app, -> IH2, -> HH, -> map_app.
    list.solve_Permutation.
Qed.

Corollary tc_detach_nodes_intact_pre tcs tc :
  snd (tc_detach_nodes tcs tc) = nil -> fst (tc_detach_nodes tcs tc) = tc.
Proof.
  (* analytic *)
  destruct (tc_detach_nodes tcs tc) as (pivot, forest) eqn:E.
  simpl.
  intros ->.
  apply prefixtr_size_eq_tr_eq.
  1: eapply eq_ind_r with (y:=pivot); [ apply tc_detach_nodes_fst_is_prefix | ]; now rewrite E.
  pose proof (tc_detach_nodes_dom_partition tcs tc) as Hperm.
  rewrite E, app_nil_r in Hperm.
  simpl in Hperm.
  apply Permutation_length in Hperm.
  now rewrite ! map_length in Hperm.
Qed.

Corollary tc_detach_nodes_intact tcs tc
  (Hdj : forall t, In t (map tr_rootid (flat_map tr_flatten (tr_rootchn tc))) -> 
    In t (map tr_rootid tcs) -> False) :
  tc_detach_nodes tcs tc = (tc, nil).
Proof.
  destruct (tc_detach_nodes tcs tc) as (pivot, forest) eqn:E.
  destruct forest as [ | tc0 ? ].
  - f_equal.
    eapply eq_ind_r with (y:=pivot); [ apply tc_detach_nodes_intact_pre | ].
    all: rewrite E; reflexivity.
  - pose proof (tc_detach_nodes_dom_incl tcs tc) as Htmp.
    pose proof (tc_detach_nodes_snd2fst_pre tcs tc) as Htmp2.
    rewrite E in Htmp, Htmp2.
    simpl in Htmp, Htmp2.
    rewrite -> Forall_cons_iff in Htmp, Htmp2.
    apply proj1 in Htmp, Htmp2.
    rewrite <- trs_find_in_iff in Htmp.
    destruct Htmp2 as (sub & Hin%(in_map tr_rootid) & ->).
    rewrite (tr_rootinfo_id_inj (prefixtr_rootinfo_same (tc_detach_nodes_fst_is_prefix _ _))) in Htmp.
    firstorder.
Qed.

Corollary tc_detach_nodes_dom_partition' tcs tc :
  Permutation (map tr_rootinfo (tr_flatten tc))
    (map tr_rootinfo (tr_flatten (fst (tc_detach_nodes tcs tc))) ++ 
      map tr_rootinfo (snd (tc_detach_nodes tcs tc)) ++ 
      map tr_rootinfo (flat_map tr_flatten (flat_map tr_rootchn (snd (tc_detach_nodes tcs tc))))).
Proof.
  etransitivity; [ apply tc_detach_nodes_dom_partition with (tcs:=tcs) | ].
  rewrite -> map_app.
  apply Permutation_app_head. 
  rewrite <- map_app.
  now apply Permutation_map, tr_flatten_root_chn_split.
Qed.

Corollary tc_detach_nodes_tid_nodup tcs tc 
  (Hnodup : NoDup (map tr_rootid (tr_flatten tc))) :
  NoDup (map tr_rootid (flat_map tr_flatten (snd (tc_detach_nodes tcs tc)))) /\
  (forall t, 
    In t (map tr_rootid (tr_flatten (fst (tc_detach_nodes tcs tc)))) ->
    In t (map tr_rootid (flat_map tr_flatten (snd (tc_detach_nodes tcs tc)))) -> False) /\
  NoDup (map tr_rootid (tr_flatten (fst (tc_detach_nodes tcs tc)))).
Proof.
  pose proof (tc_detach_nodes_dom_partition tcs tc) as Hperm%Permutation_rootinfo2rootid.
  pose proof (Permutation_NoDup Hperm Hnodup) as Htmp.
  rewrite -> map_app, <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Htmp.
  repeat setoid_rewrite -> base.elem_of_list_In in Htmp.
  intuition.
Qed.

(* there will not be any tid in tcs that is also inside the pivot tree *)

Lemma tc_detach_nodes_dom_excl tcs tc :
  forall t (Htarg : isSome (find (has_same_id t) tcs) = true)
  res (Hin : In res (tr_flatten (fst (tc_detach_nodes tcs tc)))) (Et : tr_rootid res = t),
  res = (fst (tc_detach_nodes tcs tc)).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & forest & forest' & new_chn' & _ & _ & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach in Hin |- *.
  simpl in Hin |- *.
  destruct Hin as [ | Hin ].
  1: congruence.
  (* now contradiction part *)
  rewrite -> List.Forall_forall in IH.
  apply in_flat_map in Hin.
  destruct Hin as (new_ch & Hin_ch & Hin).
  subst new_chn' new_chn.
  apply filter_In in Hin_ch.
  destruct Hin_ch as (Hin_ch & Htidnotin).
  apply in_map_iff in Hin_ch.
  destruct Hin_ch as (ch & <- & Hin_ch).
  subst t.
  eapply IH in Hin; eauto.
  subst res.
  now rewrite Htarg in Htidnotin.
Qed.

(* FIXME: use this alternative version to replace/optimize the original version? *)
Corollary tc_detach_nodes_dom_excl' tcs tc t (Htarg : isSome (find (has_same_id t) tcs) = true) :
  ~ In t (map tr_rootid (flat_map tr_flatten (tr_rootchn (fst (tc_detach_nodes tcs tc))))).
Proof.
  destruct (fst (tc_detach_nodes tcs tc)) as [ni chn] eqn:E.
  simpl.
  intros (ch & Hin_ch & (res & Eid & H)%in_map_iff)%map_flat_map_In.
  apply tc_detach_nodes_dom_excl with (res:=res) (tc:=tc) in Htarg; try assumption.
  2: rewrite E; apply subtr_trans with (tr':=ch); [ assumption | apply subtr_chn; now simpl ].
  (* contradiction *)
  apply self_not_in_tr_flatten_chn with (tr:=Node ni chn), in_flat_map.
  rewrite Htarg, E in H.
  eauto.
Qed.

Corollary tc_detach_nodes_dom_excl'' tcs tc t (Htarg : isSome (find (has_same_id t) tcs) = true) :
  ~ In t (map tr_rootid (flat_map tr_flatten (flat_map tr_rootchn (snd (tc_detach_nodes tcs tc))))).
Proof.
  intros (ch & (sub & Hpick & Hin_ch)%in_flat_map & Hin_sub)%map_flat_map_In.
  pose proof (tc_detach_nodes_snd2fst tcs tc) as Htmp.
  rewrite -> List.Forall_forall in Htmp.
  specialize (Htmp _ Hpick).
  destruct Htmp as (sub' & Hin_sub' & ->).
  eapply tc_detach_nodes_dom_excl'; [ apply Htarg | ].
  eapply map_flat_map_In_conv; eauto.
Qed.

(* only mutual in for now *)
(* FIXME: it may be possible that we can prove such iff directly? *)
Corollary tc_detach_nodes_dom_incl_iff tcs tc 
  (* FIXME: the "Hnotin" may not be compatible with the monotone join operation. consider move this constraint in the future *)
  (Hnotin : find (has_same_id (tr_rootid tc)) tcs = None) :
  forall ni,
    In ni (map tr_rootinfo (filter (fun sub => find (has_same_id (tr_rootid sub)) tcs) (tr_flatten tc))) <-> 
    In ni (map tr_rootinfo (snd (tc_detach_nodes tcs tc))).
Proof.
  intros.
  pose proof (tc_detach_nodes_dom_partition' tcs tc) as Hperm.
  rewrite <- ! map_app in Hperm.
  (* ... have to use map_filter_comm *)
  pose proof (map_filter_comm tr_rootinfo (fun ni => find (has_same_id (info_tid ni)) tcs) (tr_flatten tc)) as Htmp.
  simpl in Htmp.
  unfold tr_rootid.
  rewrite <- Htmp, -> filter_In.
  clear Htmp.
  erewrite -> Permutation_in_mutual at 1; [ | apply Hperm ].
  rewrite -> ! map_app, -> ! in_app_iff.
  split; intros H.
  - destruct H as (H & Htarg).
    (* TODO why this Hlocal? *)
    assert (forall ni0 tcs0, ~ In (info_tid ni0) (map tr_rootid tcs0) -> ~ In ni0 (map tr_rootinfo tcs0)) as Hlocal.
    {
      intros.
      intros (sub & <- & Hq)%in_map_iff.
      apply in_map with (f:=tr_rootid) in Hq.
      unfold tr_rootid in Hq at 1.
      congruence.
    } 
    pose proof (tc_detach_nodes_dom_excl' _ tc _ Htarg) as H'%Hlocal.
    pose proof (tc_detach_nodes_dom_excl'' _ tc _ Htarg) as H''%Hlocal.
    destruct (fst (tc_detach_nodes tcs tc)) as [ni0 chn] eqn:E.
    simpl in *.
    assert (ni <> ni0).
    {
      pose proof (tc_detach_nodes_fst_rootinfo_same tcs tc) as Einfo.
      rewrite -> E in Einfo.
      unfold tr_rootid in Hnotin.
      rewrite <- Einfo in Hnotin.
      simpl in Hnotin.
      intros <-.
      now rewrite Hnotin in Htarg.
    }
    eqsolve.
  - split; [ tauto | ].
    apply in_map_iff in H.
    destruct H as (sub & <- & H).
    pose proof (tc_detach_nodes_dom_incl tcs tc) as Htmp.
    rewrite -> List.Forall_forall in Htmp.
    apply Htmp.
    eauto.
Qed.

Corollary tc_detach_nodes_dom_partition'' tcs tc (Hnotin : find (has_same_id (tr_rootid tc)) tcs = None) 
  (Hnodup : List.NoDup (map tr_rootid (tr_flatten tc))) :
  Permutation
    (map tr_rootinfo (tr_flatten (fst (tc_detach_nodes tcs tc))) ++
     map tr_rootinfo (flat_map tr_flatten (flat_map tr_rootchn
            (snd (tc_detach_nodes tcs tc)))))
    (map tr_rootinfo (filter (fun sub => 
      negb (find (has_same_id (tr_rootid sub)) tcs)) (tr_flatten tc))) /\
  Permutation
    (map tr_rootinfo (snd (tc_detach_nodes tcs tc)))
    (map tr_rootinfo (filter (fun sub => find (has_same_id (tr_rootid sub)) tcs) (tr_flatten tc))).
Proof.
  apply base.and_wlog_l.
  - intros Hperm'.
    eapply Permutation_app_inv_l.
    etransitivity.
    2: rewrite <- map_app; apply Permutation_map, Permutation_split_combine.
    etransitivity.
    2: symmetry; apply tc_detach_nodes_dom_partition' with (tcs:=tcs).
    etransitivity.
    2: apply Permutation_app_swap_app.
    now apply Permutation_app_tail.
  - unfold tr_rootid in Hnodup.
    rewrite <- map_map with (f:=tr_rootinfo) in Hnodup.
    apply NoDup_map_inv in Hnodup.
    apply NoDup_Permutation.
    + eapply Permutation_NoDup in Hnodup.
      2: apply tc_detach_nodes_dom_partition' with (tcs:=tcs).
      now rewrite ! NoDup_app_ in Hnodup.
    + (* ... have to use map_filter_comm *)
      pose proof (map_filter_comm tr_rootinfo (fun ni => find (has_same_id (info_tid ni)) tcs) (tr_flatten tc)) as Htmp.
      simpl in Htmp.
      unfold tr_rootid.
      rewrite <- Htmp.
      now apply NoDup_filter.
    + intros.
      now rewrite -> tc_detach_nodes_dom_incl_iff.
Qed.

Corollary tc_shape_inv_tc_detach_nodes_fst tcs tc 
  (Hshape : tc_shape_inv tc) :
  tc_shape_inv (fst (tc_detach_nodes tcs tc)).
Proof.
  pose proof (tc_detach_nodes_fst_is_prefix tcs tc) as Hprefix.
  eapply tc_shape_inv_prefix_preserve; eauto.
Qed.

Corollary tc_shape_inv_tc_detach_nodes_snd tcs tc 
  (Hshape : tc_shape_inv tc) :
  Forall tc_shape_inv (snd (tc_detach_nodes tcs tc)).
Proof.
  pose proof (tc_detach_nodes_snd2fst tcs tc) as Hto.
  pose proof (tc_shape_inv_sub _ Hshape) as Hshape_sub.
  rewrite -> List.Forall_forall in Hto |- *.
  intros sub' Hin'.
  specialize (Hto sub' Hin').
  destruct Hto as (sub & Hin & ->).
  eapply Foralltr_subtr in Hshape_sub; [ | apply Hin ].
  now apply tc_shape_inv_tc_detach_nodes_fst.
Qed.

End TC_Detach_Nodes.

Section TC_Attach_Nodes.

(* more abstracted version *)

Lemma forest_recombine_pre tcs l
  (Hnodup : NoDup (map tr_rootid tcs)) (Hnodup' : NoDup l) 
  (Hdomincl : incl (map tr_rootid tcs) l) :
  Permutation (map Some tcs) 
    (filter isSome (map (fun t => find (has_same_id t) tcs) l)).
Proof.
  apply NoDup_Permutation.
  - apply FinFun.Injective_map_NoDup.
    1: congruence.
    now apply NoDup_map_inv with (f:=tr_rootid).
  - (* no much good way ... induction? *)
    clear Hdomincl.
    revert tcs Hnodup.
    induction l as [ | t l IH ]; intros.
    1: constructor.
    apply NoDup_cons_iff in Hnodup'.
    destruct Hnodup' as (Hnotin & Hnodup').
    simpl.
    destruct (find (has_same_id t) tcs) as [ res | ] eqn:E; simpl.
    + constructor.
      2: now apply IH.
      intros HH.
      apply filter_In, proj1, in_map_iff in HH.
      destruct HH as (u & E' & Hin').
      apply find_some, proj2, has_same_tid_true in E, E'.
      congruence.
    + now apply IH.
  - intros ot.
    split; intros Hin.
    + rewrite -> in_map_iff in Hin.
      destruct Hin as (sub & <- & Hin).
      apply filter_In.
      split; [ | auto ].
      apply in_map_iff.
      pose proof (in_map tr_rootid _ _ Hin) as Hin'.
      pose proof (id_nodup_find_self _ Hnodup) as Hself.
      rewrite -> List.Forall_forall in Hself.
      specialize (Hself _ Hin).
      eauto.
    + apply filter_In in Hin.
      destruct ot as [ res | ]; [ | intuition discriminate ].
      apply proj1, in_map_iff in Hin.
      destruct Hin as (t & Hin & _).
      apply find_some in Hin.
      now apply in_map.
Qed.

Corollary tc_detach_nodes_forest_recombine_pre tcs tc 
  (Hnodup : NoDup (map tr_rootid (tr_flatten tc)))
  (Hnodup' : NoDup (map tr_rootid tcs)) :
  Permutation
    (map Some (snd (tc_detach_nodes tcs tc)))
    (filter isSome (map
      (fun t => find (has_same_id t) (snd (tc_detach_nodes tcs tc))) 
        (map tr_rootid tcs))).
Proof.
  apply forest_recombine_pre.
  - pose proof (tc_detach_nodes_tid_nodup tcs tc Hnodup) as Hnodup_forest.
    now apply proj1, tid_nodup_root_chn_split, proj1 in Hnodup_forest.
  - assumption.
  - (* use dom incl *)
    pose proof (tc_detach_nodes_dom_incl tcs tc) as Hdomincl.
    rewrite -> List.Forall_forall in Hdomincl.
    hnf.
    repeat setoid_rewrite -> in_map_iff.
    setoid_rewrite <- trs_find_in_iff in Hdomincl.
    setoid_rewrite -> in_map_iff in Hdomincl.
    intros ? (sub & <- & Hin).
    firstorder.
Qed.

(* simulation *)

Lemma forest_chn_recombine tcs l 
  (Hperm : Permutation (map Some tcs) 
    (filter isSome (map (fun t => find (has_same_id t) tcs) l))) :
  Permutation (flat_map tr_rootchn tcs)
    (flat_map (fun t => match find (has_same_id t) tcs with
      | Some res => tr_rootchn res
      | None => nil
      end) l).
Proof.
  pose (f:=fun ot => match ot with Some tc => tr_rootchn tc | None => nil end).
  apply Permutation_flat_map with (g:=f) in Hperm.
  match type of Hperm with Permutation ?a _ => transitivity a end.
  1:{
    clear -thread_eqdec tcs.
    induction tcs as [ | tc tcs IH ].
    1: reflexivity.
    simpl.
    now apply Permutation_app_head.
  }
  match type of Hperm with Permutation _ ?a => transitivity a end.
  2:{
    clear -thread_eqdec l.
    induction l as [ | x l IH ].
    1: reflexivity.
    simpl.
    destruct (find (has_same_id x) tcs) eqn:E; simpl.
    - now apply Permutation_app_head.
    - assumption.
  }
  assumption.
Qed.

Corollary tc_detach_nodes_forest_recombine tcs tc 
  (Hnodup : NoDup (map tr_rootid (tr_flatten tc)))
  (Hnodup' : NoDup (map tr_rootid tcs)) :
  Permutation
    (flat_map tr_rootchn (snd (tc_detach_nodes tcs tc)))
    (flat_map
      (fun t : thread =>
      match find (has_same_id t) (snd (tc_detach_nodes tcs tc)) with
      | Some res => tr_rootchn res
      | None => nil
      end) (map tr_rootid tcs)).
Proof.
  pose proof (tc_detach_nodes_forest_recombine_pre _ _ Hnodup Hnodup') as Hperm.
  now apply forest_chn_recombine.
Qed.

(* a very special case for the overlay tree *)

Inductive simple_overlaytc (P : thread -> list treeclock) : treeclock -> treeclock -> Prop :=
  simple_overlaytc_intro : forall ni chn chn' chn'',
    chn'' = P (info_tid ni) ->
    Forall2 (simple_overlaytc P) chn chn' ->
    simple_overlaytc P (Node ni chn) (Node ni (chn' ++ chn'')).

Fact simple_overlaytc_inv (P : thread -> list treeclock) ni1 ni2 chn1 chn2 
  (Hso: simple_overlaytc P (Node ni1 chn1) (Node ni2 chn2)) :
  exists prefix_chn suffix_chn, ni1 = ni2 /\ chn2 = prefix_chn ++ suffix_chn /\
    suffix_chn = P (info_tid ni1) /\ Forall2 (simple_overlaytc P) chn1 prefix_chn /\
    map tr_rootinfo chn1 = map tr_rootinfo prefix_chn.
Proof. 
  inversion Hso; subst. 
  eexists. eexists. 
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ | split ]; auto.
  match goal with HH : Forall2 (simple_overlaytc P) _ _ |- _ => 
    clear -HH; induction HH as [ | [? ?] [? ?] chn1 chn2 H H' IH ] end.
  - auto.
  - inversion H.
    simpl.
    congruence.
Qed.

Lemma tc_attach_nodes_result forest tc :
  simple_overlaytc (fun t =>
    match List.find (has_same_id t) forest with
    | Some res => tr_rootchn res
    | None => nil
    end) tc (tc_attach_nodes forest tc).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  simpl.
  constructor.
  - auto.
  - clear -IH.
    induction chn as [ | ch chn ].
    1: constructor.
    apply List.Forall_cons_iff in IH.
    destruct IH as (H & IH).
    constructor; firstorder.
Qed.
(*
Fact simple_overlaytc_rootinfo_same (P : thread -> list treeclock) tc tc'
  (Hoverlay : simple_overlaytc P tc tc') : tr_rootinfo tc' = tr_rootinfo tc.
Proof. destruct tc, tc', (simple_overlaytc_inv _ _ _ _ _ Hoverlay) as (? & ? & ?). simpl. intuition. Qed.
*)
Fact tc_attach_nodes_rootinfo_same forest tc : 
  tr_rootinfo (tc_attach_nodes forest tc) = tr_rootinfo tc.
Proof. now destruct tc. Qed.

Lemma simple_overlaytc_dom_info (P : thread -> list treeclock) tc : forall tc'
  (Hoverlay : simple_overlaytc P tc tc'),
  Permutation (map tr_rootinfo (tr_flatten tc'))
  ((map tr_rootinfo (tr_flatten tc)) ++
    (map tr_rootinfo (flat_map tr_flatten (flat_map P (map tr_rootid (tr_flatten tc)))))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  simpl.
  constructor.
  rewrite -> ! flat_map_app, -> ! map_app.
  etransitivity.
  1: apply Permutation_app_comm.
  etransitivity.
  2: apply Permutation_app_comm.
  rewrite <- app_assoc.
  apply Permutation_app_head.
  clear u clk aclk.
  induction Hcorr as [ | ch new_ch chn new_chn Hso Hcorr IH' ].
  - now simpl.
  - simpl in Hinfosame |- *.
    apply Forall_cons_iff in IH.
    destruct IH as (HH & IH).
    specialize (IH' IH).
    removehead IH'.
    2: congruence.
    repeat rewrite -> ? map_app, -> ? flat_map_app.
    match goal with |- Permutation _ ((?a ++ ?b) ++ (?c ++ ?d)) => 
      remember a as la; remember b as lb; remember c as lc; remember d as ld;
      transitivity ((lc ++ la) ++ (lb ++ ld)) end.
    2:{
      rewrite -> ! app_assoc with (n:=ld).
      apply Permutation_app_tail.
      rewrite <- 2 app_assoc.
      apply Permutation_app_rot.
    }
    apply HH in Hso.
    now apply Permutation_app.
Qed.

Corollary tc_attach_nodes_dom_info subtree_tc' tc 
  (* these two conditions are required the trees of the forest appear at most once in the result *)
  (Hnodup : NoDup (map tr_rootid (tr_flatten tc)))
  (Hnodup' : NoDup (map tr_rootid (tr_flatten subtree_tc'))) :
  Permutation (map tr_rootinfo (tr_flatten (tc_attach_nodes (snd (tc_detach_nodes (tr_flatten subtree_tc') tc)) subtree_tc')))
  ((map tr_rootinfo (tr_flatten subtree_tc')) ++
    (map tr_rootinfo (flat_map tr_flatten (flat_map tr_rootchn (snd (tc_detach_nodes (tr_flatten subtree_tc') tc)))))).
Proof.
  pose proof (tc_attach_nodes_result (snd (tc_detach_nodes (tr_flatten subtree_tc') tc)) subtree_tc') as Hso.
  apply simple_overlaytc_dom_info in Hso.
  etransitivity.
  1: apply Hso.
  apply Permutation_app_head, Permutation_map, Permutation_flat_map.
  symmetry.
  now apply tc_detach_nodes_forest_recombine.
Qed.

(* TODO this is not needed for our current purpose. for now, just keep it *)
(*
Lemma simple_overlaytc_nodup (P : thread -> list treeclock) 
  (Hnodup_small : forall t, List.NoDup (map tr_rootid (flat_map tr_flatten (P t))))
  tc tc'
  (Hoverlay : simple_overlaytc P tc tc')
  (Hnodup_forest : NoDup (map tr_rootid (flat_map tr_flatten (flat_map P (map tr_rootid (tr_flatten tc))))))
  (Hnodup : List.NoDup (map tr_rootid (tr_flatten tc)))
  (* a neat choice to write None or neg here ... *)
  (Hdomexcl : forall t, tr_getnode t tc -> 
    forall t', ~ find (has_same_id t) (flat_map tr_flatten (P t'))) :
  List.NoDup (map tr_rootid (tr_flatten tc')).
Proof.
  eapply Permutation_NoDup.
  1:{
    symmetry.
    unfold tr_rootid.
    rewrite <- map_map.
    apply Permutation_map.
    eapply simple_overlaytc_dom_info.
    apply Hoverlay.
  }
  rewrite -> map_app.
  rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
  split; [ | split ].
  - now rewrite -> map_map.
  - repeat setoid_rewrite -> base.elem_of_list_In.
    rewrite -> ! map_map.
    fold tr_rootid.
    setoid_rewrite -> map_flat_map_In.
    setoid_rewrite -> in_flat_map.
    intros t Hin (ch & (u & Hin' & Hin_ch) & Hin_sub').
    rewrite -> tr_getnode_in_iff in Hin.
    pose proof (map_flat_map_In_conv _ _ _ _ _ Hin_ch Hin_sub').
    rewrite -> trs_find_in_iff in H.
    apply (Hdomexcl _ Hin _ H).
  - now rewrite -> map_map.
Qed.
*)

Lemma tc_shape_inv_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat)
  (Hcomple : forall t, exists aclk, tc_shape_inv (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hshape : tc_shape_inv tc)
  (* needed for aclk upperbound *)
  (Hclk_lt : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  (* needed for aclk sorted *)
  (Haclk_lt : Foralltr (fun tc' => let: Node ni chn := tc' in
    Forall (fun tc' => Q (info_tid ni) <= tc_rootaclk tc') chn) tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  Foralltr tc_chn_aclk_ub tc' /\ Foralltr tc_chn_aclk_decsorted tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  rewrite -> List.Forall_forall in IH.
  pose proof (Forall2_forall_exists_r _ _ _ Hcorr) as Hcorr_inr.
  (* prepare *)
  pose proof (Hcomple u) as (aclk' & Hshape_sub).
  pose proof (tc_shape_inv_chn _ Hshape) as Hshape_chn.
  simpl in Hshape_chn.
  rewrite -> tc_shape_inv_conj_iff, -> ! Foralltr_cons_iff in Hshape_sub, Hshape.
  rewrite -> Foralltr_cons_iff in Haclk_lt, Hclk_lt.
  destruct Hshape_sub as (_ & (Ha & Ha') & (Hb & Hb')), 
    Hshape as (_ & (Ha'' & _) & (Hb'' & _)), 
    Haclk_lt as (Eaclk_lt & Haclk_lt), Hclk_lt as (Eclk_lt & Hclk_lt).
  simpl in Ha, Hb, Eaclk_lt, Eclk_lt, Ha'', Hb''.

  rewrite -> List.Forall_forall in Hshape_chn, Hclk_lt, Haclk_lt.

  (* TODO repetition elimination *)
  split.
  all: rewrite -> Foralltr_cons_iff, -> List.Forall_app.
  - split; [ | split ].
    + simpl.
      apply List.Forall_app.
      split.
      * unfold tc_rootaclk.
        hnf in Ha''.
        change (fun tc' => _) with (fun tc' => (fun ni => info_aclk ni <= clk) (tr_rootinfo tc')) in Ha'' |- *.
        rewrite <- Forall_map in Ha'' |- *.
        now rewrite <- Hinfosame.
      * eapply List.Forall_impl.
        2: apply Ha.
        simpl.
        lia.
    + rewrite -> List.Forall_forall.
      intros new_ch Hin_newch.
      pose proof (Hcorr_inr _ Hin_newch) as (ch & Hin_ch & Hso).
      (* now specialize (IH _ Hin_ch (Hshape_chn _ Hin_ch) (Haclk_bounded _ Hin_ch) _ Hso). *)
      eapply IH; eauto.
    + assumption.
  - split; [ | split ].
    + hnf.
      unfold tc_rootaclk.
      simpl.
      rewrite <- map_map, -> map_app, <- Hinfosame, <- map_app, -> map_map.
      fold tc_rootaclk.
      rewrite -> map_app.
      apply StronglySorted_app.
      * assumption.
      * assumption.
      * hnf in Ha, Ha'', Eaclk_lt.
        change (fun tc' => _) with (fun tc' => (fun a => a <= clk) (tc_rootaclk tc')) in Ha''.
        change (fun tc' => _) with (fun tc' => (fun a => a <= Q u) (tc_rootaclk tc')) in Ha.
        change (fun tc' => _) with (fun tc' => (fun a => Q u <= a) (tc_rootaclk tc')) in Eaclk_lt.
        rewrite <- Forall_map, -> List.Forall_forall in Ha, Ha'', Eaclk_lt.
        firstorder lia.
    + rewrite -> List.Forall_forall.
      intros new_ch Hin_newch.
      pose proof (Hcorr_inr _ Hin_newch) as (ch & Hin_ch & Hso).
      eapply IH; eauto.
    + assumption.
Qed.

Lemma tc_ge_with_subdmono_simple_overlaytc (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hdmono_sub : forall t, exists aclk, Foralltr (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hge : tc_ge tc_larger tc)
  (* needed for using dmono on (P t) *)
  (Hclk_le : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  tc_ge tc_larger tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  rewrite -> List.Forall_forall in IH.
  pose proof (Forall2_forall_exists_r _ _ _ Hcorr) as Hcorr_inr.
  specialize (Hdmono_sub u).
  destruct Hdmono_sub as (aclk' & Hdmono_sub).
  unfold tc_ge in Hge |- *.
  rewrite -> Foralltr_cons_iff in Hclk_le, Hdmono_sub, Hge |- *.
  destruct Hge as (Ege & Hge), Hclk_le as (Eclk_le & Hclk_le), 
    Hdmono_sub as (Hdmono_sub & _).
  rewrite -> List.Forall_forall in Hge, Hclk_le.
  hnf in Hdmono_sub.
  simpl in Eclk_le, Hdmono_sub, Ege.
  removehead Hdmono_sub.
  2: lia.
  split; auto.
  apply List.Forall_app.
  split.
  2: now apply Foralltr_cons_iff in Hdmono_sub.
  rewrite -> List.Forall_forall.
  intros new_ch Hin_newch.
  pose proof (Hcorr_inr _ Hin_newch) as (ch & Hin_ch & Hso).
  specialize (IH _ Hin_ch (Hge _ Hin_ch) (Hclk_le _ Hin_ch) _ Hso).
  now apply IH.
Qed.

Corollary dmono_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hdmono_sub : forall t, exists aclk, Foralltr (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hdmono : Foralltr (dmono_single tc_larger) tc)
  (* needed for using dmono on (P t) *)
  (Hclk_le : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  Foralltr (dmono_single tc_larger) tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  pose proof Hoverlay as Hoverlay_backup.
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  rewrite -> List.Forall_forall in IH.
  pose proof (Forall2_forall_exists_r _ _ _ Hcorr) as Hcorr_inr.
  constructor.
  - intros Hle.
    eapply tc_ge_with_subdmono_simple_overlaytc with (P:=P) (Q:=Q).
    4: apply Hoverlay_backup.
    all: try assumption.
    apply Foralltr_self in Hdmono.
    intuition.
  - apply List.Forall_app.
    split.
    + rewrite -> Foralltr_cons_iff in Hdmono, Hclk_le.
      destruct Hdmono as (_ & Hdmono_chn), Hclk_le as (_ & Hclk_le).
      rewrite -> List.Forall_forall in Hdmono_chn, Hclk_le |- *.
      firstorder.
    + specialize (Hdmono_sub u).
      destruct Hdmono_sub as (aclk' & Hdmono_sub).
      now apply Foralltr_cons_iff in Hdmono_sub.
Qed.

Lemma imono_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hdmono_sub : forall t, exists aclk, Foralltr (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  (Himono_sub : forall t, exists aclk, Foralltr (imono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Himono : Foralltr (imono_single tc_larger) tc)
  (Hclk_le : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  Foralltr (imono_single tc_larger) tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  rewrite -> List.Forall_forall in IH.
  pose proof (Forall2_forall_exists_r _ _ _ Hcorr) as Hcorr_inr.
  pose proof (Himono_sub u) as (aclk' & Himono_sub').
  rewrite -> Foralltr_cons_iff in Himono, Hclk_le, Himono_sub' |- *.
  destruct Himono as (Himono & Himono_chn), Hclk_le as (Eclk_le & Hclk_le), 
    Himono_sub' as (Himono_sub' & Himono_subchn).
  simpl in Eclk_le.
  split.
  - apply List.Forall_app.
    split.
    2: assumption.
    hnf in Himono |- *.
    rewrite -> List.Forall_forall in Himono, Hclk_le |- *.
    intros [(v, clk_v, aclk_v) chn_v] Hin_newch.
    intros Hle.
    pose proof (Hcorr_inr _ Hin_newch) as (ch & Hin_ch & Hso).
    eapply tc_ge_with_subdmono_simple_overlaytc with (P:=P) (Q:=Q).
    4: apply Hso.
    all: try assumption.
    + (* TODO this inversion may be as a tactic ... *)
      destruct ch as [(v', clk_v', aclk_v') ?].
      apply simple_overlaytc_inv in Hso.
      simpl in Hso.
      destruct Hso as (_ & _ & Htmp & _ & _ & _ & _).
      injection Htmp as ->.
      subst clk_v' aclk_v'.
      specialize (Himono _ Hin_ch).
      intuition.
    + intuition.
  - apply List.Forall_app.
    split.
    + rewrite -> List.Forall_forall in Himono_chn, Hclk_le |- *.
      firstorder.
    + assumption.
Qed.

Corollary tc_respect_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hrespect_sub : forall t, exists aclk, tc_respect (Node (mkInfo t (Q t) aclk) (P t)) tc_larger)
  tc (Hrespect : tc_respect tc tc_larger)
  (Hclk_le : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  tc_respect tc' tc_larger.
Proof.
  constructor.
  - apply dmono in Hrespect.
    eapply dmono_simple_overlaytc_pre; eauto.
    intros t.
    destruct (Hrespect_sub t) as (aclk & H).
    exists aclk.
    now apply dmono.
  - apply imono in Hrespect.
    eapply imono_simple_overlaytc_pre; eauto.
    all: intros t.
    all: destruct (Hrespect_sub t) as (aclk & H).
    all: exists aclk.
    + now apply dmono.
    + now apply imono.
Qed.

Lemma tc_attach_detached_nodes_tid_nodup tc tc'
  (Hnodup : NoDup (map tr_rootid (tr_flatten tc))) (Hnodup' : NoDup (map tr_rootid (tr_flatten tc'))) :
  NoDup (map tr_rootid (tr_flatten (tc_attach_nodes (snd (tc_detach_nodes (tr_flatten tc') tc)) tc'))).
Proof.
  (* TODO still needs some preparation when using tc_attach_nodes_dom_info *)
  pose proof (tc_attach_nodes_dom_info _ _ Hnodup Hnodup') as Hperm.
  rewrite <- map_app in Hperm.
  apply Permutation_rootinfo2rootid in Hperm.
  eapply Permutation_NoDup. 
  1: symmetry; apply Hperm. 
  rewrite -> map_app.
  rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
  repeat setoid_rewrite -> base.elem_of_list_In.
  split; [ assumption | split ].
  2: apply tid_nodup_root_chn_split, tc_detach_nodes_tid_nodup; assumption.
  (* use domain exclusion *)
  (* FIXME: extract this out? *)
  intros t H (ch & (sub & Hpick & Hin_ch)%in_flat_map & Hin_sub)%map_flat_map_In.
  pose proof (tc_detach_nodes_snd2fst (tr_flatten tc') tc) as Htmp.
  rewrite -> List.Forall_forall in Htmp.
  specialize (Htmp _ Hpick).
  destruct Htmp as (sub' & Hin_sub' & ->).
  eapply tc_detach_nodes_dom_excl'; [ apply trs_find_in_iff, H | ].
  eapply map_flat_map_In_conv; eauto.
Qed.

(* now, put everything together *)
(* TODO revise the following two proofs *)

Lemma tc_attach_nodes_tc_shape_inv tc tc' 
  (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc') 
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc')
  (Hrespect : tc_respect tc' tc) :
  tc_shape_inv (tc_attach_nodes 
    (snd (tc_detach_nodes (tr_flatten (tc_get_updated_nodes_join tc tc')) tc)) 
    (tc_get_updated_nodes_join tc tc')).
Proof.
  pose proof (tc_attach_nodes_result 
    (snd (tc_detach_nodes (tr_flatten (tc_get_updated_nodes_join tc tc')) tc))
    (tc_get_updated_nodes_join tc tc')) as Hso.
  remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
  destruct (tc_detach_nodes (tr_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
  simpl in Hso |- *.
  pose proof Hso as Hnodup.
  pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
  rewrite <- Eprefix in Hprefix.
  pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix Hshape') as Hshape_pf.
  assert (forest = snd (tc_detach_nodes (tr_flatten prefix_tc') tc)) as Eforest by now rewrite -> Edetach.

  pose proof Hso as Hother.
  eapply tc_shape_inv_simple_overlaytc_pre with (Q:=fun t => tc_getclk t tc) in Hother.
  2:{
    intros t.
    destruct (find (has_same_id t) forest) as [ [(t', clk, aclk) chn] | ] eqn:E.
    2:{
      exists 0.
      constructor.
      all: simpl.
      2-3: rewrite -> Foralltr_cons_iff.
      2-3: split; [ | constructor ].
      2-3: simpl.
      2-3: constructor.
      now repeat constructor.
    }
    simpl.
    apply find_some in E.
    rewrite -> has_same_tid_true in E.
    simpl in E.
    destruct E as (Hin & <-).
    (* unify getclk t tc and clk ... slightly troublesome *)
    pose proof (tc_detach_nodes_snd_is_subprefix (tr_flatten prefix_tc') tc) as Hsnd2pf.
    pose proof (tc_shape_inv_tc_detach_nodes_snd (tr_flatten prefix_tc') tc Hshape) as Hshape_forest.
    rewrite <- Eforest, -> List.Forall_forall in Hsnd2pf, Hshape_forest.
    specialize (Hsnd2pf _ Hin).
    specialize (Hshape_forest _ Hin).
    destruct Hsnd2pf as (sub & Hin_sub & E).
    pose proof (prefixtr_rootinfo_same E) as Einfo.
    pose proof (id_nodup_find_self_sub tr_rootinfo _ (tid_nodup _ Hshape) _ Hin_sub) as Hres.
    apply option.fmap_Some in Hres.
    destruct Hres as (res & Hres & Einfo').
    unfold tr_rootid in Hres.
    rewrite <- Einfo in Hres.
    simpl in Hres.
    assert (tc_getclk t tc = clk) as <-.
    {
      unfold tc_getclk, tc_rootclk.
      now rewrite -> Hres, <- Einfo', <- Einfo.
    }
    eauto.
  }
  2:{
    pose proof (tc_shape_inv_prefix_preserve _ _ (tc_get_updated_nodes_join_is_prefix tc tc') Hshape').
    congruence.
  }
  2:{
    pose proof (tc_get_updated_nodes_join_shape _ Hshape' _ Hrespect Hroot_clk_le).
    subst prefix_tc'.
    eapply Foralltr_impl.
    2: apply (proj1 H).
    simpl.
    lia.
  }
  2:{
    pose proof (tc_get_updated_nodes_join_shape _ Hshape' _ Hrespect Hroot_clk_le).
    subst prefix_tc'.
    eapply Foralltr_impl.
    2: apply (proj2 H).
    intros [? ?].
    apply List.Forall_impl.
    lia.
  }

  apply tc_shape_inv_conj_iff.
  split; [ | assumption ].
  subst forest.
  apply tc_attach_detached_nodes_tid_nodup. 
  all: now apply tid_nodup.
Qed.

Lemma tc_attach_nodes_respect tc tc' 
  (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc') 
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc')
  (Hrespect : tc_respect tc' tc) tc_larger 
    (Hrespect1 : tc_respect tc tc_larger)
    (Hrespect2 : tc_respect tc' tc_larger) :
  tc_respect (tc_attach_nodes 
    (snd (tc_detach_nodes (tr_flatten (tc_get_updated_nodes_join tc tc')) tc)) 
    (tc_get_updated_nodes_join tc tc')) tc_larger.
Proof.
  pose proof (tc_attach_nodes_result 
    (snd (tc_detach_nodes (tr_flatten (tc_get_updated_nodes_join tc tc')) tc))
    (tc_get_updated_nodes_join tc tc')) as Hso.
  remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
  destruct (tc_detach_nodes (tr_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
  simpl in Hso |- *.
  pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
  assert (forest = snd (tc_detach_nodes (tr_flatten prefix_tc') tc)) as Eforest by now rewrite -> Edetach.
  rewrite <- Eprefix in Hprefix.
  revert Hso.
  apply tc_respect_simple_overlaytc_pre with (Q:=fun t => tc_getclk t tc).
  - intros t.
    destruct (find (has_same_id t) forest) as [ [(t', clk, aclk) chn] | ] eqn:E.
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
    (* FIXME: revise? *)
    pose proof (tc_detach_nodes_snd_is_subprefix (tr_flatten prefix_tc') tc) as Hsnd2pf.
    pose proof (tc_shape_inv_tc_detach_nodes_snd (tr_flatten prefix_tc') tc Hshape) as Hshape_forest.
    rewrite <- Eforest, -> List.Forall_forall in Hsnd2pf, Hshape_forest.
    specialize (Hsnd2pf _ Hin).
    specialize (Hshape_forest _ Hin).
    destruct Hsnd2pf as (sub & Hin_sub & E).
    pose proof (prefixtr_rootinfo_same E) as Einfo.
    pose proof (id_nodup_find_self_sub tr_rootinfo _ (tid_nodup _ Hshape) _ Hin_sub) as Hres.
    apply option.fmap_Some in Hres.
    destruct Hres as (res & Hres & Einfo').
    unfold tr_rootid in Hres.
    rewrite <- Einfo in Hres.
    simpl in Hres.
    assert (tc_getclk t tc = clk) as <-.
    {
      unfold tc_getclk, tc_rootclk.
      now rewrite -> Hres, <- Einfo', <- Einfo.
    }
    exists aclk.
    pose proof (tc_respect_sub _ _ Hrespect1) as Hrespect_sub.
    rewrite -> Foralltr_Forall_subtree, -> List.Forall_forall in Hrespect_sub.
    specialize (Hrespect_sub _ Hin_sub).
    eapply tc_respect_prefix_preserve; eauto.
  - eapply tc_respect_prefix_preserve; eauto.
  - pose proof (tc_get_updated_nodes_join_shape _ Hshape' _ Hrespect Hroot_clk_le).
    subst prefix_tc'.
    eapply Foralltr_impl.
    2: apply (proj1 H).
    simpl.
    lia.
Qed.

(* should also be "tcs_congr", but keep the word "forest" anyway *)
Lemma tc_attach_nodes_forest_congr forest1 forest2 tc
  (H : Foralltr (fun tc' => List.find (has_same_id (tr_rootid tc')) forest1 = 
    List.find (has_same_id (tr_rootid tc')) forest2) tc) :
  tc_attach_nodes forest1 tc = tc_attach_nodes forest2 tc.
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  rewrite Foralltr_cons_iff in H.
  simpl in H |- *.
  destruct H as (Hroot & H).
  eapply Forall_impl_impl in H.
  2: apply IH.
  erewrite -> map_ext_Forall.
  2: apply H.
  now rewrite Hroot.
Qed.

Corollary tc_attach_nodes_forest_cleanhd forest1 sub tc
  (Hnotin : ~ In (tr_rootid sub) (map tr_rootid (tr_flatten tc))) :
  tc_attach_nodes forest1 tc = tc_attach_nodes (sub :: forest1) tc.
Proof.
  apply tc_attach_nodes_forest_congr, Foralltr_Forall_subtree, Forall_forall.
  intros sub' Hin.
  simpl.
  destruct (has_same_id (tr_rootid sub') sub) eqn:E; try reflexivity.
  rewrite -> has_same_tid_true in E.
  apply in_map with (f:=tr_rootid) in Hin.
  congruence.
Qed.

(* FIXME: why so long? *)

Lemma tc_detach_attach_distr1_fst tc forest nd 
  (Hnotin : ~ In (tr_rootid nd) (map tr_rootid (tr_flatten tc))) :
  fst (tc_detach_nodes (nd :: nil) (tc_attach_nodes forest tc)) =
  tc_attach_nodes (map fst (map (tc_detach_nodes (nd :: nil)) forest)) tc.
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  simpl.
  remember (match find (has_same_id (info_tid ni)) forest with Some u => tr_rootchn u | None => nil end) as old_chn eqn:Eold_chn.
  remember (map (tc_attach_nodes forest) chn) as app_chn eqn:Eapp_chn.
  rewrite map_app, split_app.
  destruct (List.split (map (tc_detach_nodes (nd :: nil)) app_chn)) as (new_chn1, res1) eqn:Esplit1, 
    (List.split (map (tc_detach_nodes (nd :: nil)) old_chn)) as (new_chn2, res2) eqn:Esplit2, 
    (partition (fun tc' : treeclock => isSome (if has_same_id (tr_rootid tc') nd then Some nd else None)) (new_chn1 ++ new_chn2))
    as (res', new_chn') eqn:Epar.
  (* bad isSome *)
  rewrite -> partition_ext_Forall with (g:=fun tc' => has_same_id (tr_rootid tc') nd) in Epar.
  2: apply Forall_forall; intros x ?; now destruct (has_same_id (tr_rootid x) nd).
  simpl.
  f_equal.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit1, Esplit2.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit1, Esplit2, Epar.
  destruct Epar as (Eres' & Enew_chn'), Esplit1 as (Enew_chn1 & Eres1), 
    Esplit2 as (Enew_chn2 & Eres2).
  simpl in Hnotin.
  apply Forall_impl_impl with (P:=fun tc => ~ In (tr_rootid nd) (map tr_rootid (tr_flatten tc))) in IH.
  2:{
    apply Forall_forall.
    intros ch Hin_ch Hin.
    (* TODO streamline? *)
    apply Hnotin.
    right.
    eapply map_flat_map_In_conv; eauto.
  }
  rewrite <- (map_ext_Forall _ _ IH).
  subst.
  rewrite -> ! map_map, -> filter_app.
  f_equal.
  - apply filter_all_true.
    intros ? (ch & <- & Hin)%in_map_iff.
    apply negb_true_iff, not_true_is_false.
    intros HH.
    rewrite -> has_same_tid_true in HH.
    apply Hnotin.
    right.
    eapply map_flat_map_In_conv; eauto.
    rewrite <- HH.
    unfold tr_rootid at 1.
    rewrite (prefixtr_rootinfo_same (tc_detach_nodes_fst_is_prefix _ _)).
    destruct ch; simpl; auto.
  - (* ? *)
    clear -forest.
    induction forest as [ | tc' forest IH ]; simpl; auto.
    erewrite -> tc_rootinfo_has_same_tid_congr with (x:=(fst (tc_detach_nodes (nd :: nil) tc'))).
    2: apply tc_detach_nodes_fst_rootinfo_same.
    destruct (has_same_id (info_tid ni) tc') eqn:E.
    + destruct tc' as [ ni' chn' ].
      simpl.
      (* TODO ... *)
      destruct (List.split (map (tc_detach_nodes (nd :: nil)) chn'))
        as (new_chn, forest') eqn:Esplit, 
        (partition (fun tc' : treeclock => isSome (if has_same_id (tr_rootid tc') nd then Some nd else None)) new_chn)
        as (res', new_chn') eqn:Epar.
      simpl.
      (* bad isSome *)
      rewrite -> partition_ext_Forall with (g:=fun tc' => has_same_id (tr_rootid tc') nd) in Epar.
      2: apply Forall_forall; intros x ?; now destruct (has_same_id (tr_rootid x) nd).
      rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
      rewrite -> partition_filter in Epar.
      apply pair_equal_split in Esplit, Epar.
      destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
      now subst.
    + apply IH.
Qed.

Lemma tc_detach_attach_distr1_snd tc forest nd 
  (Hnotin : ~ In (tr_rootid nd) (map tr_rootid (tr_flatten tc))) :
  Permutation
  (snd (tc_detach_nodes (nd :: nil) (tc_attach_nodes forest tc)))
  (flat_map snd (map (fun tc' => tc_detach_nodes (nd :: nil) 
    (match find (has_same_id (tr_rootid tc')) forest with 
      | Some u => u | None => Node (mkInfo (tr_rootid tc') 0%nat 0%nat) nil end)) (tr_flatten tc))).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  simpl.
  remember (match find (has_same_id (info_tid ni)) forest with Some u => tr_rootchn u | None => nil end) as old_chn eqn:Eold_chn.
  remember (map (tc_attach_nodes forest) chn) as app_chn eqn:Eapp_chn.
  rewrite map_app, split_app.
  destruct (List.split (map (tc_detach_nodes (nd :: nil)) app_chn)) as (new_chn1, res1) eqn:Esplit1, 
    (List.split (map (tc_detach_nodes (nd :: nil)) old_chn)) as (new_chn2, res2) eqn:Esplit2, 
    (partition (fun tc' : treeclock => isSome (if has_same_id (tr_rootid tc') nd then Some nd else None)) (new_chn1 ++ new_chn2))
    as (res', new_chn') eqn:Epar.
  (* bad isSome *)
  rewrite -> partition_ext_Forall with (g:=fun tc' => has_same_id (tr_rootid tc') nd) in Epar.
  2: apply Forall_forall; intros x ?; now destruct (has_same_id (tr_rootid x) nd).
  simpl.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit1, Esplit2.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit1, Esplit2, Epar.
  destruct Epar as (Eres' & Enew_chn'), Esplit1 as (Enew_chn1 & Eres1), 
    Esplit2 as (Enew_chn2 & Eres2).
  simpl in Hnotin.
  apply Forall_impl_impl with (P:=fun tc => ~ In (tr_rootid nd) (map tr_rootid (tr_flatten tc))) in IH.
  2:{
    apply Forall_forall.
    intros ch Hin_ch Hin.
    apply Hnotin.
    right.
    eapply map_flat_map_In_conv; eauto.
  }
  rewrite -> ! flat_map_concat_map, -> concat_map, -> map_map, <- ! flat_map_concat_map.

  subst.
  rewrite -> concat_app, -> ! map_map, <- flat_map_concat_map.
  etransitivity.
  1: apply Permutation_app; [ apply Permutation_app; 
    [ eapply Permutation_Forall_flat_map; apply IH | reflexivity ] | reflexivity ].
  erewrite -> map_ext_Forall with (l:=chn).
  2:{
    apply Forall_forall.
    intros ch Hin_ch.
    apply tc_detach_attach_distr1_fst.
    intros Hin.
    apply Hnotin.
    right.
    eapply map_flat_map_In_conv; eauto.
  }
  rewrite -> map_map with (g:=fst), -> filter_app.
  match goal with |- Permutation (_ ++ ?al ++ _) _ => 
    replace al with (@nil treeclock) end.
  2:{
    rewrite -> filter_all_false; auto.
    intros ? (ch & <- & Hin)%in_map_iff.
    apply not_true_is_false.
    intros HH.
    rewrite -> has_same_tid_true in HH.
    apply Hnotin.
    right.
    eapply map_flat_map_In_conv; eauto.
    rewrite <- HH.
    destruct ch; simpl; auto.
  }
  simpl.

  (* ? *)
  assert (forall [A B C D : Type] (l : list A) (f : B -> C) (g : C -> list D) (h : A -> list B), 
    flat_map g (flat_map (fun x => map f (h x)) l) = 
    flat_map (fun x => flat_map g (map f (h x))) l) as Htmp.
  {
    intros. 
    induction l as [ | a l IHH ]; simpl; auto.
    now rewrite flat_map_app, IHH.
  }
  rewrite Htmp; clear Htmp.
  rewrite <- app_assoc.
  etransitivity; [ | apply Permutation_app_comm ].
  apply Permutation_app_head.

  destruct (find (has_same_id (info_tid ni)) forest) as [ [ ni' chn' ] | ] eqn:E.
  2: now simpl.
  clear -chn'.
  cbn delta [tr_rootchn] beta iota.
  (* TODO this is a simple equation for the result of tc_detach_nodes only? *)
  simpl.
  destruct (List.split (map (tc_detach_nodes (nd :: nil)) chn')) as (new_chn, res) eqn:Esplit,  
    (partition (fun tc' : treeclock => isSome (if has_same_id (tr_rootid tc') nd then Some nd else None)) new_chn)
    as (res', new_chn') eqn:Epar.
  (* bad isSome *)
  rewrite -> partition_ext_Forall with (g:=fun tc' => has_same_id (tr_rootid tc') nd) in Epar.
  2: apply Forall_forall; intros x ?; now destruct (has_same_id (tr_rootid x) nd).
  simpl.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Epar as (Eres' & Enew_chn'), Esplit as (Enew_chn & Eres).
  now subst.
Qed.

(* TODO can we prove this from the beginning? this seems to be the only thing we want. *)
(* FIXME: something must be repeating here. what is it? *)
Corollary tc_detach_attach_distr1_snd' tc forest nd 
  (Hnotin : ~ In (tr_rootid nd) (map tr_rootid (tr_flatten tc))) 
  (Hdomincl : Forall (fun tc' => In (tr_rootid tc') (map tr_rootid (tr_flatten tc))) forest)
  (Hnodup_forest : NoDup (map tr_rootid forest))
  (Hnodup : NoDup (map tr_rootid (tr_flatten tc))) :
  Permutation
    (snd (tc_detach_nodes (nd :: nil) (tc_attach_nodes forest tc)))
    (flat_map snd (map (tc_detach_nodes (nd :: nil)) forest)).
Proof.
  rewrite tc_detach_attach_distr1_snd; try assumption.
  match goal with |- _ (flat_map snd (map ?ff _)) _ =>
    rewrite -> map_ext_Forall with (l:=forest) (f:=(tc_detach_nodes (nd :: nil))) (g:=ff) end.
  2:{
    pose proof (id_nodup_find_self _ Hnodup_forest) as Htmp.
    rewrite -> Forall_forall in Htmp |- *.
    intros x Hin.
    specialize (Htmp _ Hin).
    now rewrite Htmp.
  }
  etransitivity.
  1: apply Permutation_flat_map, Permutation_map, 
    Permutation_split_combine with (f:=fun tc' => find (has_same_id (tr_rootid tc')) forest).
  rewrite -> map_app, -> flat_map_app.
  match goal with |- _ (?aa ++ ?bb) _ => replace bb with (@nil treeclock) end.
  2:{
    rewrite -> flat_map_concat_map.
    apply eq_sym, concat_nil_Forall, Forall_map, Forall_map, Forall_forall.
    intros x (Hin & HH%negb_true_iff)%filter_In.
    destruct (find _ _) eqn:E in |- *.
    1: rewrite E in HH; discriminate.
    rewrite -> tc_detach_nodes_intact; try reflexivity.
    auto.
  }
  rewrite app_nil_r.
  (* ... *)
  pose proof (map_map tr_rootid (fun t => tc_detach_nodes (nd :: nil)
    match find (has_same_id t) forest with Some u => u | None => Node (mkInfo t 0%nat 0%nat) nil end)) as Htmp.
  simpl in Htmp.
  rewrite <- ! Htmp.
  clear Htmp.
  apply Permutation_flat_map, Permutation_map.
  (* ... have to use map_filter_comm *)
  pose proof (map_filter_comm tr_rootid (fun t => (find (has_same_id t) forest)) (tr_flatten tc)) as Htmp.
  simpl in Htmp.
  rewrite <- ! Htmp.
  clear Htmp.
  (* ... *)
  apply NoDup_Permutation; try assumption.
  1: now apply NoDup_filter.
  intros t.
  rewrite filter_In.
  rewrite -> Forall_forall in Hdomincl.
  split.
  - match goal with |- context[find ?a ?b] => destruct (find a b) as [ res | ] eqn:Eres end.
    2: intros (? & ?); discriminate.
    intros (Hin & _).
    apply trs_find_in_iff.
    now rewrite Eres.
  - intros Hin.
    split.
    + rewrite -> in_map_iff in Hin.
      destruct Hin as (sub & <- & Hin).
      now apply Hdomincl.
    + now rewrite -> trs_find_in_iff in Hin.
Qed.

End TC_Attach_Nodes.

(* purely computational *)

Fact tc_join_trivial tc tc' (H : tc_rootclk tc' <= tc_getclk (tr_rootid tc') tc) :
  tc_join tc tc' = tc.
Proof.
  unfold tc_join.
  destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
  simpl in H |- *.
  apply Nat.leb_le in H.
  now rewrite H.
Qed.

Fact tc_join_roottid_same_trivial tc tc' (H : tr_rootid tc = tr_rootid tc') 
  (Hroot_clk_le : tc_getclk (tr_rootid tc) tc' <= tc_rootclk tc) :
  tc_join tc tc' = tc.
Proof.
  apply tc_join_trivial.
  destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
  simpl in H, Hroot_clk_le |- *; subst z.
  unfold tc_getclk, tr_getnode in Hroot_clk_le |- *. 
  simpl in Hroot_clk_le |- *.
  now destruct (eqdec z' z').
Qed.

Fact tc_join_go tc tc' 
  (H : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') :
  tc_join tc tc' = tc_join_partial tc (tc_get_updated_nodes_join tc tc').
Proof.
  unfold tc_join, tc_join_partial.
  destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
  simpl in H.
  apply Nat.leb_gt in H.
  cbn delta [tr_rootinfo] zeta iota beta.
  now rewrite H.
Qed.

Fact tc_join_partial_rootinfo_same tc subtree_tc' :
  tr_rootinfo (tc_join_partial tc subtree_tc') = tr_rootinfo tc.
Proof.
  unfold tc_join_partial.
  destruct (tc_detach_nodes _ _) as (pivot, forest) eqn:Edetach.
  destruct subtree_tc' as [(?, ?, ?) ?] eqn:E, pivot as [(?, ?, ?) ?] eqn:Epivot.
  simpl in *. 
  rewrite <- tc_detach_nodes_fst_rootinfo_same with (tcs:=tr_flatten (subtree_tc')).
  subst.
  simpl.
  now rewrite -> Edetach.
Qed.

Section TC_Join_Partial.

  Variables (tc tc' : treeclock).

  (* a direct result *)
  Lemma tc_join_partial_dom_info :
    Permutation (map tr_rootinfo (tr_flatten (tc_join_partial tc tc')))
      (map tr_rootinfo (tr_flatten (fst (tc_detach_nodes (tr_flatten tc') tc))) ++
        map tr_rootinfo (tr_flatten 
          (let: Node (mkInfo t clk _) chn := tc_attach_nodes 
            (snd (tc_detach_nodes (tr_flatten tc') tc)) tc' 
          in Node (mkInfo t clk (tc_rootclk tc)) chn))).
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    unfold tc_join_partial.
    rewrite <- ! Etc'.
    destruct (tc_detach_nodes (tr_flatten tc') tc) as (pivot, forest) eqn:Edetach.
    destruct (tc_attach_nodes forest tc') as [ni chn_w] eqn:Eattach.
    pose proof (tc_attach_nodes_rootinfo_same forest tc') as Eni.
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Eni_z.
    rewrite -> Eattach, -> Etc' in Eni.
    rewrite -> Edetach in Eni_z.
    destruct pivot as [ni_z chn_z] eqn:Epivot.
    simpl in Eni, Eni_z.
    subst ni ni_z.
    simpl.
    constructor.
    rewrite -> Eattach.
    simpl.
    rewrite -> map_app.
    etransitivity. (* FIXME: perm solver *)
    2: apply Permutation_middle.
    constructor.
    now apply Permutation_app_comm.
  Qed.

  Corollary tc_join_partial_dom_tid :
    Permutation (map tr_rootid (tr_flatten (tc_join_partial tc tc')))
      (map tr_rootid (tr_flatten (fst (tc_detach_nodes (tr_flatten tc') tc))) ++
        map tr_rootid (tr_flatten (tc_attach_nodes 
          (snd (tc_detach_nodes (tr_flatten tc') tc)) tc'))).
  Proof.
    pose proof tc_join_partial_dom_info as Hperm.
    rewrite <- map_app in Hperm.
    apply Permutation_rootinfo2rootid in Hperm.
    etransitivity; [ apply Hperm | ].
    rewrite -> map_app.
    apply Permutation_app_head.
    destruct (tc_attach_nodes _ _) as [(?, ?, ?) ?].
    now simpl.
  Qed.

  Hypotheses (Hnodup : List.NoDup (map tr_rootid (tr_flatten tc))) (Hnodup' : List.NoDup (map tr_rootid (tr_flatten tc'))).
  Collection collection_nodup := Hnodup Hnodup'.

  (* TODO there may be some repetition below ... *)

  (* a refined result *)
  Lemma tc_join_partial_dom_partial_info :
    Permutation (map tc_rootinfo_partial (tr_flatten (tc_join_partial tc tc')))
      (map tc_rootinfo_partial (tr_flatten (fst (tc_detach_nodes (tr_flatten tc') tc))) ++
        map tc_rootinfo_partial (tr_flatten tc') ++
        map tc_rootinfo_partial (flat_map tr_flatten (flat_map tr_rootchn
                (snd (tc_detach_nodes (tr_flatten tc') tc))))).
  Proof.
    pose proof tc_join_partial_dom_info as Hperm.
    pose proof (tc_attach_nodes_dom_info _ _ Hnodup Hnodup') as Hperm'.
    rewrite <- map_app in Hperm, Hperm'.
    apply Permutation_rootinfo2partialinfo in Hperm, Hperm'.
    etransitivity; [ apply Hperm | ].
    rewrite -> map_app.
    apply Permutation_app_head.
    rewrite -> map_app in Hperm'.
    destruct (tc_attach_nodes (snd (tc_detach_nodes (tr_flatten tc') tc)) tc') as [(?, ?, ?) ?].
    etransitivity; [ apply Hperm' | ].
    reflexivity.
  Qed.

  Corollary tc_join_partial_dom_tid' :
    Permutation (map tr_rootid (tr_flatten (tc_join_partial tc tc')))
      (map tr_rootid (tr_flatten (fst (tc_detach_nodes (tr_flatten tc') tc))) ++
        map tr_rootid (tr_flatten tc') ++
        map tr_rootid (flat_map tr_flatten (flat_map tr_rootchn
                (snd (tc_detach_nodes (tr_flatten tc') tc))))).
  Proof.
    pose proof (tc_attach_nodes_dom_info _ _ Hnodup Hnodup') as Hperm.
    rewrite <- map_app in Hperm.
    apply Permutation_rootinfo2rootid in Hperm.
    rewrite -> map_app in Hperm.
    etransitivity; [ apply tc_join_partial_dom_tid; auto | ].
    now apply Permutation_app_head.
  Qed.

  (* Hypothesis (Hnotin : find (has_same_id (tr_rootid tc)) (tr_flatten tc') = None). *)
  Hypothesis (Hnotin : ~ In (tr_rootid tc) (map tr_rootid (tr_flatten tc'))).

  Corollary tc_join_partial_dom_partial_info' :
    Permutation (map tc_rootinfo_partial (tr_flatten (tc_join_partial tc tc')))
      (map tc_rootinfo_partial (filter (fun sub => 
              negb (find (has_same_id (tr_rootid sub)) (tr_flatten tc'))) (tr_flatten tc)) ++
        map tc_rootinfo_partial (tr_flatten tc')).
  Proof.
    etransitivity; [ apply tc_join_partial_dom_partial_info | ].
    etransitivity; [ apply Permutation_app_swap_app | ].
    etransitivity; [ | apply Permutation_app_comm ].
    apply Permutation_app_head.
    rewrite <- map_app.
    apply Permutation_rootinfo2partialinfo.
    rewrite -> map_app.
    apply tc_detach_nodes_dom_partition''; try assumption.
    rewrite -> trs_find_in_iff in Hnotin.
    now destruct (find _ _); unfold is_true in Hnotin.
  Qed.

  Corollary tc_join_partial_tid_nodup :
    List.NoDup (map tr_rootid (tr_flatten (tc_join_partial tc tc'))).
  Proof.
    pose proof tc_join_partial_dom_partial_info' as Hperm.
    rewrite <- map_app in Hperm.
    eapply Permutation_NoDup; [ symmetry; apply Permutation_partialinfo2roottid, Hperm | ].
    rewrite -> map_app.
    rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
    repeat setoid_rewrite -> base.elem_of_list_In.
    (* ... have to use map_filter_comm *)
    pose proof (map_filter_comm tr_rootid (fun t => negb (find (has_same_id t) (tr_flatten tc'))) (tr_flatten tc)) as Htmp.
    simpl in Htmp.
    rewrite <- ! Htmp.
    clear Htmp.
    split; [ now apply NoDup_filter | split; try assumption ].
    intros t (Hin & E)%filter_In Hin'%trs_find_in_iff.
    now rewrite -> Hin' in E.
  Qed.

  Lemma tc_join_partial_getclk t :
    tc_getclk t (tc_join_partial tc tc') = match tr_getnode t tc' with Some res => tc_rootclk res | None => tc_getclk t tc end.
  Proof.
    pose proof tc_join_partial_dom_partial_info' as Hperm.
    rewrite -> Permutation_app_comm, <- map_app in Hperm.
    pose proof (tc_getclk_perm_congr_pre _ _ tc_join_partial_tid_nodup Hperm t) as Htmp.
    rewrite -> find_app in Htmp.
    fold (tr_getnode t (tc_join_partial tc tc')) in Htmp.
    rewrite -> tc_getclk_as_fmap, -> Htmp.
    fold (tr_getnode t tc').
    destruct (tr_getnode t tc') as [ res | ] eqn:Eres; simpl.
    1: reflexivity.
    unfold tc_getclk.
    destruct (find _ _) as [ res' | ] eqn:Eres' in |- *; simpl.
    - apply find_some in Eres'.
      rewrite -> has_same_tid_true, -> filter_In, -> negb_true_iff in Eres'.
      destruct Eres' as ((Hres' & _) & ->).
      unfold tr_getnode.
      pose proof (id_nodup_find_self _ Hnodup) as Htmp2%Foralltr_Forall_subtree.
      eapply Foralltr_subtr in Htmp2.
      2: apply Hres'.
      now rewrite -> Htmp2.
    - destruct (tr_getnode t tc) as [ res'' | ] eqn:Eres''.
      2: reflexivity.
      apply find_some in Eres''.
      rewrite -> has_same_tid_true in Eres''.
      destruct Eres'' as (Eres'' & ->).
      apply find_none with (x:=res'') in Eres'.
      2:{
        rewrite -> filter_In, -> negb_true_iff.
        split; try assumption.
        unfold tr_getnode in Eres.
        now rewrite Eres.
      }
      now rewrite has_same_tid_false in Eres'.
  Qed.

End TC_Join_Partial.

Section TC_Join.

  Variables (tc tc' : treeclock).
  Hypotheses (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc')
    (Hrespect : tc_respect tc' tc).

  (* this is fundamental! the root of tc will not be updated *)
  Hypothesis (Hroot_clk_le : tc_getclk (tr_rootid tc) tc' <= tc_rootclk tc).

  Lemma tc_join_tc_shape_inv :
    tc_shape_inv (tc_join tc tc').
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    unfold tc_join.
    cbn delta [tr_rootinfo] beta iota.
    destruct (clk_u' <=? tc_getclk u' tc) eqn:Eclk_lt.
    1: assumption.
    apply Nat.leb_gt in Eclk_lt.
    pose proof (tc_join_go tc tc') as Ejoin. (* get partial *)
    rewrite -> Etc' in Ejoin at 1 2.
    simpl in Ejoin.
    specialize (Ejoin Eclk_lt).
    rewrite <- ! Etc'.
    remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
    destruct (tc_detach_nodes (tr_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
    destruct (tc_attach_nodes forest prefix_tc') as [ni chn_w] eqn:Eattach.
    pose proof (tc_attach_nodes_rootinfo_same forest prefix_tc') as Eni.
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Eni_z.
    rewrite -> Eattach, -> Eprefix, -> (prefixtr_rootinfo_same (tc_get_updated_nodes_join_is_prefix _ _)), 
      -> Etc' in Eni.
    rewrite -> Edetach in Eni_z.
    destruct pivot as [ni_z chn_z] eqn:Epivot.
    simpl in Eni, Eni_z.
    subst ni ni_z.

    (* use prepend child *)
    apply tc_shape_inv_prepend_child.
    - pose proof (tc_shape_inv_tc_detach_nodes_fst (tr_flatten prefix_tc') tc Hshape) as H.
      now rewrite -> Edetach in H.
    - apply tc_shape_inv_root_aclk_useless with (aclk:=aclk_u').
      pose proof (tc_attach_nodes_tc_shape_inv _ _ Hshape Hshape' Eclk_lt Hrespect) as H.
      subst.
      rewrite -> Edetach in H.
      cbn delta [snd] beta iota in H.
      now rewrite -> Eattach in H.
    - (* manipulate *)
      pose proof (tc_join_partial_tid_nodup tc (tc_get_updated_nodes_join tc tc') (tid_nodup _ Hshape)) as Htmp.
      pose proof (tid_nodup_prefix_preserve _ _ (tc_get_updated_nodes_join_is_prefix tc tc')) as Htmp2.
      rewrite -> Etc' in Htmp2 at 1.
      specialize (Htmp2 (tid_nodup _ Hshape')).
      pose proof (tc_get_updated_nodes_join_adequacy _ Hshape' _ Hrespect) as Htmp3.
      simpl tc_rootclk in Htmp3.
      simpl tr_rootid in Htmp3.
      specialize (Htmp3 Eclk_lt (tr_rootid tc)).
      apply Nat.nlt_ge in Hroot_clk_le.
      unfold tc_getclk in Htmp3 at 1.
      rewrite -> tc_getnode_self in Htmp3.
      rewrite -> Htmp3, <- tr_getnode_in_iff, <- Etc' in Hroot_clk_le.
      specialize (Htmp Htmp2 Hroot_clk_le).
      unfold tc_join_partial in Htmp.
      now rewrite <- Eprefix, -> Edetach, -> Eattach in Htmp.
    - now simpl.
    - simpl.
      pose proof (tc_shape_inv_tc_detach_nodes_fst (tr_flatten prefix_tc') tc Hshape) as H.
      apply aclk_upperbound, Foralltr_self in H.
      rewrite -> Edetach in H.
      destruct tc as [(?, clk_z, ?) ?].
      simpl in H |- *.
      hnf in H.
      rewrite -> List.Forall_forall in H.
      destruct chn_z as [ | ch ? ]; simpl.
      1: lia.
      now specialize (H _ (or_introl eq_refl)).
  Qed.

  Lemma tc_join_pointwise_max_pre
    (Hroot_clk_lt : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') t :
    tc_getclk t (tc_join tc tc') = Nat.max (tc_getclk t tc) (tc_getclk t tc').
  Proof.
    pose proof (tc_join_go tc tc' Hroot_clk_lt) as ->.
    (* manipulate; TODO repeating above? *)
    pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
    pose proof (tc_join_partial_getclk tc (tc_get_updated_nodes_join tc tc') (tid_nodup _ Hshape)) as Htmp.
    pose proof (tid_nodup_prefix_preserve _ _ Hprefix) as Htmp2.
    specialize (Htmp2 (tid_nodup _ Hshape')).
    pose proof (tc_get_updated_nodes_join_adequacy _ Hshape' _ Hrespect Hroot_clk_lt) as Htmp3.
    pose proof Htmp3 as Htmp3'.
    specialize (Htmp3' (tr_rootid tc)).
    apply Nat.nlt_ge in Hroot_clk_le.
    unfold tc_getclk in Htmp3' at 1.
    rewrite -> tc_getnode_self in Htmp3'.
    rewrite -> Htmp3', <- tr_getnode_in_iff in Hroot_clk_le.
    specialize (Htmp Htmp2 Hroot_clk_le).

    rewrite -> Htmp.
    destruct (tr_getnode t (tc_get_updated_nodes_join tc tc')) as [ res | ] eqn:Eres.
    - match type of Eres with ?a = _ => assert (a) as Eres' by now rewrite Eres end.
      rewrite <- Htmp3 in Eres'.
      pose proof Eres as (Eres2 & <-)%trs_find_has_id.
      apply in_map with (f:=tr_rootinfo), (prefixtr_flatten_info_incl Hprefix), in_map_iff in Eres2.
      destruct Eres2 as (res2 & Einfo & Hres2).
      (* TODO extract this unifying process? *)
      pose proof (id_nodup_find_self _ (tid_nodup _ Hshape')) as HH%Foralltr_Forall_subtree.
      eapply Foralltr_subtr in HH.
      2: apply Hres2.
      rewrite -> (tr_rootinfo_id_inj Einfo) in HH.
      replace (tc_rootclk res) with (tc_getclk (tr_rootid res) tc').
      2: unfold tc_getclk, tr_getnode, tc_rootclk; now rewrite -> HH, -> Einfo.
      lia.
    - match type of Eres with ?a = _ => assert (~ a) as Eres' by now rewrite Eres end.
      rewrite <- Htmp3 in Eres'.
      apply Nat.nlt_ge in Eres'.
      lia.
  Qed.

  Corollary tc_join_pointwise_max t :
    tc_getclk t (tc_join tc tc') = Nat.max (tc_getclk t tc) (tc_getclk t tc').
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    destruct (clk_u' <=? tc_getclk u' tc) eqn:Eclk_lt.
    - unfold tc_join.
      simpl.
      rewrite -> Eclk_lt.
      apply Nat.leb_le in Eclk_lt.
      (* by respect *)
      rewrite <- Etc', -> max_l.
      1: reflexivity.
      apply tc_ge_all_getclk_ge.
      apply dmono, Foralltr_self in Hrespect.
      simpl in Hrespect.
      subst tc'.
      intuition.
    - apply Nat.leb_gt in Eclk_lt.
      rewrite <- Etc' in *.
      replace clk_u' with (tc_rootclk tc') in Eclk_lt by now rewrite -> Etc'.
      replace u' with (tr_rootid tc') in Eclk_lt by now rewrite -> Etc'.
      now apply tc_join_pointwise_max_pre.
  Qed.

  Corollary tc_join_respected tc''
    (Hrespect1 : tc_respect tc'' tc) (Hrespect2 : tc_respect tc'' tc') :
    tc_respect tc'' (tc_join tc tc').
  Proof.
    eapply tc_respect_pointwise_max_preserve.
    4: apply Hrespect1.
    4: apply Hrespect2.
    1: apply tc_join_pointwise_max.
    all: now apply tid_nodup.
  Qed.

  Lemma tc_join_respect tc''
    (Hrespect1 : tc_respect tc tc'') (Hrespect2 : tc_respect tc' tc'') 
    (* ensure that there is no dmono at the root *)
    (Hroot_clk_lt' : tc_getclk (tr_rootid tc) tc'' < tc_rootclk tc) :
    tc_respect (tc_join tc tc') tc''.
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    unfold tc_join.
    cbn delta [tr_rootinfo] beta iota.
    destruct (clk_u' <=? tc_getclk u' tc) eqn:Eclk_lt.
    1: assumption.
    apply Nat.leb_gt in Eclk_lt.
    rewrite <- ! Etc'.
    remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
    destruct (tc_detach_nodes (tr_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
    destruct (tc_attach_nodes forest prefix_tc') as [ni chn_w] eqn:Eattach.
    pose proof (tc_attach_nodes_rootinfo_same forest prefix_tc') as Eni.
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Eni_z.
    rewrite -> Eattach, -> Eprefix, -> (prefixtr_rootinfo_same (tc_get_updated_nodes_join_is_prefix _ _)), 
      -> Etc' in Eni.
    rewrite -> Edetach in Eni_z.
    destruct pivot as [ni_z chn_z] eqn:Epivot.
    simpl in Eni, Eni_z.
    subst ni ni_z.
    (* prepare *)
    pose proof (tc_detach_nodes_fst_is_prefix (tr_flatten prefix_tc') tc) as Hprefix_pivot.
    rewrite -> Edetach in Hprefix_pivot.
    simpl in Hprefix_pivot.
    pose proof (tc_respect_prefix_preserve _ _ Hprefix_pivot _ Hrespect1) as Hrespect_pivot.
    pose proof (tc_attach_nodes_respect _ _ Hshape Hshape' Eclk_lt Hrespect _ Hrespect1 Hrespect2) as Hrespect_attach.
    rewrite <- Etc', <- Eprefix, -> Edetach in Hrespect_attach.
    simpl in Hrespect_attach.
    rewrite -> Eattach in Hrespect_attach.
    constructor.
    - constructor.
      + (* impossible by assumption *)
        simpl.
        destruct tc as [(?, ?, ?) ?].
        hnf in Hroot_clk_lt' |- *.
        simpl in Hroot_clk_lt' |- *.
        lia.
      + constructor.
        * (* the difference of aclk is troublesome ... *)
          apply dmono in Hrespect_attach.
          rewrite -> Foralltr_cons_iff in Hrespect_attach |- *.
          split; [ | intuition ].
          apply proj1 in Hrespect_attach.
          hnf in Hrespect_attach |- *.
          simpl in Hrespect_attach |- *.
          unfold tc_ge in Hrespect_attach |- *.
          now rewrite -> Foralltr_cons_iff in Hrespect_attach |- *.
        * eapply List.Forall_impl.
          2: apply tc_respect_chn in Hrespect_pivot; apply Hrespect_pivot.
          simpl.
          intros.
          now apply dmono.
    - constructor.
      + unfold imono_single.
        destruct tc as [(z, clk_z, aclk_z) chn_z'].
        simpl.
        constructor.
        * (* impossible by assumption *)
          simpl in Hroot_clk_lt' |- *.
          lia.
        * now apply imono, Foralltr_cons_iff, proj1 in Hrespect_pivot.
      + constructor.
        * (* the difference of aclk is troublesome ... *)
          apply imono in Hrespect_attach.
          rewrite -> Foralltr_cons_iff in Hrespect_attach |- *.
          split; intuition.
        * eapply List.Forall_impl.
          2: apply tc_respect_chn in Hrespect_pivot; apply Hrespect_pivot.
          simpl.
          intros.
          now apply imono.
  Qed.

End TC_Join.

(* TODO tc_join tc tc' = tc_join tc (prefix); this may not be useful enough, though *)

Section Preorder_Prefix_Theory.

(* it is very difficult to use only one version of this ... *)

Fixpoint tc_vertical_splitr (full : bool) tc (l : list nat) : treeclock :=
  match l with
  | nil => Node (tr_rootinfo tc) (if full then tr_rootchn tc else nil)
  | x :: l' =>
    match nth_error (tr_rootchn tc) x with
    | Some ch => Node (tr_rootinfo tc) (tc_vertical_splitr full ch l' :: skipn (S x) (tr_rootchn tc))
    (* | None => Node (tr_rootinfo tc) (skipn (S x) (tr_rootchn tc)) *)
    | None => Node (tr_rootinfo tc) nil
    end
  end.

(* compute both the positions and thread ids at the same time *)

Fixpoint tc_traversal_waitlist tc (l : list nat) : (list (list nat)) * (list treeclock) :=
  match l with
  | nil => (nil, nil)
  | x :: l' =>
    match nth_error (tr_rootchn tc) x with
    | Some ch => 
      let: (res1, res2) := (tc_traversal_waitlist ch l') in
      ((map (fun i => i :: nil) (seq 0 x)) ++ (map (fun l0 => x :: l0) res1), (firstn x (tr_rootchn tc)) ++ res2)
    | None => 
      ((map (fun i => i :: nil) (seq 0 (length (tr_rootchn tc)))), (tr_rootchn tc))
    end
  end.

Definition pos_succ (l : list nat) :=
  match rev l with
  | nil => nil
  | x :: l' => rev ((S x) :: l')
  end.

Fact pos_succ_nil : pos_succ nil = nil. Proof eq_refl. 

Fact pos_succ_last l x : 
  pos_succ (l ++ x :: nil) = l ++ (S x) :: nil.
Proof. unfold pos_succ. rewrite ! rev_app_distr. simpl. now rewrite rev_involutive. Qed.

Fact pos_succ_cons x y l : 
  pos_succ (x :: y :: l) = x :: pos_succ (y :: l).
Proof. 
  assert (y :: l <> nil) as (l' & y' & E)%exists_last by auto.
  rewrite -> ! E, -> ! app_comm_cons, -> ! pos_succ_last, -> app_comm_cons.
  reflexivity.
Qed.

Fact tc_traversal_waitlist_align tc l : 
  length (fst (tc_traversal_waitlist tc l)) = length (snd (tc_traversal_waitlist tc l)).
Proof.
  revert tc.
  induction l as [ | x l IH ]; intros; simpl; try reflexivity.
  destruct tc as [ni chn]; simpl. 
  destruct (nth_error chn x) as [ ch | ] eqn:E; simpl.
  - destruct (tc_traversal_waitlist ch l) as (res1, res2) eqn:EE; simpl.
    specialize (IH ch).
    rewrite -> ! EE in IH.
    simpl in IH.
    rewrite -> ! app_length, -> ! map_length, -> seq_length.
    f_equal; try assumption.
    apply nth_error_some_inrange in E.
    rewrite -> firstn_length_le; lia.
  - now rewrite -> ! map_length, -> seq_length.
Qed.

Fact tc_traversal_waitlist_length_lt_tc_size tc l : 
  length (snd (tc_traversal_waitlist tc l)) < tc_size tc.
Proof.
  revert tc.
  induction l as [ | x l IH ]; intros [ni chn]; intros; simpl; try lia.
  destruct (nth_error chn x) as [ ch | ] eqn:E; simpl.
  - destruct (tc_traversal_waitlist ch l) as (res1, res2) eqn:EE; simpl.
    specialize (IH ch).
    rewrite EE in IH.
    simpl in IH.
    rewrite <- firstn_skipn with (n:=x) (l:=chn) at 2.
    rewrite flat_map_app.
    rewrite ! app_length.
    match goal with |- (_ + ?a < S (_ + ?b))%nat => enough (a < S b)%nat end.
    + pose proof (tcs_size_le_full (firstn x chn)).
      lia.
    + apply nth_error_split in E.
      (* TODO streamline this? *)
      destruct E as (pre & suf & Echn & Elen).
      rewrite -> Echn, -> list.drop_app_alt.
      2: auto.
      simpl.
      rewrite app_length.
      unfold tc_size in IH.
      lia.
  - pose proof (tcs_size_le_full chn).
    lia.
Qed.

Fact tc_traversal_waitlist_pos_notnil tc l : 
  Forall (fun l' => l' <> nil) (fst (tc_traversal_waitlist tc l)).
Proof.
  destruct l as [ | x l ], tc as [ni chn]; simpl; auto.
  destruct (nth_error chn x) as [ ch | ] eqn:E; simpl.
  - destruct (tc_traversal_waitlist ch l) as (res1, res2) eqn:EE; simpl.
    rewrite Forall_app, ! Forall_map.
    split; now apply list.Forall_true.
  - rewrite Forall_map.
    now apply list.Forall_true.
Qed.

Fact tc_traversal_waitlist_pos_app pos1 : forall tc pos2 sub (H : tc_locate tc pos1 = Some sub),
  tc_traversal_waitlist tc (pos1 ++ pos2) = 
    (fst (tc_traversal_waitlist tc pos1) ++ (map (fun pos => pos1 ++ pos) (fst (tc_traversal_waitlist sub pos2))), 
      snd (tc_traversal_waitlist tc pos1) ++ snd (tc_traversal_waitlist sub pos2)).
Proof.
  induction pos1 as [ | x pos1 IH ]; intros; simpl in *.
  - injection H as <-.
    rewrite -> map_id_eq.
    now destruct (tc_traversal_waitlist _ _).
  - destruct tc as [ni chn].
    simpl in *.
    destruct (nth_error chn x) eqn:E; try discriminate.
    rewrite -> (IH _ pos2 _ H).
    do 2 destruct (tc_traversal_waitlist _ _).
    simpl.
    rewrite -> ! map_app, -> map_map, <- ! app_assoc.
    reflexivity.
Qed.

Lemma tc_traversal_terminate l : forall tc (Hnil : fst (tc_traversal_waitlist tc l) = nil),
  tc_vertical_splitr true tc l = tc.
Proof.
  induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in Hnil |- *.
  - congruence.
  - destruct (nth_error chn x) as [ ch | ] eqn:E.
    2: destruct chn; simpl in Hnil; congruence.
    f_equal.
    destruct (tc_traversal_waitlist _ _) eqn:Ew.
    simpl in Hnil.
    apply app_eq_nil in Hnil.
    destruct Hnil as (E1%map_eq_nil & ->%map_eq_nil).
    assert (x = 0%nat) as -> by (now destruct chn, x).
    specialize (IH ch).
    rewrite -> Ew in IH.
    rewrite IH; auto.
    destruct chn; simpl in E; try discriminate.
    injection E as ->.
    now simpl; rewrite skipn_O.
Qed.

Local Tactic Notation "injection_last_pair" "in_" hyp(E) "as_" ident(E1) ident(E2) :=
  match type of E with (?l1 ++ ?y1, ?l2 ++ ?y2) = (?l1' ++ ?y1', ?l2' ++ ?y2') =>
    assert (l1 ++ y1 = l1' ++ y1') as E1 by congruence;
    assert (l2 ++ y2 = l2' ++ y2') as E2 by congruence;
    rewrite -> app_inj_tail_iff in E1, E2 end.

(* slightly tedious, but maybe no much better way ... *)
(* TODO maybe extract a proof pattern (e.g., for tc_traversal_waitlist) for the following proofs? *)

Lemma tc_traversal_waitlist_continue_trivial tc l y (Hle : y <= length (tr_rootchn tc))
  (H : tc_traversal_waitlist tc l = (map (fun i => i :: nil) (seq 0 y), firstn y (tr_rootchn tc)))
  res1 l' res2 sub' (E : tc_traversal_waitlist tc l = (res1 ++ l' :: nil, res2 ++ sub' :: nil)) :
  tc_locate tc l' = Some sub' /\ tc_traversal_waitlist tc l' = (res1, res2).
Proof.
  destruct tc as [ni chn]; simpl in *.
  rewrite H in E.
  destruct y as [ | y ].
  1: simpl in E; inversion E; now destruct res1.
  rewrite <- Nat.add_1_r in E at 1. 
  rewrite -> seq_app with (len2:=1), -> map_app in E.
  simpl in E.
  (* FIXME: revise this destruction *)
  destruct chn eqn:Etmp.
  1: inversion Hle.
  rewrite <- Etmp in *.
  assert (firstn (S y) chn <> nil) as (res2' & lst & E2)%exists_last by now subst.
  rewrite -> E2 in E.
  injection_last_pair in_ E as_ EE1 EE2.
  destruct EE1 as (? & <-), EE2 as (? & <-).
  simpl.
  epose proof (list.last_snoc _ _) as Elst.
  rewrite <- E2, -> firstn_last in Elst; try assumption.
  rewrite Elst, ! app_nil_r, <- removelast_firstn, -> E2, -> removelast_last.
  2: lia.
  split; congruence.
Qed.

(* this will be used in proving the transition of nochild case *)

Lemma tc_traversal_waitlist_continue tc : forall l (H : tc_locate tc l) 
  res1 l' res2 sub' (E : tc_traversal_waitlist tc l = (res1 ++ l' :: nil, res2 ++ sub' :: nil)),
  tc_locate tc l' = Some sub' /\ tc_traversal_waitlist tc l' = (res1, res2).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  destruct l as [ | x l ]; simpl in E.
  1: inversion E; now destruct res1.
  simpl in H.
  destruct (nth_error chn x) as [ ch | ] eqn:E0; simpl.
  - destruct (tc_traversal_waitlist ch l) as (res1', res2') eqn:EE; simpl.
    pose proof (tc_traversal_waitlist_align ch l) as Hlen.
    rewrite -> EE in Hlen.
    simpl in Hlen.
    (* find where is this last *)
    destruct (list_rev_destruct res1') as [ -> | (res1'' & l'' & Etmp') ].
    + destruct res2'; simpl in Hlen; try discriminate.
      simpl in E.
      rewrite ! app_nil_r in E.
      apply tc_traversal_waitlist_continue_trivial with (y:=x) (l:=x::l); simpl.
      1: apply nth_error_some_inrange in E0; lia.
      all: now rewrite E0, EE, ! app_nil_r.
    + rewrite -> Etmp', -> app_length, -> Nat.add_1_r in Hlen.
      destruct (list_rev_destruct res2') as [ -> | (res2'' & sub'' & Etmp2') ]; try discriminate.
      rewrite -> Etmp', -> Etmp2', -> map_app, -> ! app_assoc in E.
      simpl in E.
      apply Forall_forall with (x:=ch) in IH.
      2: now apply nth_error_In in E0.
      specialize (IH _ H res1'' l'' res2'' sub'').
      rewrite -> EE, -> Etmp', -> Etmp2' in IH.
      specialize (IH eq_refl).
      destruct IH as (IH1 & IH2).
      injection_last_pair in_ E as_ EE1 EE2.
      destruct EE1 as (? & <-), EE2 as (? & <-).
      simpl.
      rewrite E0, IH1, IH2.
      split; congruence.
  - apply tc_traversal_waitlist_continue_trivial with (y:=length chn) (l:=x::l); simpl.
    1: constructor.
    all: now rewrite E0.
Qed.

Lemma tc_vertical_splitr_lastover l : forall tc (H : tc_locate tc l = None),
  tc_vertical_splitr false tc l = tc_vertical_splitr false tc (removelast l).
Proof.
  induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in H |- *.
  - reflexivity.
  - destruct (nth_error chn x) as [ ch | ] eqn:E.
    + rewrite -> IH; auto.
      destruct l; simpl; try discriminate.
      now rewrite E.
    + destruct l; simpl.
      1: reflexivity.
      now rewrite E.
Qed.

Fact tc_vertical_splitr_leaf_ignorefull l : forall tc ni0 (H : tc_locate tc l = Some (Node ni0 nil)), 
  tc_vertical_splitr false tc l = tc_vertical_splitr true tc l.
Proof.
  induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in H |- *.
  - injection H as ->.
    subst.
    reflexivity.
  - destruct (nth_error chn x) as [ ch | ] eqn:E0; simpl.
    + now erewrite -> IH; eauto.
    + reflexivity.
Qed.

Lemma tc_vertical_splitr_continue l : forall tc
  res1 l' res2 sub' (E : tc_traversal_waitlist tc l = (res1 ++ l' :: nil, res2 ++ sub' :: nil)),
  tc_vertical_splitr true tc l = tc_vertical_splitr true tc (pos_succ l') /\
  (* merged, just for reducing repeating proof preparation; 
    and this is not quite compatible with tc_traversal_waitlist_continue, so merge to here *)
  (forall ni, tc_locate tc l = Some (Node ni nil) -> tc_locate tc (pos_succ l')).
Proof.
  induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in E |- *.
  1: destruct res1; inversion E; discriminate.
  destruct (nth_error chn x) as [ ch | ] eqn:E0; simpl.
  - destruct (tc_traversal_waitlist ch l) as (res1', res2') eqn:EE; simpl.
    pose proof (tc_traversal_waitlist_align ch l) as Hlen.
    rewrite -> EE in Hlen.
    simpl in Hlen.
    destruct (list_rev_destruct res1') as [ -> | (res1'' & l'' & ->) ].
    + destruct res2'; try discriminate.
      simpl in E.
      rewrite -> ! app_nil_r in E.
      destruct x as [ | x ].
      1: simpl in E; inversion E; now destruct res1.
      (* TODO ...? *)
      rewrite <- Nat.add_1_r in E at 1. 
      rewrite -> seq_app with (len2:=1), -> map_app in E.
      simpl in E.
      match type of E with (?l1 ++ ?y1, _) = (?l1' ++ ?y1', _) =>
        assert (l1 ++ y1 = l1' ++ y1') as EE1 by congruence;
        rewrite -> app_inj_tail_iff in EE1; 
        destruct EE1 as (? & <-) end.
      simpl in E0 |- *.
      rewrite E0.
      split.
      * do 2 f_equal.
        transitivity ch; [ | now destruct ch ].
        (* termination *)
        apply tc_traversal_terminate.
        now rewrite EE.
      * now intros.
    + destruct (list_rev_destruct res2') as [ -> | (res2'' & sub'' & ->) ].
      1: rewrite -> app_length, -> Nat.add_1_r in Hlen; discriminate.
      rewrite -> map_app, -> ! app_assoc in E.
      simpl in E.
      injection_last_pair in_ E as_ EE1 EE2.
      destruct EE1 as (? & <-), EE2 as (? & <-).
      destruct (list_rev_destruct l'') as [ El'' | (y & l''' & ->) ].
      * (* impossible *)
        pose proof (tc_traversal_waitlist_pos_notnil ch l) as HH.
        rewrite EE in HH.
        simpl in HH.
        now apply Forall_app, proj2, Forall_cons_iff, proj1 in HH.
      * rewrite app_comm_cons, ! pos_succ_last, <- app_comm_cons.
        simpl.
        specialize (IH ch _ _ _ _ EE).
        rewrite pos_succ_last in IH.
        destruct IH as (IH1 & IH2).
        split.
        --now rewrite -> IH1, E0.
        --intros ?.
          rewrite E0.
          now apply IH2.
  - destruct (list_rev_destruct chn) as [ -> | (chn' & ch & Echn) ].
    1: simpl in E; inversion E; now destruct res1.
    rewrite -> Echn, -> app_length, -> seq_app, -> map_app in E.
    simpl in E.
    injection_last_pair in_ E as_ EE1 EE2.
    destruct EE1 as (? & <-), EE2 as (? & <-).
    replace (pos_succ _) with ((length chn) :: nil).
    2: unfold pos_succ; subst; simpl; rewrite -> app_length, -> Nat.add_1_r; reflexivity.
    simpl.
    pose proof (le_n (length chn)) as Htmp%nth_error_None.
    now rewrite Htmp.
Qed.

(* may use this to trace on the original tree (i.e., tc) *)

Lemma tc_vertical_splitr_is_prefix full l : forall tc, 
  prefixtr (tc_vertical_splitr full tc l) tc.
Proof.
  induction l as [ | x l IH ]; intros [ni chn]; simpl.
  - destruct full.
    + apply prefixtc_refl.
    + apply prefixtc_nil_l.
  - destruct (nth_error chn x) as [ ch | ] eqn:E.
    2: now apply prefixtc_nil_l.
    apply nth_error_split in E.
    destruct E as (pre & suf & Echn & Elen).
    rewrite -> Echn at 1. 
    rewrite -> list.cons_middle, -> app_assoc, -> list.drop_app_alt.
    2: rewrite app_length; simpl; lia.
    apply prefixtc_intro with (chn_sub:=ch :: suf).
    + subst chn.
      now apply list.sublist_inserts_l.
    + now constructor.
Qed.

Inductive tc_traversal_snapshot (tc : treeclock) : list thread -> treeclock -> Prop :=
  | TTSend : tc_traversal_snapshot tc nil tc
  | TTSitm : forall stk l sub pf full, 
    tc_locate tc l = Some sub ->
    (* full should be false only in the exceeding case, and be true otherwise *)
    full = isSome (tc_locate tc (pos_succ l)) ->
    stk = (map tr_rootid (snd (tc_traversal_waitlist tc l) ++ (sub :: nil))) ->
    pf = tc_vertical_splitr full tc (pos_succ l) ->
    tc_traversal_snapshot tc stk pf.

Fact tc_traversal_snapshot_inv_stacknil tc stk pf (E : stk = nil)
  (H : tc_traversal_snapshot tc stk pf) : tc = pf.
Proof.
  inversion H; subst.
  - reflexivity.
  - match goal with HH : nil = map _ _ |- _ => 
      rewrite -> map_app in HH; simpl in HH; symmetry in HH; apply app_eq_nil in HH; eqsolve 
    end.
Qed.

Fact tc_traversal_snapshot_inv_stacknotnil tc stk pf (E : stk <> nil)
  (H : tc_traversal_snapshot tc stk pf) : 
  exists l sub, tc_locate tc l = Some sub /\
    stk = (map tr_rootid (snd (tc_traversal_waitlist tc l) ++ (sub :: nil))) /\
    pf = tc_vertical_splitr (tc_locate tc (pos_succ l)) tc (pos_succ l).
Proof.
  inversion H; subst.
  - contradiction.
  - exists l, sub.
    match goal with HH : tc_locate _ (pos_succ _) = _ |- _ => rewrite HH | _ => idtac end.
    intuition.
Qed.

(* two different transitions of using tc_get_updated_nodes_join *)

Lemma tc_traversal_snapshot_trans_children tc l sub 
  (Hsub : tc_locate tc l = Some sub) (Echn : tr_rootchn sub <> nil) :
  tc_traversal_snapshot tc 
    (map tr_rootid (snd (tc_traversal_waitlist tc l) ++ tr_rootchn sub)) 
    (tc_vertical_splitr false tc l).
Proof.
  destruct sub as [ni chn].
  simpl in Echn |- *.
  remember (length chn) as n eqn:Elen.
  destruct n as [ | n ].
  1: destruct chn; simpl in *; try contradiction; try discriminate.
  clear Echn.
  (* many ways to specify lst_ch *)
  destruct (list_rev_destruct chn) as [ -> | (chn' & lst_ch & Echn) ]; try discriminate.
  pose proof Elen as Elen'.
  rewrite -> Echn, -> app_length, -> Nat.add_1_r, -> Nat.succ_inj_wd in Elen'.
  assert (nth_error chn n = Some lst_ch) as Enth.
  {
    subst.
    rewrite -> nth_error_app2, -> Nat.sub_diag; simpl; auto.
  }
  assert (tc_locate tc (l ++ S n :: nil) = None) as Eex.
  {
    apply tc_locate_pos_app with (pos2:=S n :: nil) in Hsub.
    rewrite Hsub.
    cbn delta -[nth_error] beta iota.
    pose proof (le_n (S n)) as Htmp.
    rewrite -> Elen, <- nth_error_None in Htmp at 1.
    now rewrite Htmp.
  }
  apply TTSitm with (l:=l ++ (n :: nil)) (sub:=lst_ch) (full:=false).
  - apply tc_locate_pos_app with (pos2:=n :: nil) in Hsub.
    simpl in Hsub.
    now rewrite Enth in Hsub.
  - now rewrite -> pos_succ_last, -> Eex.
  - eapply tc_traversal_waitlist_pos_app with (pos2:=n :: nil) in Hsub.
    rewrite Hsub.
    simpl.
    rewrite Enth, ! app_nil_r.
    simpl.
    rewrite <- app_assoc.
    do 2 f_equal.
    subst.
    now rewrite list.take_app_alt.
  - rewrite -> pos_succ_last, -> tc_vertical_splitr_lastover with (l:=l ++ S n :: nil).
    + now rewrite removelast_last.
    + assumption.
Qed.

Lemma tc_traversal_snapshot_trans_nochild tc l sub 
  (Hsub : tc_locate tc l = Some sub) (Echn : tr_rootchn sub = nil) :
  tc_traversal_snapshot tc 
    (map tr_rootid (snd (tc_traversal_waitlist tc l))) 
    (* essentially for true, though *)
    (tc_vertical_splitr false tc l).
Proof.
  destruct sub as [ni chn].
  simpl in Echn |- *.
  subst chn.
  (* much manipulation *)
  rewrite -> tc_vertical_splitr_leaf_ignorefull with (ni0:=ni); try assumption.
  destruct (tc_traversal_waitlist tc l) as (res1, res2) eqn:EE.
  pose proof (tc_traversal_waitlist_align tc l) as Hlen.
  rewrite EE in Hlen.
  simpl in Hlen |- *.
  destruct (list_rev_destruct res2) as [ -> | (res2' & sub' & ->) ].
  - destruct res1; try discriminate.
    simpl.
    rewrite -> tc_traversal_terminate.
    2: now rewrite EE.
    apply TTSend.
  - destruct (list_rev_destruct res1) as [ -> | (res1' & l' & ->) ].
    1: rewrite -> app_length, -> Nat.add_1_r in Hlen; discriminate.
    pose proof EE as (Hcont_t1 & Hcont_t2)%tc_vertical_splitr_continue.
    pose proof EE as (Hcont_w1 & Hcont_w2)%tc_traversal_waitlist_continue.
    2: now rewrite Hsub.
    apply TTSitm with (l:=l') (sub:=sub') (full:=true).
    + tauto.
    + symmetry.
      eapply Hcont_t2; eauto.
    + now rewrite -> Hcont_w2.
    + now rewrite Hcont_t1.
Qed.

Corollary tc_traversal_snapshot_trans tc l sub (Hsub : tc_locate tc l = Some sub) :
  tc_traversal_snapshot tc 
    (map tr_rootid (snd (tc_traversal_waitlist tc l) ++ tr_rootchn sub)) 
    (tc_vertical_splitr false tc l).
Proof.
  destruct (list_ifnil_destruct (tr_rootchn sub)) as [ H | H ].
  - rewrite H, app_nil_r.
    eapply tc_traversal_snapshot_trans_nochild; eauto.
  - eapply tc_traversal_snapshot_trans_children; eauto.
Qed.

Fact tc_vertical_splitr_locate l :
  forall tc sub full (H : tc_locate tc l = Some sub),
    tc_locate (tc_vertical_splitr full tc l) (List.repeat 0%nat (length l)) = 
    Some (tc_vertical_splitr full sub nil).
Proof.
  induction l as [ | x l IH ]; intros [ni chn]; intros; simpl in H |- *.
  1: injection H as <-; reflexivity.
  destruct (nth_error chn x) as [ ch | ] eqn:E0; simpl.
  2: discriminate.
  erewrite IH; eauto.
Qed.

(* initial condition *)

Lemma tc_traversal_snapshot_init tc : 
  tc_traversal_snapshot tc (map tr_rootid (tr_rootchn tc)) (Node (tr_rootinfo tc) nil).
Proof.
  destruct tc as [ni chn].
  simpl.
  destruct (list_ifnil_destruct chn) as [ -> | Hnn ].
  - now apply TTSend.
  - now apply (tc_traversal_snapshot_trans_children (Node ni chn) nil _ eq_refl Hnn).
Qed.

End Preorder_Prefix_Theory.

(* TODO where to put these ... *)

Fact tc_attach_nodes_colocate forest tc :
  forall l sub (H : tc_locate tc l = Some sub), 
    base.fmap tr_rootinfo (tc_locate (tc_attach_nodes forest tc) l) = Some (tr_rootinfo sub).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  destruct l as [ | x l ]; simpl in H |- *.
  - now injection H as <-.
  - destruct (nth_error chn x) as [ ch | ] eqn:Enth; try discriminate.
    rewrite nth_error_app1.
    2: rewrite map_length; apply nth_error_some_inrange in Enth; lia.
    rewrite nth_error_map, Enth.
    simpl.
    rewrite -> Forall_forall in IH.
    specialize (IH _ (nth_error_In _ _ Enth) _ _ H).
    apply IH.
Qed.

End TreeClock.
