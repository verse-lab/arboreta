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

Fact tc_getclk_perm_congr_pre [tcs1 tcs2] (Hnodup1 : trs_roots_NoDupId tcs1)
  (Hperm : Permutation (map tc_rootinfo_partial tcs1) (map tc_rootinfo_partial tcs2)) :
  forall t, base.fmap tc_rootclk (trs_find_node t tcs1) = base.fmap tc_rootclk (trs_find_node t tcs2).
Proof.
  intros.
  etransitivity.
  (* FIXME: the combination use of "Basics.compose" and "option.option_fmap_compose" might be extracted as a tactic? *)
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
  Node info_u' (tc_get_updated_nodes_join_aux tc (tc_getclk (info_id info_u') tc) chn_u').
Proof. destruct tc'. reflexivity. Qed.

(* The recursive version of "detachNodes" will return a pair: the resulting tree after detaching
    all subtrees, and also the list of detached subtrees. *)

Fixpoint tc_detach_nodes (tcs : list treeclock) (tc : treeclock) : treeclock * list treeclock :=
  let: Node ni chn := tc in
  let: (new_chn, res) := List.split (map (tc_detach_nodes tcs) chn) in
  let: (res', new_chn') := List.partition (fun tc' => isSome (trs_find_node (tr_rootid tc') tcs))
    new_chn in
  (Node ni new_chn', (List.concat res) ++ res').

(* The recursive version of "attachNodes" will be given a list of subtrees and a tree; this function
    will traverse the tree and try attaching subtrees from the list to the tree. *)

Fixpoint tc_attach_nodes (forest : list treeclock) (tc' : treeclock) : treeclock :=
  let: Node info_u' chn' := tc' in
  let: u_pre := trs_find_node (info_tid info_u') forest in
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

Fact tc_ge_root_aclk_useless [u clk aclk aclk'] [chn : list treeclock] [tc_larger]
  (Hge : tc_ge tc_larger (Node (mkInfo u clk aclk) chn)) :
  tc_ge tc_larger (Node (mkInfo u clk aclk') chn).
Proof.
  constructor.
  - now apply Foralltr_self in Hge.
  - now apply Foralltr_chn in Hge.
Qed.

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
  pose proof (id_nodup_find_self' Hnodup) as Hself.
  eapply Foralltr_impl; eauto.
  simpl.
  intros tc0 E.
  specialize (H (tr_rootid tc0)).
  unfold tc_getclk in H |- *.
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

Fact tc_respect_root_aclk_useless [u clk aclk aclk'] [chn : list treeclock] [tc_larger]
  (Hrespect : tc_respect (Node (mkInfo u clk aclk) chn) tc_larger) :
  tc_respect (Node (mkInfo u clk aclk') chn) tc_larger.
Proof.
  constructor.
  - apply dmono in Hrespect.
    constructor.
    + apply Foralltr_self in Hrespect.
      hnf in Hrespect |- *.
      simpl in Hrespect |- *.
      intros; eapply tc_ge_root_aclk_useless; eauto.
    + now apply Foralltr_chn in Hrespect.
  - apply imono in Hrespect.
    constructor.
    + now apply Foralltr_self in Hrespect.
    + now apply Foralltr_chn in Hrespect.
Qed.

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

Fact tc_shape_inv_nil ni : tc_shape_inv (Node ni nil).
Proof.
  constructor.
  - hnf; simpl; constructor; auto using NoDup_nil.
  - constructor; auto.
    hnf; simpl; auto.
  - constructor; auto.
    hnf; simpl; constructor.
Qed.

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
  cbn delta -[tc_get_updated_nodes_join info_id] iota beta;
  rewrite -> tc_get_updated_nodes_join_eta.

Tactic Notation "tc_get_updated_nodes_join_unfold" "in_" hyp(H) :=
  cbn delta -[tc_get_updated_nodes_join info_id] iota beta in H;
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
  (* "Haclk_impl_clk" is a simple condition, which is implied by "imono" (see below)
    and is only used for this proof *)
  (Haclk_impl_clk : forall tc', In tc' chn_u' -> 
    tc_rootaclk tc' <= clk -> 
    tc_rootclk tc' <= (tc_getclk (tr_rootid tc') tc)) 
  (Hsorted: StronglySorted ge (map tc_rootaclk chn_u')) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc clk chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    Forall (fun tc' => tc_getclk (tr_rootid tc') tc < tc_rootclk tc' /\
      clk < tc_rootaclk tc') chn_u'' /\
    Forall (fun tc' => tc_getclk (tr_rootid tc') tc < tc_rootclk tc' -> In tc' chn_u'') chn_u'.
Proof.
  induction chn_u' as [ | tc_v' chn_u' IH ].
  - exists nil.
    intuition.
  - simpl in Haclk_impl_clk, Hsorted.
    apply StronglySorted_inv in Hsorted.
    destruct Hsorted as (Hsorted & Hallle).
    destruct tc_v' as [(v', clk_v', aclk_v') chn_v'] eqn:Etc_v'.
    simpl in Hallle.
    pose proof (fun tc' H => Haclk_impl_clk tc' (or_intror H)) as H'.
    specialize (IH H' Hsorted).
    destruct IH as (chn_u'' & Hsub & Hres & Halllt & Hinsub).
    setoid_rewrite -> Forall_cons_iff.
    tc_get_updated_nodes_join_unfold.
    destruct (clk_v' <=? tc_getclk v' tc) eqn:Ecmp_clk_v'.
    + apply Nat.leb_le in Ecmp_clk_v'.
      destruct (aclk_v' <=? clk) eqn:Ecmp_aclk_v'.
      * apply Nat.leb_le in Ecmp_aclk_v'.
        exists nil.
        simpl.
        do 3 (split; [ auto using list.sublist_nil_l | ]).
        split; [ now apply Nat.nlt_ge | ].
        (* use transitivity of sorted *)
        rewrite Forall_map in Hallle.
        revert Hallle.
        apply Forall_impl_impl, Forall_forall.
        intros ch' Hin' HH.
        apply Nat.nlt_ge, H'; auto; try lia.
      * exists chn_u''.
        split; [ now constructor | ].
        do 3 (split; try assumption).
        simpl.
        intros; lia.
    + apply Nat.leb_gt in Ecmp_clk_v'.
      pose proof (contra_not (Haclk_impl_clk _ (or_introl eq_refl))) as Ecmp_clk_v'_lt.
      rewrite 2 Nat.nle_gt in Ecmp_clk_v'_lt.
      simpl in Ecmp_clk_v'_lt.
      specialize (Ecmp_clk_v'_lt Ecmp_clk_v').
      exists (tc_v' :: chn_u'').
      subst tc_v'.
      split; [ now constructor | ].
      simpl.
      split; [ now f_equal | ].
      split; [ constructor; simpl; auto | ].
      split; [ auto | ].
      revert Hinsub.
      apply Forall_impl; tauto.
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
  simpl in H.
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
  eapply prefixtr_by_sublist_map; eauto.
  now apply sublist_map.
Qed.

Corollary tc_get_updated_nodes_join_map_map_rootinfo tc tcs :
  map tr_rootinfo (map (tc_get_updated_nodes_join tc) tcs) = map tr_rootinfo tcs.
Proof.
  rewrite -> prefixtr_rootinfo_same_map with (trs':=tcs); auto.
  apply Forall2_mapself_l, list.Forall_true, tc_get_updated_nodes_join_is_prefix.
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

(* subsumption of "tc_get_updated_nodes_join_aux_result"; more useful *)
Lemma tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn_u' 
  (Hshape_tc' : tc_shape_inv (Node (mkInfo u' clk_u' aclk_u') chn_u')) 
  (Hrespect : tc_respect (Node (mkInfo u' clk_u' aclk_u') chn_u') tc) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc (tc_getclk u' tc) chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    Forall (fun tc' => tc_getclk (tr_rootid tc') tc < tc_rootclk tc' /\
      (tc_getclk u' tc) < tc_rootaclk tc') chn_u'' /\
    Forall (fun tc' => ~ In tc' chn_u'' -> tc_ge tc tc') chn_u' /\
    (* this iff is sometimes useful *)
    Forall (fun tc' => In tc' chn_u'' <-> (tc_getclk (tr_rootid tc') tc) < tc_rootclk tc') chn_u'.
Proof.
  (* get aclk_impl_clk *)
  pose proof (imono Hrespect) as Himono.
  apply Foralltr_cons_iff, proj1 in Himono.
  pose proof (imono_single_aclk_impl_clk Himono) as Haclk_impl_clk.
  pose proof (fun tc' H => contra_not (Haclk_impl_clk tc' H)) as Haclk_impl_clk'.
  repeat setoid_rewrite -> Nat.nle_gt in Haclk_impl_clk'.
  pose proof (tc_get_updated_nodes_join_aux_result tc (tc_getclk u' tc) chn_u' 
    Haclk_impl_clk (Foralltr_self (aclk_decsorted Hshape_tc'))) as (chn_u'' & Hsub & Hres & Halllt & Hinsub).
  exists chn_u''.
  do 3 (split; try assumption).
  apply base.and_wlog_l.
  - (* slightly cheat here: use dmono instead of imono to derive this *)
    apply Forall_impl_impl, Forall_forall.
    intros ch' Hin' -> Hle%Nat.nlt_ge.
    revert Hle; pattern ch'; eapply Foralltr_self, dmono.
    revert ch' Hin'; apply Forall_forall.
    now apply tc_respect_chn in Hrespect.
  - apply list.Forall_and.
    split; auto.
    rewrite Forall_forall in Halllt |- *.
    firstorder.
Qed.

(* make it over the whole tree *)

Corollary tc_get_updated_nodes_join_shape [tc tc'] (Hshape: tc_shape_inv tc')
  (Hrespect: tc_respect tc' tc) :
  Foralltr (fun tc' => 
    Forall (fun tc'' => tc_getclk (tr_rootid tc'') tc < tc_rootclk tc'' /\
      tc_getclk (tr_rootid tc') tc < tc_rootaclk tc'') (tr_rootchn tc')) 
    (tc_get_updated_nodes_join tc tc').
Proof.
  (* note: here, doing induction on the prefix relation of "(tc_get_updated_nodes_join tc tc')" will not work, 
    since we are unable to unify the sublists in "prefixtr_ind_2" and in "tc_get_updated_nodes_join_aux_result_regular"
    FIXME: this might be an interesting problem to look into later? *)
  revert tc Hrespect.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using tree_ind_2; intros.
  tc_get_updated_nodes_join_unfold.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & -> & H & _ & _).
  constructor.
  - simpl.
    unfold tr_rootid, tc_rootclk, tc_rootaclk.
    now rewrite <- Forall_map with (P:=fun ni => tc_getclk (info_id ni) tc < info_clk ni /\ tc_getclk u' tc < info_aclk ni) (f:=tr_rootinfo), 
      -> tc_get_updated_nodes_join_map_map_rootinfo, -> Forall_map.
  - eapply Forall_map, sublist_Forall; eauto.
    rewrite -> Forall_forall in IH |- *.
    intros ch' Hin'.
    apply IH; auto.
    all: revert ch' Hin'; apply Forall_forall.
    + now apply tc_shape_inv_chn in Hshape.
    + now apply tc_respect_chn in Hrespect.
Qed.

Corollary tc_get_updated_nodes_join_shape' [tc tc'] (Hshape: tc_shape_inv tc')
  (Hrespect: tc_respect tc' tc) 
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') :
  Foralltr (fun tc' => tc_getclk (tr_rootid tc') tc < tc_rootclk tc') 
    (tc_get_updated_nodes_join tc tc').
Proof.
  apply Foralltr_cons_iff'.
  split.
  - unfold tr_rootid, tc_rootclk.
    erewrite 1 prefixtr_rootinfo_same.
    2: apply tc_get_updated_nodes_join_is_prefix.
    auto.
  - apply Foralltr_Forall_chn_comm.
    pose proof (tc_get_updated_nodes_join_shape Hshape Hrespect) as H.
    revert H.
    apply Foralltr_impl.
    intros ?; now rewrite list.Forall_and.
Qed.

(* by analysis, rather by induction *)
Corollary tc_get_updated_nodes_join_sound [tc'] (Hshape: tc_shape_inv tc')
  [tc] (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') :
  forall t, isSome (tr_getnode t (tc_get_updated_nodes_join tc tc')) = true ->
    tc_getclk t tc < tc_getclk t tc'.
Proof.
  intros t (sub & <- & Hin)%tr_getnode_in_iff%in_map_iff.
  rewrite -> (tc_getclk_as_fmap _ tc').
  change tc_rootclk with (Basics.compose info_clk tr_rootinfo).
  rewrite option.option_fmap_compose, (id_nodup_find_prefix' (tc_get_updated_nodes_join_is_prefix tc _) (tid_nodup Hshape) Hin).
  simpl.
  pattern sub.
  eapply Foralltr_subtr; eauto.
  now apply tc_get_updated_nodes_join_shape'.
Qed.

(* the complement part; constraining the nodes not on the prefix *)

Corollary tc_get_updated_nodes_join_shape_complement [tc'] (Hshape: tc_shape_inv tc')
  [tc] (Hrespect: tc_respect tc' tc) :
  Foralltr (fun tc'' => 
    ~ (In (tr_rootid tc'') (map tr_rootid (tr_flatten (tc_get_updated_nodes_join tc tc')))) ->
      tc_rootclk tc'' <= tc_getclk (tr_rootid tc'') tc) tc'.
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using tree_ind_2'; intros.
  tc_get_updated_nodes_join_unfold.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn' Hshape Hrespect) 
    as (chn_u'' & Hsub & E & _ & Hge & Halllt).
  rewrite E.
  pose proof (tc_shape_inv_chn Hshape) as Hshape_ch.
  pose proof (tc_respect_chn Hrespect) as Hrespect_ch.
  simpl in Hshape_ch, Hrespect_ch.
  rewrite -> List.Forall_forall in Hshape_ch, Hrespect_ch, Halllt, Hge.
  constructor.
  - simpl.
    intuition.
  - rewrite Forall_forall.
    intros ch' Hin'.
    specialize (IH _ Hin' ltac:(auto) ltac:(auto)).
    destruct (tc_getclk (tr_rootid ch') tc <? tc_rootclk ch') eqn:EE.
    + apply Nat.ltb_lt, Halllt in EE; try assumption.
      revert IH.
      apply Foralltr_impl.
      intros tr HH Hq.
      apply HH; intros Ht; apply Hq.
      right.
      eapply map_flat_map_In_conv; eauto.
      now apply in_map.
    + rewrite -> Nat.ltb_nlt, <- Halllt in EE; auto.
      (* use Hge *)
      apply Hge in EE; auto.
      revert EE.
      now apply Foralltr_impl.
Qed.

Corollary tc_get_updated_nodes_join_complete [tc'] (Hshape: tc_shape_inv tc')
  [tc] (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc')
  t (Hlt : tc_getclk t tc < tc_getclk t tc') :
    isSome (tr_getnode t (tc_get_updated_nodes_join tc tc')) = true.
Proof.
  destruct (tr_getnode _ _) eqn:E; auto.
  apply (f_equal (@isSome treeclock)), not_true_iff_false in E.
  setoid_rewrite <- trs_find_in_iff in E.
  (* proof by neg *)
  exfalso; revert Hlt; apply Nat.nlt_ge.
  unfold tc_getclk at 1.
  destruct (tr_getnode t tc') as [ res' | ] eqn:E'; [ | lia ].
  apply trs_find_has_id in E'.
  destruct E' as (Hin & <-).
  revert E.
  pattern res'.
  eapply Foralltr_subtr; eauto.
  now apply tc_get_updated_nodes_join_shape_complement.
Qed.

Corollary tc_get_updated_nodes_join_adequacy [tc'] (Hshape: tc_shape_inv tc')
  [tc] (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') t :
  tc_getclk t tc < tc_getclk t tc' <->
  isSome (tr_getnode t (tc_get_updated_nodes_join tc tc')) = true.
Proof.
  split; intros H.
  - now apply tc_get_updated_nodes_join_complete.
  - now apply tc_get_updated_nodes_join_sound.
Qed.

(* a sufficient condition, which will be useful in very later *)
Corollary tc_get_updated_nodes_root_notin [tc'] (Hshape: tc_shape_inv tc')
  [tc] (Hrespect: tc_respect tc' tc)
  (Hroot_clk_lt : tc_getclk (tr_rootid tc') tc < tc_rootclk tc')
  (Hroot_clk_le : tc_getclk (tr_rootid tc) tc' <= tc_rootclk tc) :
  ~ In (tr_rootid tc)
    (map tr_rootid (tr_flatten (tc_get_updated_nodes_join tc tc'))).
Proof.
  replace (tc_rootclk tc) with (tc_getclk (tr_rootid tc) tc) in Hroot_clk_le by (unfold tc_getclk; now rewrite tr_getnode_self).
  rewrite <- Nat.nlt_ge, -> (tc_get_updated_nodes_join_adequacy Hshape Hrespect), <- tr_getnode_in_iff in Hroot_clk_le; auto.
Qed.

End TC_Get_Updated_Nodes_Join.

Section TC_Detach_Nodes.

(* an ad-hoc destruct rule *)

Fact tc_detach_nodes_eta ni chn tcs :
  exists new_chn res res' new_chn', 
    List.split (map (tc_detach_nodes tcs) chn) = (new_chn, res) /\
    partition (fun tc' : treeclock => isSome (trs_find_node (tr_rootid tc') tcs)) new_chn = (res', new_chn') /\
    map (fun x : treeclock => fst (tc_detach_nodes tcs x)) chn = new_chn /\
    map (fun x : treeclock => snd (tc_detach_nodes tcs x)) chn = res /\
    filter (fun tc' : treeclock => isSome (trs_find_node (tr_rootid tc') tcs)) new_chn = res' /\
    filter (fun tc' : treeclock => negb (isSome (trs_find_node (tr_rootid tc') tcs))) new_chn = new_chn' /\
    tc_detach_nodes tcs (Node ni chn) = (Node ni new_chn', concat res ++ res').
Proof.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs) chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' => isSome (trs_find_node (tr_rootid tc') tcs)) new_chn)
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
  apply Forall_app; split.
  - subst res.
    (* a lot of structural predicate rules *)
    rewrite Forall_concat, Forall_map.
    revert IH.
    apply Forall_impl_impl, Forall_forall.
    intros ch Hin.
    apply Forall_impl.
    intros ? (sub & Hin' & ->).
    exists sub.
    split; auto.
    apply (in_flat_map_conv _ _ _ sub Hin (tr_flatten_proper_subtr Hin')).
  - subst res' new_chn.
    apply Forall_filter.
    rewrite Forall_map, Forall_forall.
    intros ch Hin.
    exists ch.
    split; [ apply (trs_flatten_self_in Hin) | auto ].
Qed.

Corollary tc_detach_nodes_snd2fst tcs tc :
  Forall (fun tc' => exists sub, In sub (tr_flatten tc) /\ (* weakened for convenience *)
    tc' = fst (tc_detach_nodes tcs sub))
  (snd (tc_detach_nodes tcs tc)).
Proof.
  eapply Forall_impl.
  2: apply tc_detach_nodes_snd2fst_pre.
  simpl.
  intros ? (sub & Hin%tr_flatten_proper_subtr & ->).
  eauto.
Qed.

Lemma tc_detach_nodes_dom_incl tcs tc :
  Forall (fun tc' => isSome (trs_find_node (tr_rootid tc') tcs) = true) (snd (tc_detach_nodes tcs tc)).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach.
  simpl.
  apply Forall_app; split.
  - subst res.
    now rewrite Forall_concat, Forall_map.
  - subst res' new_chn.
    rewrite map_filter_comm, Forall_map, Forall_forall.
    now setoid_rewrite filter_In.
Qed.

Lemma tc_detach_nodes_tcs_congr tcs1 tcs2 
  (H : forall x, In x (map tr_rootid tcs1) <-> In x (map tr_rootid tcs2)) tc :
  tc_detach_nodes tcs1 tc = tc_detach_nodes tcs2 tc.
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  simpl.
  rewrite -> map_ext_Forall with (g:=(tc_detach_nodes tcs2)); auto.
  destruct (List.split (map (tc_detach_nodes tcs2) chn)) as (new_chn, res) eqn:Esplit.
  rewrite -> partition_ext_Forall with (g:=(fun tc' => isSome (trs_find_node (tr_rootid tc') tcs2))); auto.
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
  subst.
  simpl.
  rewrite -> map_filter_comm.
  eapply prefixtr_by_sublist_map.
  1: apply IH.
  apply sublist_map, filter_sublist.
Qed.

Corollary tc_detach_nodes_snd_is_subprefix tcs tc :
  Forall (fun tc' => exists sub, In sub (tr_flatten tc) /\
    prefixtr tc' sub) (snd (tc_detach_nodes tcs tc)).
Proof.
  pose proof (tc_detach_nodes_snd2fst tcs tc) as Hto.
  revert Hto; apply Forall_impl.
  intros ? (sub & Hin & ->).
  pose proof (tc_detach_nodes_fst_is_prefix tcs sub).
  eauto.
Qed.

Corollary tc_detach_nodes_snd_find_unify [tcs tc]
  (Hnodup : tr_NoDupId tc)
  [t res] (E : trs_find_node t (snd (tc_detach_nodes tcs tc)) = Some res) :
  base.fmap tr_rootinfo (tr_getnode t tc) = Some (tr_rootinfo res).
Proof.
  apply trs_find_has_id in E.
  destruct E as (Hin & <-).
  pose proof (tc_detach_nodes_snd_is_subprefix tcs tc) as Hsnd2pf.
  rewrite -> List.Forall_forall in Hsnd2pf.
  specialize (Hsnd2pf _ Hin).
  destruct Hsnd2pf as (sub & Hin_sub & E).
  rewrite (prefixtr_rootid_same E).
  rewrite id_nodup_find_self_subtr; auto.
  now rewrite (prefixtr_rootinfo_same E).
Qed.

Corollary tc_detach_nodes_fst_rootinfo_same tcs tc : 
  tr_rootinfo (fst (tc_detach_nodes tcs tc)) = tr_rootinfo tc.
Proof. erewrite prefixtr_rootinfo_same; eauto using tc_detach_nodes_fst_is_prefix. Qed.

Corollary tc_detach_nodes_fst_rootid_same tcs tc : 
  tr_rootid (fst (tc_detach_nodes tcs tc)) = tr_rootid tc.
Proof. erewrite prefixtr_rootid_same; eauto using tc_detach_nodes_fst_is_prefix. Qed.

Lemma tc_detach_nodes_tcs_app_fst tcs1 tcs2 tc :
  fst (tc_detach_nodes (tcs1 ++ tcs2) tc) =
  fst (tc_detach_nodes tcs2 (fst (tc_detach_nodes tcs1 tc))).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs1) as (new_chn1 & res1 & res1' & new_chn1' & _ & _ & Enew_chn1 & Eres1 & Eres1' & Enew_chn1' & Edetach1).
  pose proof (tc_detach_nodes_eta ni chn (tcs1 ++ tcs2)) as (new_chn & res & res' & new_chn' & _ & _ & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach1, Edetach.
  cbn delta [fst] beta iota.
  pose proof (tc_detach_nodes_eta ni new_chn1' tcs2) as (new_chn2 & res2 & res2' & new_chn2' & _ & _ & Enew_chn2 & Eres2 & Eres2' & Enew_chn2' & Edetach2).
  rewrite Edetach2.
  simpl; f_equal.
  subst.
  rewrite (map_ext_Forall _ _ IH).
  (* do some algebraic reasoning *)
  rewrite ! map_filter_comm, ! map_map.
  f_equal.
  rewrite filter_filter.
  apply filter_ext.
  intros ?.
  rewrite trs_find_node_isSome_app, ! tc_detach_nodes_fst_rootid_same.
  now destruct (trs_find_node _ tcs1), (trs_find_node _ tcs2).
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
  subst res res' new_chn.
  apply Permutation_Forall_flat_map in IH.
  rewrite <- flat_map_concat_map, -> IH, -> ! Permutation_flat_map_innerapp_split.
  subst.
  (* applying these rewritings is not systematic, but just heuristics ... enlightened by some simplification ... *)
  rewrite ? flat_map_concat_map, ? map_app, ? concat_app, ? flat_map_app, <- ? app_assoc.
  rewrite ! map_filter_comm, ! filter_filter.
  (* this is nightmare! use induction to avoid much repetition *)
  clear.
  induction chn as [ | ch chn IH ]; auto.
  simpl.
  rewrite ! tc_detach_nodes_fst_rootid_same, ! trs_find_node_isSome_app, 
    ! map_app, ! concat_app, ? flat_map_concat_map.
  (* exploit the decidability *)
  assert (forall y (x : treeclock) l, count_occ tr_eqdec (x :: l) y = 
    count_occ tr_eqdec (x :: nil) y + count_occ tr_eqdec l y) as Htmp
    by (intros; change (x :: l) with ((x :: nil) ++ l); now rewrite ! count_occ_app).
  destruct (trs_find_node (tr_rootid ch) tcs1), (trs_find_node (tr_rootid ch) tcs2); simpl.
  all: rewrite ? tc_detach_nodes_tcs_app_fst.
  all: rewrite (Permutation_count_occ tr_eqdec) in IH |- *.
  all: intros x; specialize (IH x).
  all: rewrite ! count_occ_app in IH; rewrite ! count_occ_app.
  all: try rewrite ? Htmp with (l:=map _ _).
  all: try rewrite ? Htmp with (l:=_ ++ _).
  all: rewrite ? count_occ_app; lia.
Qed.

(* a niche case *)
Fact tc_detach_nodes_prepend_child ni ch chn tcs 
  (H : trs_find_node (tr_rootid ch) tcs = None) :
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
  replace pivot_ch with (fst (tc_detach_nodes tcs ch)) by now rewrite Ech.
  rewrite ! tc_detach_nodes_fst_rootid_same, Ech, H.
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
  apply Permutation_Forall_flat_map in IH.
  rewrite ! flat_map_map, Permutation_flat_map_innerapp_split in IH.
  rewrite IH, flat_map_app, ! map_app.
  (* merge the two parts splitted by "partition" *)
  etransitivity.
  2: apply Permutation_app_head, Permutation_app_swap.
  rewrite Permutation_app_swap_app, app_assoc.
  etransitivity.
  2: apply Permutation_app_tail; rewrite <- map_app, <- flat_map_app; 
    apply Permutation_map, Permutation_flat_map.
  2: etransitivity; [ apply Permutation_partition | ]; rewrite Epar; reflexivity.
  subst; apply Permutation_app.
  - now rewrite ! flat_map_concat_map, ! map_map.
  - now rewrite <- flat_map_concat_map, flat_map_flat_map.
Qed.

Corollary tc_detach_nodes_intact_pre tcs tc :
  snd (tc_detach_nodes tcs tc) = nil -> fst (tc_detach_nodes tcs tc) = tc.
Proof.
  (* analytic without induction *)
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
    etransitivity; [ | apply tc_detach_nodes_intact_pre ].
    all: rewrite E; reflexivity.
  - pose proof (tc_detach_nodes_dom_incl tcs tc) as Htmp.
    pose proof (tc_detach_nodes_snd2fst_pre tcs tc) as Htmp2.
    rewrite E in Htmp, Htmp2.
    simpl in Htmp, Htmp2.
    apply Forall_cons_iff, proj1 in Htmp, Htmp2.
    rewrite <- trs_find_in_iff in Htmp.
    destruct Htmp2 as (sub & Hin%(in_map tr_rootid) & ->).
    rewrite tc_detach_nodes_fst_rootid_same in Htmp.
    firstorder.
Qed.

Corollary tc_detach_nodes_dom_partition' tcs tc :
  Permutation (map tr_rootinfo (tr_flatten tc))
    (map tr_rootinfo (tr_flatten (fst (tc_detach_nodes tcs tc))) ++ 
      map tr_rootinfo (snd (tc_detach_nodes tcs tc)) ++ 
      map tr_rootinfo (flat_map tr_flatten (flat_map tr_rootchn (snd (tc_detach_nodes tcs tc))))).
Proof.
  now rewrite tc_detach_nodes_dom_partition, -> map_app, 1 tr_flatten_root_chn_split, ! map_app.
Qed.

Corollary tc_detach_nodes_tid_nodup tcs tc (Hnodup : tr_NoDupId tc) :
  trs_NoDupId (snd (tc_detach_nodes tcs tc)) /\
  (forall t, 
    In t (map tr_rootid (tr_flatten (fst (tc_detach_nodes tcs tc)))) ->
    In t (map tr_rootid (flat_map tr_flatten (snd (tc_detach_nodes tcs tc)))) -> False) /\
  tr_NoDupId (fst (tc_detach_nodes tcs tc)).
Proof.
  pose proof (tc_detach_nodes_dom_partition tcs tc) as Hperm%Permutation_rootinfo2rootid.
  pose proof (Permutation_NoDup Hperm Hnodup) as Htmp.
  now rewrite map_app, NoDup_app_ in Htmp.
Qed.

(* there will not be any tid in tcs that is also inside the pivot tree *)

Lemma tc_detach_nodes_dom_excl tcs tc :
  forall t (Htarg : isSome (trs_find_node t tcs) = true),
  ~ In t (map tr_rootid (flat_map tr_flatten (tr_rootchn (fst (tc_detach_nodes tcs tc))))).
Proof.
  induction tc as [ni chn IH] using tree_ind_2'; intros.
  pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & forest & forest' & new_chn' & _ & _ & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  subst new_chn' new_chn.
  rewrite Edetach.
  simpl.
  intros (sub & <- & (? & ((ch & <- & Hin)%in_map_iff & Hb%negb_true_iff)%filter_In & Hsub)%in_flat_map)%in_map_iff.
  rewrite tc_detach_nodes_fst_rootid_same in Hb.
  eapply IH; eauto.
  rewrite (tree_recons (fst _)), tc_detach_nodes_fst_rootinfo_same in Hsub.
  simpl in Hsub.
  destruct Hsub as [ <- | ].
  - unfold tr_rootid in *.
    simpl in Htarg; congruence.
  - now apply in_map.
Qed.

Corollary tc_detach_nodes_dom_excl_snd tcs tc t (Htarg : isSome (trs_find_node t tcs) = true) :
  ~ In t (map tr_rootid (flat_map tr_flatten (flat_map tr_rootchn (snd (tc_detach_nodes tcs tc))))).
Proof.
  intros (ch & (sub & Hpick & Hin_ch)%in_flat_map & Hin_sub)%map_flat_map_In.
  pose proof (tc_detach_nodes_snd2fst tcs tc) as Htmp.
  rewrite -> List.Forall_forall in Htmp.
  specialize (Htmp _ Hpick).
  destruct Htmp as (sub' & Hin_sub' & ->).
  eapply tc_detach_nodes_dom_excl; [ apply Htarg | ].
  eapply map_flat_map_In_conv; eauto.
Qed.

Corollary tc_detach_nodes_dom_incl_iff tcs tc 
  (* FIXME: the "Hnotin" may not be compatible with the monotone copy operation. consider move this constraint in the future *)
  (Hnotin : trs_find_node (tr_rootid tc) tcs = None) :
  forall ni,
    In ni (filter (fun ni => isSome (trs_find_node (info_id ni) tcs)) (map tr_rootinfo (tr_flatten tc))) <->
    In ni (map tr_rootinfo (snd (tc_detach_nodes tcs tc))).
Proof.
  (* purely analytic proof *)
  intros.
  pose proof (tc_detach_nodes_dom_partition' tcs tc) as Hperm.
  pose proof (Permutation_in_mutual Hperm) as Hinin.
  do 2 setoid_rewrite in_app_iff in Hinin.
  split.
  - intros (Hin%Hinin & Hb)%filter_In.
    destruct Hin as [ Hin | [ Hin | Hin ] ].
    + rewrite (tree_recons (fst _)) in Hin.
      simpl in Hin.
      rewrite tc_detach_nodes_fst_rootinfo_same in Hin.
      destruct Hin as [ <- | Hin ].
      * now setoid_rewrite Hnotin in Hb.
      * apply tc_detach_nodes_dom_excl with (tc:=tc) in Hb.
        apply (in_map info_tid) in Hin.
        now rewrite map_map in Hin.
    + assumption.
    + apply tc_detach_nodes_dom_excl_snd with (tc:=tc) in Hb.
      apply (in_map info_id) in Hin.
      now rewrite map_map in Hin.
  - intros H.
    apply filter_In.
    split; [ firstorder | ].
    apply in_map_iff in H.
    destruct H as (sub & <- & H).
    revert sub H.
    apply Forall_forall, tc_detach_nodes_dom_incl.
Qed.

(* a critical partitioning result *)

Corollary tc_detach_nodes_dom_partition'' tcs tc (Hnotin : trs_find_node (tr_rootid tc) tcs = None) 
  (Hnodup : tr_NoDupId tc) :
  Permutation
    (map tr_rootinfo (tr_flatten (fst (tc_detach_nodes tcs tc))) ++
     map tr_rootinfo (flat_map tr_flatten (flat_map tr_rootchn (snd (tc_detach_nodes tcs tc)))))
    (map tr_rootinfo (filter (fun sub => negb (isSome (trs_find_node (tr_rootid sub) tcs))) (tr_flatten tc))) /\
  Permutation
    (map tr_rootinfo (snd (tc_detach_nodes tcs tc)))
    (map tr_rootinfo (filter (fun sub => isSome (trs_find_node (tr_rootid sub) tcs)) (tr_flatten tc))).
Proof.
  pose proof (tc_detach_nodes_dom_partition' tcs tc) as Hperm.
  rewrite Permutation_app_swap_app in Hperm.
  pose proof (Permutation_split_combine (fun sub => isSome (trs_find_node (tr_rootid sub) tcs)) (tr_flatten tc)) as Hperm_par%(Permutation_map tr_rootinfo).
  rewrite map_app in Hperm_par.
  apply base.and_wlog_l.
  - intros H.
    rewrite Hperm_par, H in Hperm.
    apply Permutation_app_inv_l in Hperm.
    now rewrite Hperm.
  - apply id_nodup_rootinfo_nodup in Hnodup.
    apply Permutation_NoDup, NoDup_app_ in Hperm, Hperm_par; try assumption.
    apply NoDup_Permutation; try tauto.
    intros.
    rewrite <- tc_detach_nodes_dom_incl_iff; try assumption.
    now rewrite map_filter_comm.
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
  pose proof (tc_detach_nodes_snd_is_subprefix tcs tc) as Hto.
  revert Hto.
  apply Forall_impl.
  intros ? (sub & Hsub & Hpf).
  eapply tc_shape_inv_prefix_preserve, Foralltr_subtr; eauto.
  now apply tc_shape_inv_sub.
Qed.

Corollary tc_respect_tc_detach_nodes_snd [tc tc_larger]
  (Hrespect : tc_respect tc tc_larger) tcs :
  Forall (fun tc' => tc_respect tc' tc_larger) (snd (tc_detach_nodes tcs tc)).
Proof.
  pose proof (tc_detach_nodes_snd_is_subprefix tcs tc) as Hto.
  revert Hto.
  apply Forall_impl.
  intros ? (sub & Hsub & Hpf).
  apply (tc_respect_prefix_preserve Hpf). 
  pattern sub.
  eapply Foralltr_subtr; eauto.
  now apply tc_respect_sub.
Qed.

Lemma tc_detach_nodes_forest_recombine_pre [tcs tc]
  (Hnodup : tr_NoDupId tc) (Hnodup' : trs_roots_NoDupId tcs) :
  Permutation
    (map Some (snd (tc_detach_nodes tcs tc)))
    (filter (@isSome _) (map
      (fun t => trs_find_node t (snd (tc_detach_nodes tcs tc))) 
        (map tr_rootid tcs))).
Proof.
  apply trs_find_rearrangement.
  - pose proof (tc_detach_nodes_tid_nodup tcs tc Hnodup) as Hnodup_forest.
    now apply proj1, id_nodup_root_chn_split, proj1 in Hnodup_forest.
  - assumption.
  - (* use dom incl *)
    hnf.
    intros t (sub & <- & Hin)%in_map_iff.
    apply trs_find_in_iff.
    revert sub Hin.
    apply Forall_forall, tc_detach_nodes_dom_incl.
Qed.

(* simulation *)

Lemma forest_chn_recombine [tcs l]
  (Hperm : Permutation (map Some tcs) 
    (filter (@isSome _) (map (fun t => trs_find_node t tcs) l))) :
  Permutation (flat_map tr_rootchn tcs)
    (flat_map (fun t => match trs_find_node t tcs with
      | Some res => tr_rootchn res
      | None => nil
      end) l).
Proof.
  pose (f:=fun ot : option treeclock => match ot with Some tc => tr_rootchn tc | None => nil end).
  apply Permutation_flat_map with (g:=f) in Hperm.
  etransitivity; [ | etransitivity ].
  2: apply Hperm.
  - clear -thread_eqdec tcs.
    induction tcs as [ | tc tcs IH ].
    1: reflexivity.
    simpl.
    now rewrite IH.
  - clear -thread_eqdec l.
    induction l as [ | x l IH ].
    1: reflexivity.
    simpl.
    destruct (trs_find_node x tcs) eqn:E; simpl.
    + now rewrite IH.
    + assumption.
Qed.

Corollary tc_detach_nodes_forest_recombine tcs tc 
  (Hnodup : tr_NoDupId tc) (Hnodup' : trs_roots_NoDupId tcs) :
  Permutation
    (flat_map tr_rootchn (snd (tc_detach_nodes tcs tc)))
    (flat_map
      (fun t : thread =>
      match trs_find_node t (snd (tc_detach_nodes tcs tc)) with
      | Some res => tr_rootchn res
      | None => nil
      end) (map tr_rootid tcs)).
Proof.
  pose proof (tc_detach_nodes_forest_recombine_pre Hnodup Hnodup') as Hperm.
  now apply forest_chn_recombine.
Qed.

End TC_Detach_Nodes.

Section TC_Attach_Nodes.

(* a very special case for the overlay tree *)
(* P can be considered as a function for tracking the right list of trees to be appended *)
(* FIXME: is this a pattern, just like prefix? can we unify them? *)
Inductive simple_overlaytc (P : thread -> list treeclock) : treeclock -> treeclock -> Prop :=
  simple_overlaytc_intro : forall ni chn chn' chn'',
    chn'' = P (info_tid ni) ->
    Forall2 (simple_overlaytc P) chn chn' ->
    simple_overlaytc P (Node ni chn) (Node ni (chn' ++ chn'')).

Fact simple_overlaytc_inv [P ni1 ni2 chn1 chn2]
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

Lemma simple_overlaytc_ind_2 (P : thread -> list treeclock)
  (Q : treeclock -> treeclock -> Prop)
  (Hind : forall (ni : nodeinfo) (chn1 chn2 : list treeclock),
    map tr_rootinfo chn1 = map tr_rootinfo chn2 ->
    Forall2 (simple_overlaytc P) chn1 chn2 -> 
    Forall2 Q chn1 chn2 -> Q (Node ni chn1) (Node ni (chn2 ++ P (info_tid ni))))
  (tr1 tr2 : treeclock) (H : simple_overlaytc P tr1 tr2) : Q tr1 tr2.
Proof.
  revert tr2 H.
  induction tr1 as [ni chn1 IH] using tree_ind_2; intros.
  destruct tr2 as [ni2 chn2].
  apply simple_overlaytc_inv in H.
  destruct H as (chn2_ & chn2_' & -> & -> & -> & Hcorr & Hinfosame).
  eapply Hind; eauto.
  clear -Hcorr IH.
  induction Hcorr.
  1: constructor.
  rewrite Forall_cons_iff in IH.
  constructor; firstorder.
Qed.

Lemma tc_attach_nodes_result forest tc :
  simple_overlaytc (fun t =>
    match trs_find_node t forest with
    | Some res => tr_rootchn res
    | None => nil
    end) tc (tc_attach_nodes forest tc).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using tree_ind_2; intros.
  simpl.
  constructor.
  - auto.
  - now apply Forall2_swap, Forall2_mapself_l.
Qed.

Fact simple_overlaytc_rootinfo_same [P tc tc']
  (Hoverlay : simple_overlaytc P tc tc') : tr_rootinfo tc' = tr_rootinfo tc.
Proof. destruct tc, tc', (simple_overlaytc_inv Hoverlay) as (? & ? & ?). simpl. intuition. Qed.

Fact tc_attach_nodes_rootinfo_same forest tc : 
  tr_rootinfo (tc_attach_nodes forest tc) = tr_rootinfo tc.
Proof. now destruct tc. Qed.

Lemma simple_overlaytc_dom_info (P : thread -> list treeclock) [tc tc']
  (Hoverlay : simple_overlaytc P tc tc') :
  Permutation ((map tr_rootinfo (tr_flatten tc ++
      flat_map tr_flatten (flat_map P (map tr_rootid (tr_flatten tc))))))
    (map tr_rootinfo (tr_flatten tc')).
Proof.
  induction Hoverlay as [ ni chn1 chn2 Hinfosame Hcorr IH ] using simple_overlaytc_ind_2.
  simpl.
  constructor.
  rewrite -> ! flat_map_app, -> ! map_app.
  apply Permutation_Forall2_flat_map in IH.
  rewrite ! flat_map_map, Permutation_flat_map_innerapp_split, map_app in IH.
  rewrite <- IH, <- app_assoc.
  apply Permutation_app_head.
  rewrite Permutation_app_comm.
  apply Permutation_app_tail.
  (* using induction to make things easier *)
  clear.
  induction chn1; simpl; auto.
  repeat (rewrite map_app + rewrite flat_map_app).
  now rewrite IHchn1.
Qed.

Corollary tc_attach_nodes_dom_info [subtree_tc' tc]
  (* these two conditions are required the trees of the forest appear at most once in the result *)
  (* we have to use "subtree_tc'" here, since "tc_attach_nodes" works on a tree *)
  (Hnodup : tr_NoDupId tc) (Hnodup' : tr_NoDupId subtree_tc') :
  Permutation (map tr_rootinfo (tr_flatten (tc_attach_nodes (snd (tc_detach_nodes (tr_flatten subtree_tc') tc)) subtree_tc')))
  ((map tr_rootinfo (tr_flatten subtree_tc')) ++
    (map tr_rootinfo (flat_map tr_flatten (flat_map tr_rootchn (snd (tc_detach_nodes (tr_flatten subtree_tc') tc)))))).
Proof.
  pose proof (tc_attach_nodes_result (snd (tc_detach_nodes (tr_flatten subtree_tc') tc)) subtree_tc') as Hso.
  apply simple_overlaytc_dom_info in Hso.
  rewrite map_app in Hso.
  rewrite <- Hso.
  apply Permutation_app_head, Permutation_map, Permutation_flat_map.
  symmetry.
  now apply tc_detach_nodes_forest_recombine.
Qed.

(* this is not needed for proving "tc_attach_detached_nodes_tid_nodup", which is easier to prove directly. for now, just keep this *)
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
  (* Q: retrieves the clock of a given thread *)
  (Hcomple : forall t, exists aclk, tc_shape_inv (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hshape : tc_shape_inv tc)
  (* needed for aclk upperbound *)
  (Hclk_lt : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  (* needed for aclk sorted *)
  (Haclk_lt : Foralltr (fun tc' =>
    Forall (fun tc0 => Q (tr_rootid tc') <= tc_rootaclk tc0) (tr_rootchn tc')) tc) 
  tc' (Hoverlay : simple_overlaytc P tc tc') :
  Foralltr tc_chn_aclk_ub tc' /\ Foralltr tc_chn_aclk_decsorted tc'.
Proof.
  induction Hoverlay as [ ni chn1 chn2 Hinfosame Hcorr IH ] using simple_overlaytc_ind_2.
  apply Foralltr_and.
  constructor.
  - (* various preparations ... *)
    destruct (Hcomple (info_tid ni)) as (aclk & (Ha & Hb%Foralltr_self & Hc%Foralltr_self)%tc_shape_inv_conj_iff).
    apply Foralltr_self in Hclk_lt.
    simpl in Hclk_lt.
    apply (f_equal (map info_aclk)) in Hinfosame.
    rewrite 2 map_map in Hinfosame.
    fold (tc_rootaclk) in Hinfosame.
    split; hnf; simpl.
    1: apply aclk_upperbound in Hshape.
    2: apply aclk_decsorted in Hshape.
    all: apply Foralltr_self in Hshape; hnf in Hshape, Hb, Hc; simpl in Hshape, Hb, Hc.
    + apply Forall_app; split.
      * rewrite <- Forall_map with (f:=tc_rootaclk) (P:=fun n => n <= info_clk ni) in Hshape |- *.
        congruence.
      * revert Hb.
        apply Forall_impl; intros. 
        etransitivity; eauto.
    + rewrite map_app.
      apply StronglySorted_app; auto.
      * congruence.
      * (* there is a bar: all aclk in prefix >= bar, and all aclk in suffix <= bar *)
        apply Foralltr_self in Haclk_lt.
        simpl in Haclk_lt.
        rewrite <- Forall_map with (f:=tc_rootaclk) (P:=fun n => Q (info_id ni) <= n), -> Hinfosame, -> Forall_forall in Haclk_lt.
        rewrite <- Forall_map with (f:=tc_rootaclk) (P:=fun n => n <= Q (info_tid ni)), -> Forall_forall in Hb.
        intros x y Hx Hy.
        specialize (Haclk_lt _ Hx); specialize (Hb _ Hy).
        change info_id with info_tid in Haclk_lt. (* TODO this is bad! *)
        lia.
  - erewrite list.Forall_iff with (Q:=fun x => _ x /\ _ x).
    2: intros; rewrite Foralltr_and at 1; reflexivity.
    apply Forall_app; split.
    + (* using IH structurally *)
      (* FIXME: from the proofs below, this seems like pretty much a proof pattern! *)
      eapply list.Forall2_Forall_r.
      1: apply IH.
      apply tc_shape_inv_chn in Hshape.
      apply Foralltr_chn in Hclk_lt, Haclk_lt.
      pose proof (Forall_and (Forall_and Hshape Hclk_lt) Haclk_lt) as HH.
      simpl in HH.
      revert HH; apply Forall_impl.
      intuition.
    + destruct (Hcomple (info_tid ni)) as (aclk & (_ & Hb%Foralltr_chn & Hc%Foralltr_chn)%tc_shape_inv_conj_iff).
      now apply Forall_and.
Qed.

(* if pf respects some tree, then the result of attach should also respect that tree *)
(* later, will use "tc_shape_inv_prepend_child" in combination *)

Lemma tc_ge_with_subdmono_simple_overlaytc (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hdmono_sub : forall t, exists aclk, Foralltr (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hge : tc_ge tc_larger tc)
  (* needed for using dmono on (P t) *)
  (Hclk_le : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  tc' (Hoverlay : simple_overlaytc P tc tc') :
  tc_ge tc_larger tc'.
Proof.
  induction Hoverlay as [ ni chn1 chn2 Hinfosame Hcorr IH ] using simple_overlaytc_ind_2.
  constructor.
  - now apply Foralltr_self in Hge.
  - apply Forall_app; split.
    + eapply list.Forall2_Forall_r.
      1: apply IH.
      apply Foralltr_chn in Hge, Hclk_le.
      pose proof (Forall_and Hge Hclk_le) as HH.
      simpl in HH.
      revert HH; apply Forall_impl.
      intuition.
    + apply Foralltr_self in Hge, Hclk_le.
      simpl in Hge, Hclk_le.
      pose proof (Hdmono_sub (info_tid ni)) as (aclk & HH%Foralltr_self).
      hnf in HH.
      specialize (HH (Nat.le_trans _ _ _ Hclk_le Hge)).
      now apply Foralltr_chn in HH.
Qed.

Corollary dmono_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hdmono_sub : forall t, exists aclk, Foralltr (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hdmono : Foralltr (dmono_single tc_larger) tc)
  (* needed for using dmono on (P t) *)
  (Hclk_le : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  tc' (Hoverlay : simple_overlaytc P tc tc') :
  Foralltr (dmono_single tc_larger) tc'.
Proof.
  induction Hoverlay as [ ni chn1 chn2 Hinfosame Hcorr IH ] using simple_overlaytc_ind_2.
  constructor.
  - intros Hle.
    eapply tc_ge_with_subdmono_simple_overlaytc; eauto.
    + apply Foralltr_self in Hdmono.
      simpl in Hle.
      now apply Hdmono.
    + now constructor.
  - apply Forall_app; split.
    + eapply list.Forall2_Forall_r.
      1: apply IH.
      apply Foralltr_chn in Hdmono, Hclk_le.
      pose proof (Forall_and Hdmono Hclk_le) as HH.
      simpl in HH.
      revert HH; apply Forall_impl.
      intuition.
    + now pose proof (Hdmono_sub (info_tid ni)) as (aclk & HH%Foralltr_chn).
Qed.

Lemma imono_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hdmono_sub : forall t, exists aclk, Foralltr (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  (Himono_sub : forall t, exists aclk, Foralltr (imono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Himono : Foralltr (imono_single tc_larger) tc)
  (Hclk_le : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  tc' (Hoverlay : simple_overlaytc P tc tc') :
  Foralltr (imono_single tc_larger) tc'.
Proof.
  induction Hoverlay as [ ni chn1 chn2 Hinfosame Hcorr IH ] using simple_overlaytc_ind_2.
  (* FIXME: this seems to require a dependent version of "Foralltr_Forall_chn_comm". how to achieve that? *)
  rewrite Foralltr_cons_iff in Himono, Hclk_le |- *.
  unfold imono_single in Himono |- * at 1.
  rewrite <- list.Forall_and in Himono |- *.
  simpl in Himono |- *.
  apply Forall_app; split.
  - (* this is slightly different proof route, compared with above *)
    eapply list.Forall2_Forall_r.
    1: apply Forall2_and; split; [ apply IH | apply Hcorr ].
    pose proof (Forall_and Himono (proj2 Hclk_le)) as HH.
    simpl in HH.
    revert HH; apply Forall_impl.
    intuition.
    eapply tc_ge_with_subdmono_simple_overlaytc; eauto.
    match goal with HH : simple_overlaytc _ ?a ?b |- _ => 
      enough (tc_rootaclk a = tc_rootaclk b) as Htmp by (rewrite Htmp in *; intuition); 
      unfold tc_rootaclk; 
      now rewrite (simple_overlaytc_rootinfo_same HH) end.
  - pose proof (Himono_sub (info_tid ni)) as (aclk & HH%Foralltr_cons_iff).
    now apply list.Forall_and.
Qed.

Corollary tc_respect_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hrespect_sub : forall t, exists aclk, tc_respect (Node (mkInfo t (Q t) aclk) (P t)) tc_larger)
  tc (Hrespect : tc_respect tc tc_larger)
  (Hclk_le : Foralltr (fun tc' => Q (tr_rootid tc') <= tc_rootclk tc') tc)
  tc' (Hoverlay : simple_overlaytc P tc tc') :
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

Lemma tc_attach_detached_nodes_id_nodup tc tc'
  (Hnodup : tr_NoDupId tc) (Hnodup' : tr_NoDupId tc') :
  tr_NoDupId (tc_attach_nodes (snd (tc_detach_nodes (tr_flatten tc') tc)) tc').
Proof.
  pose proof (tc_attach_nodes_dom_info Hnodup Hnodup') as Hperm.
  rewrite <- map_app in Hperm.
  apply Permutation_rootinfo2rootid in Hperm.
  eapply Permutation_NoDup. 
  1: symmetry; apply Hperm. 
  rewrite -> map_app.
  apply NoDup_app_.
  split; [ assumption | split ].
  2: apply id_nodup_root_chn_split, tc_detach_nodes_tid_nodup; assumption.
  (* use domain exclusion *)
  intros ??.
  now apply tc_detach_nodes_dom_excl_snd, trs_find_in_iff.
Qed.

(* now, put everything together *)

Local Tactic Notation "saturate" constr(tc) constr(tc') ident(Hso) hyp(Hshape') hyp(Hrespect) hyp(Hroot_clk_lt) :=
  match goal with |- context[tc_attach_nodes ?tcs ?tc] =>
    pose proof (tc_attach_nodes_result tcs tc) as Hso end;
  remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix;
  destruct (tc_detach_nodes (tr_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach;
  simpl in Hso |- *;
  pose proof (tc_get_updated_nodes_join_shape Hshape' Hrespect) as Hsq;
  pose proof (tc_get_updated_nodes_join_shape' Hshape' Hrespect Hroot_clk_lt) as Hsq';
  pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix;
  rewrite <- Eprefix in Hprefix, Hsq;
  pose proof (tc_shape_inv_prefix_preserve Hprefix Hshape') as Hshape_pf;
  assert (forest = snd (tc_detach_nodes (tr_flatten prefix_tc') tc)) as Eforest by now rewrite -> Edetach.

Lemma tc_attach_nodes_tc_shape_inv [tc tc']
  (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc') 
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc')
  (Hrespect : tc_respect tc' tc) :
  tc_shape_inv (tc_attach_nodes 
    (snd (tc_detach_nodes (tr_flatten (tc_get_updated_nodes_join tc tc')) tc)) 
    (tc_get_updated_nodes_join tc tc')).
Proof.
  saturate tc tc' Hso Hshape' Hrespect Hroot_clk_le.
  apply tc_shape_inv_conj_iff.
  split.
  - subst.
    apply tc_attach_detached_nodes_id_nodup.
    all: now apply tid_nodup.
  - eapply tc_shape_inv_simple_overlaytc_pre with (Q:=fun t => tc_getclk t tc); eauto.
    + intros t.
      simpl.
      destruct (trs_find_node t forest) as [ res | ] eqn:E.
      2: exists 0; now apply tc_shape_inv_nil.
      pose proof E as (Hin & <-)%trs_find_has_id.
      subst forest.
      (* do unify *)
      apply tc_detach_nodes_snd_find_unify in E.
      2: now apply tid_nodup.
      exists (tc_rootaclk res).
      pose proof (tc_shape_inv_tc_detach_nodes_snd (tr_flatten prefix_tc') tc Hshape) as Hshape_forest.
      enough (tc_shape_inv res) as HH.
      2: clear E; revert res Hin; now apply Forall_forall.
      rewrite tc_getclk_as_fmap.
      change tc_rootclk with (Basics.compose info_clk tr_rootinfo).
      rewrite option.option_fmap_compose, E.
      destruct res as [(?, ?, ?) ?]; simpl in *; auto.
    + subst prefix_tc'.
      revert Hsq'.
      apply Foralltr_impl; lia.
    + (* basically repeating the proof of "tc_get_updated_nodes_join_shape'" *)
      eapply Foralltr_impl.
      2: apply Hsq.
      intros ?.
      apply Forall_impl.
      lia.
Qed.

Lemma tc_attach_nodes_respect [tc tc']
  (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc') 
  (Hroot_clk_le : tc_getclk (tr_rootid tc') tc < tc_rootclk tc')
  (Hrespect : tc_respect tc' tc) tc_larger 
    (Hrespect1 : tc_respect tc tc_larger)
    (Hrespect2 : tc_respect tc' tc_larger) :
  tc_respect (tc_attach_nodes 
    (snd (tc_detach_nodes (tr_flatten (tc_get_updated_nodes_join tc tc')) tc)) 
    (tc_get_updated_nodes_join tc tc')) tc_larger.
Proof.
  saturate tc tc' Hso Hshape' Hrespect Hroot_clk_le.
  revert Hso.
  apply tc_respect_simple_overlaytc_pre with (Q:=fun t => tc_getclk t tc).
  - intros t.
    destruct (trs_find_node t forest) as [ res | ] eqn:E.
    2: exists 0; now apply tc_respect_nochn_trivial.
    pose proof E as (Hin & <-)%trs_find_has_id.
    subst forest.
    (* do unify *)
    (* FIXME: proof repeating ... any good way to work around? *)
    apply tc_detach_nodes_snd_find_unify in E.
    2: now apply tid_nodup.
    exists (tc_rootaclk res).
    pose proof (tc_respect_tc_detach_nodes_snd Hrespect1 (tr_flatten prefix_tc')) as Hshape_forest.
    enough (tc_respect res tc_larger) as HH.
    2: clear E; revert res Hin; now apply Forall_forall.
    rewrite tc_getclk_as_fmap.
    change tc_rootclk with (Basics.compose info_clk tr_rootinfo).
    rewrite option.option_fmap_compose, E.
    destruct res as [(?, ?, ?) ?]; simpl in *; auto.
  - eapply tc_respect_prefix_preserve; eauto.
  - subst prefix_tc'.
    revert Hsq'.
    apply Foralltr_impl; lia.
Qed.

(* should also be "tcs_congr", but keep the word "forest" anyway *)
Lemma tc_attach_nodes_forest_congr forest1 forest2 tc
  (H : Foralltr (fun tc' => trs_find_node (tr_rootid tc') forest1 = 
    trs_find_node (tr_rootid tc') forest2) tc) :
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
  change info_tid with info_id. (* TODO this is bad! *)
  now rewrite Hroot.
Qed.

Corollary tc_attach_nodes_forest_cleanhd forest1 sub tc
  (Hnotin : ~ In (tr_rootid sub) (map tr_rootid (tr_flatten tc))) :
  tc_attach_nodes forest1 tc = tc_attach_nodes (sub :: forest1) tc.
Proof.
  apply tc_attach_nodes_forest_congr, Foralltr_Forall_subtree, Forall_forall.
  intros sub' Hin.
  simpl.
  unfold has_same_id.
  rewrite eqdec_must_right; auto.
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
  remember (match trs_find_node (info_tid ni) forest with Some u => tr_rootchn u | None => nil end) as old_chn eqn:Eold_chn.
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
    rewrite -> has_same_id_true in HH.
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
    erewrite -> tr_rootinfo_has_same_id_congr with (x:=(fst (tc_detach_nodes (nd :: nil) tc'))).
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
    (match trs_find_node (tr_rootid tc') forest with 
      | Some u => u | None => Node (mkInfo (tr_rootid tc') 0%nat 0%nat) nil end)) (tr_flatten tc))).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  simpl.
  remember (match trs_find_node (info_tid ni) forest with Some u => tr_rootchn u | None => nil end) as old_chn eqn:Eold_chn.
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
    rewrite -> has_same_id_true in HH.
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

  change info_id with info_tid.
  destruct (trs_find_node (info_tid ni) forest) as [ [ ni' chn' ] | ] eqn:E.
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
    pose proof (id_nodup_find_self Hnodup_forest) as Htmp.
    rewrite -> Forall_forall in Htmp |- *.
    intros x Hin.
    specialize (Htmp _ Hin).
    now rewrite Htmp.
  }
  etransitivity.
  1: apply Permutation_flat_map, Permutation_map, 
    Permutation_split_combine with (f:=fun tc' => isSome (trs_find_node (tr_rootid tc') forest)).
  rewrite -> map_app, -> flat_map_app.
  match goal with |- _ (?aa ++ ?bb) _ => replace bb with (@nil treeclock) end.
  2:{
    rewrite -> flat_map_concat_map.
    apply eq_sym, concat_nil_Forall, Forall_map, Forall_map, Forall_forall.
    intros x (Hin & HH%negb_true_iff)%filter_In.
    destruct (trs_find_node _ _) eqn:E in |- *.
    1: rewrite E in HH; discriminate.
    rewrite -> tc_detach_nodes_intact; try reflexivity.
    auto.
  }
  rewrite app_nil_r.
  (* ... *)
  pose proof (map_map tr_rootid (fun t => tc_detach_nodes (nd :: nil)
    match trs_find_node t forest with Some u => u | None => Node (mkInfo t 0%nat 0%nat) nil end)) as Htmp.
  simpl in Htmp.
  rewrite <- ! Htmp.
  clear Htmp.
  apply Permutation_flat_map, Permutation_map.
  (* ... have to use map_filter_comm *)
  pose proof (map_filter_comm tr_rootid (fun t => isSome (trs_find_node t forest)) (tr_flatten tc)) as Htmp.
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
  - match goal with |- context[trs_find_node ?a ?b] => destruct (trs_find_node a b) as [ res | ] eqn:Eres end.
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
  cbn delta [tr_rootinfo] zeta iota beta.
  simpl in H.
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
  now rewrite eqdec_must_left in Hroot_clk_le |- *.
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

Section TC_Join_Partial_And_Join.

(* not quite reusable, so make it a tactic instead of a lemma *)
Local Tactic Notation "saturate" constr(tc) constr(tc') hyp(Etc') :=
  destruct (tc_detach_nodes (tr_flatten tc') tc) as (pivot, forest) eqn:Edetach;
  destruct (tc_attach_nodes forest tc') as [ni chn_w] eqn:Eattach;
  pose proof (tc_attach_nodes_rootinfo_same forest tc') as Eni;
  epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Eni_z;
  rewrite -> Eattach in Eni;
  match goal with
  | Eprefix : tc' = tc_get_updated_nodes_join _ _ |- _ =>
    rewrite -> Eprefix, -> (prefixtr_rootinfo_same (tc_get_updated_nodes_join_is_prefix _ _)) in Eni
  | _ => idtac
  end;
  rewrite -> Etc' in Eni;
  rewrite -> Edetach in Eni_z;
  destruct pivot as [ni_z chn_z] eqn:Epivot;
  simpl in Eni, Eni_z;
  subst ni ni_z.

Section TC_Join_Partial.

  (* a direct result; the dom of partial join ~= the dom of pivot + the dom of attach *)
  Lemma tc_join_partial_dom_info tc tc' :
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
    saturate tc tc' Etc'.
    simpl.
    rewrite Eattach, map_app.
    simpl.
    list.solve_Permutation.
  Qed.

  Context [tc tc' : treeclock].
  Hypotheses (Hnodup : tr_NoDupId tc) (Hnodup' : tr_NoDupId tc').

  (* so much manipulation below (e.g., rewrite, change, unfold ...)! *)

  (* a refined result *)
  Lemma tc_join_partial_dom_partial_info :
    Permutation (map tc_rootinfo_partial (tr_flatten (tc_join_partial tc tc')))
      (map tc_rootinfo_partial (tr_flatten (fst (tc_detach_nodes (tr_flatten tc') tc))) ++
        map tc_rootinfo_partial (tr_flatten tc') ++
        map tc_rootinfo_partial (flat_map tr_flatten (flat_map tr_rootchn
                (snd (tc_detach_nodes (tr_flatten tc') tc))))).
  Proof.
    pose proof (tc_join_partial_dom_info tc tc') as Hperm.
    pose proof (tc_attach_nodes_dom_info Hnodup Hnodup') as Hperm'.
    rewrite <- map_app in Hperm, Hperm'.
    apply Permutation_rootinfo2partialinfo in Hperm, Hperm'.
    rewrite Hperm, map_app.
    destruct (tc_attach_nodes _ tc') as [(?, ?, ?) ?].
    now rewrite Hperm', map_app.
  Qed.

  Corollary tc_join_partial_dom_tid :
    Permutation (map tr_rootid (tr_flatten (tc_join_partial tc tc')))
      (map tr_rootid (tr_flatten (fst (tc_detach_nodes (tr_flatten tc') tc))) ++
        map tr_rootid (tr_flatten tc') ++
        map tr_rootid (flat_map tr_flatten (flat_map tr_rootchn
                (snd (tc_detach_nodes (tr_flatten tc') tc))))).
  Proof. rewrite <- ! map_app. apply Permutation_partialinfo2roottid. now rewrite ! map_app, tc_join_partial_dom_partial_info. Qed.

  Hypothesis (Hnotin : ~ In (tr_rootid tc) (map tr_rootid (tr_flatten tc'))).

  Corollary tc_join_partial_dom_partial_info' :
    Permutation (map tc_rootinfo_partial (tr_flatten (tc_join_partial tc tc')))
      (map tc_rootinfo_partial (tr_flatten tc') ++
        map tc_rootinfo_partial (filter (fun sub => 
              negb (isSome (trs_find_node (tr_rootid sub) (tr_flatten tc')))) (tr_flatten tc))).
  Proof.
    rewrite tc_join_partial_dom_partial_info, Permutation_app_swap_app.
    apply Permutation_app_head.
    rewrite <- map_app.
    apply Permutation_rootinfo2partialinfo.
    rewrite -> map_app.
    apply tc_detach_nodes_dom_partition''; try assumption.
    rewrite -> trs_find_in_iff in Hnotin.
    now destruct (trs_find_node _ _).
  Qed.

  Corollary tc_join_partial_id_nodup : tr_NoDupId (tc_join_partial tc tc').
  Proof.
    pose proof tc_join_partial_dom_partial_info' as Hperm.
    rewrite <- map_app in Hperm.
    eapply Permutation_NoDup; [ symmetry; apply Permutation_partialinfo2roottid, Hperm | ].
    rewrite map_app, NoDup_app_.
    (* have to use "map_filter_comm" in the reverse way; FIXME: any better unification approach? *)
    pose proof (map_filter_comm tr_rootid (fun t => negb (isSome (trs_find_node t (tr_flatten tc')))) (tr_flatten tc)) as Htmp.
    simpl in Htmp.
    rewrite <- ! Htmp.
    clear Htmp.
    split; [ assumption | split; [ | now apply NoDup_filter ] ].
    intros t Hin'%trs_find_in_iff (Hin & E)%filter_In.
    now rewrite -> Hin' in E.
  Qed.

  Lemma tc_join_partial_getclk t :
    tc_getclk t (tc_join_partial tc tc') = match tr_getnode t tc' with Some res => tc_rootclk res | None => tc_getclk t tc end.
  Proof.
    pose proof tc_join_partial_dom_partial_info' as Hperm.
    rewrite <- map_app in Hperm.
    pose proof (tc_getclk_perm_congr_pre tc_join_partial_id_nodup Hperm t) as Htmp.
    change (trs_find_node t (tr_flatten (tc_join_partial tc tc'))) with (tr_getnode t (tc_join_partial tc tc')) in Htmp.
    unfold trs_find_node in Htmp at 1.
    rewrite -> find_app in Htmp.
    rewrite -> tc_getclk_as_fmap, -> Htmp.
    fold (tr_getnode t tc').
    destruct (tr_getnode t tc') as [ res | ] eqn:Eres; simpl; auto.
    apply tr_getnode_none in Eres.
    destruct (find _ _) as [ res' | ] eqn:Eres' in |- *; simpl.
    - apply trs_find_has_id in Eres'.
      destruct Eres' as (Hin'%filter_In%proj1 & <-).
      rewrite tc_getclk_as_fmap, id_nodup_find_self_subtr; auto.
    - apply trs_find_none in Eres'.
      (* have to use "map_filter_comm" in the reverse way *)
      pose proof (map_filter_comm tr_rootid (fun t => negb (isSome (trs_find_node t (tr_flatten tc')))) (tr_flatten tc)) as Htmp'.
      simpl in Htmp'.
      rewrite <- Htmp' in Eres'.
      clear Htmp.
      rewrite filter_In, negb_true_iff, <- not_true_iff_false, <- trs_find_in_iff in Eres'.
      unfold tc_getclk.
      destruct (tr_getnode t tc) as [ res'' | ] eqn:Eres''; auto.
      apply tr_getnode_some in Eres''.
      intuition.
  Qed.

End TC_Join_Partial.

Section TC_Join.

  Variables (tc tc' : treeclock).
  Hypotheses (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc')
    (Hrespect : tc_respect tc' tc).

  Local Tactic Notation "tc_join_initial_judge" constr(clk_u') constr(u') :=
    destruct (clk_u' <=? tc_getclk u' tc) eqn:Eclk_lt;
    [ apply Nat.leb_le in Eclk_lt; rewrite tc_join_trivial by assumption |
      apply Nat.leb_gt in Eclk_lt; rewrite tc_join_go by assumption ].

  (* this is fundamental! the root of tc will not be updated *)
  Hypothesis (Hroot_clk_le : tc_getclk (tr_rootid tc) tc' <= tc_rootclk tc).

  Lemma tc_join_tc_shape_inv :
    tc_shape_inv (tc_join tc tc').
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    tc_join_initial_judge clk_u' u'; auto.
    unfold tc_join_partial.
    rewrite <- ! Etc' in *.
    remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
    saturate tc prefix_tc' Etc'.
    (* use prepend child *)
    apply tc_shape_inv_prepend_child.
    - pose proof (tc_shape_inv_tc_detach_nodes_fst (tr_flatten prefix_tc') tc Hshape) as H.
      now rewrite -> Edetach in H.
    - apply tc_shape_inv_root_aclk_useless with (aclk:=aclk_u').
      rewrite <- Eattach.
      subst.
      eapply eq_ind_r with (y:=forest) (x:=snd _).
      1: now apply tc_attach_nodes_tc_shape_inv.
      now rewrite Edetach.
    - pose proof (tc_join_partial_id_nodup (tid_nodup Hshape) 
        (id_nodup_prefix_preserve (tc_get_updated_nodes_join_is_prefix _ _) (tid_nodup Hshape')) 
        (tc_get_updated_nodes_root_notin Hshape' Hrespect ltac:(now subst tc') Hroot_clk_le)) as Htmp.
      unfold tc_join_partial in Htmp.
      now rewrite <- Eprefix, -> Edetach, -> Eattach in Htmp.
    - now simpl.
    - destruct chn_z; [ lia | ].
      simpl.
      pose proof (tc_shape_inv_tc_detach_nodes_fst (tr_flatten prefix_tc') tc Hshape) as H.
      apply aclk_upperbound, Foralltr_self in H.
      rewrite -> Edetach in H.
      apply Forall_inv in H.
      simpl in H.
      lia.
  Qed.

  Lemma tc_join_pointwise_max_pre
    (Hroot_clk_lt : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') t :
    tc_getclk t (tc_join tc tc') = Nat.max (tc_getclk t tc) (tc_getclk t tc').
  Proof.
    pose proof (tc_join_go tc tc' Hroot_clk_lt) as ->.
    pose proof (tc_join_partial_getclk (tid_nodup Hshape) 
      (id_nodup_prefix_preserve (tc_get_updated_nodes_join_is_prefix _ _) (tid_nodup Hshape')) 
      (tc_get_updated_nodes_root_notin Hshape' Hrespect Hroot_clk_lt Hroot_clk_le)) as Htmp.
    rewrite -> Htmp.
    destruct (tr_getnode t _) as [ res | ] eqn:Eres.
    - pose proof Eres as Eres'%(f_equal (@isSome _))%tc_get_updated_nodes_join_sound; auto.
      enough (tc_getclk t tc' = tc_rootclk res) by lia.
      pose proof Eres as Eres''%(f_equal (base.fmap tr_rootinfo))
        %(id_nodup_find_prefix (tc_get_updated_nodes_join_is_prefix _ _) (tid_nodup Hshape')).
      rewrite tc_getclk_as_fmap.
      change tc_rootclk with (Basics.compose info_clk tr_rootinfo).
      now rewrite option.option_fmap_compose, Eres''.
    - pose proof Eres as Eres'%(f_equal (@isSome _))%not_true_iff_false.
      rewrite <- tc_get_updated_nodes_join_adequacy in Eres'; auto.
      lia.
  Qed.

  (* this shows that tree clock is indeed a logical clock! *)
  Corollary tc_join_pointwise_max t :
    tc_getclk t (tc_join tc tc') = Nat.max (tc_getclk t tc) (tc_getclk t tc').
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    tc_join_initial_judge clk_u' u'.
    - (* by respect *)
      rewrite <- Etc', -> max_l.
      1: reflexivity.
      apply tc_ge_all_getclk_ge.
      apply dmono, Foralltr_self in Hrespect.
      intuition.
    - rewrite <- tc_join_go; auto.
      rewrite <- Etc' in *.
      apply tc_join_pointwise_max_pre.
      now subst tc'.
  Qed.

  Corollary tc_join_respected tc''
    (Hrespect1 : tc_respect tc'' tc) (Hrespect2 : tc_respect tc'' tc') :
    tc_respect tc'' (tc_join tc tc').
  Proof.
    (* directly by pointwise_max_preserve property *)
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
    tc_join_initial_judge clk_u' u'; try assumption.
    unfold tc_join_partial.
    rewrite <- ! Etc' in *.
    remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
    saturate tc prefix_tc' Etc'.
    (* prepare more *)
    (* FIXME: extract this proof into a lemma like "tc_respect_prepend_child" ... ? *)
    pose proof (tc_detach_nodes_fst_is_prefix (tr_flatten prefix_tc') tc) as Hprefix_pivot.
    rewrite -> Edetach in Hprefix_pivot.
    simpl in Hprefix_pivot.
    pose proof (tc_respect_prefix_preserve Hprefix_pivot Hrespect1) as Hrespect_pivot.
    pose proof (tc_attach_nodes_respect Hshape Hshape' ltac:(now subst tc') Hrespect _ Hrespect1 Hrespect2) as Hrespect_attach.
    rewrite <- Eprefix, -> Edetach in Hrespect_attach.
    simpl in Hrespect_attach.
    rewrite -> Eattach in Hrespect_attach.
    constructor.
    - constructor.
      + (* impossible by assumption *)
        destruct tc as [(?, ?, ?) ?].
        hnf in Hroot_clk_lt' |- *.
        simpl in Hroot_clk_lt' |- *.
        lia.
      + constructor.
        * eapply tc_respect_root_aclk_useless; eauto.
        * now apply dmono, Foralltr_chn in Hrespect_pivot.
    - constructor.
      + hnf.
        destruct tc as [(z, clk_z, aclk_z) chn_z'].
        simpl.
        constructor.
        * (* impossible by assumption *)
          simpl in Hroot_clk_lt' |- *.
          lia.
        * now apply imono, Foralltr_cons_iff, proj1 in Hrespect_pivot.
      + constructor.
        * eapply tc_respect_root_aclk_useless; eauto.
        * now apply imono, Foralltr_chn in Hrespect_pivot.
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
