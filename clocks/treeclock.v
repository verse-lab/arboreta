From Coq Require Import List Bool Lia PeanoNat Sorting RelationClasses Permutation.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.

From arboreta.utils Require Import util.
From arboreta.utils Require Export rosetree.

From stdpp Require list.

Section TreeClock.

(* Sometimes using auto with * is affordable. *)
Local Ltac intuition_solver ::= auto with *.

Local Notation isSome := ssrbool.isSome.

Context {thread : Type} `{thread_eqdec : EqDec thread}.

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

Local Tactic Notation "go" := destruct x as [ [] ], y as [ [] ].

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
  let: u_pre := trs_find_node (info_tid info_u') forest in (* FIXME: maybe change this "info_tid" in the future *)
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
      pose proof (ssrbool.contra_not (Haclk_impl_clk _ (or_introl eq_refl))) as Ecmp_clk_v'_lt.
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

Fact tc_get_updated_nodes_join_trace [tc' tc sub_prefix]
  (H : subtr sub_prefix (tc_get_updated_nodes_join tc tc')) :
  exists sub, subtr sub tc' /\ sub_prefix = tc_get_updated_nodes_join tc sub.
Proof.
  apply subtr_subtr_witness in H.
  destruct H as (l & H).
  revert tc' sub_prefix H.
  induction l as [ | x l IH ]; intros [ (u', clk', aclk') chn']; intros; auto.
  - injection H as <-.
    eexists.
    split; [ apply tr_flatten_self_in | reflexivity ].
  - hnf in H.
    tc_get_updated_nodes_join_unfold in_ H.
    simpl in H.
    pose proof (tc_get_updated_nodes_join_aux_result_submap tc (tc_getclk u' tc) chn') 
      as (chn'' & Hsl & E).
    rewrite E, nth_error_map in H.
    destruct (nth_error chn'' x) as [ ch' | ] eqn:Enth; try discriminate.
    simpl in H.
    destruct (IH _ _ H) as (sub & Hsub & ->).
    exists sub.
    split; [ | reflexivity ].
    apply nth_error_In in Enth.
    eapply subtr_trans; [ eauto | now apply subtr_chn, (sublist_In Hsl) ].
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
  pose proof (fun tc' H => ssrbool.contra_not (Haclk_impl_clk tc' H)) as Haclk_impl_clk'.
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
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn'
    ltac:(assumption) ltac:(assumption)) as Htmp.
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

Corollary tc_detach_nodes_tcs_congr_app tcs1 tcs2 tc :
  tc_detach_nodes (tcs1 ++ tcs2) tc = tc_detach_nodes (tcs2 ++ tcs1) tc.
Proof. apply tc_detach_nodes_tcs_congr. intros. rewrite ! map_app, ! in_app_iff. tauto. Qed.

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
    (* FIXME: will putting the following fst/snd inside the function after map make proof easier? *)
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

Corollary tc_detach_nodes_intact' tcs tc
  (Hdj : forall t, In t (map tr_rootid (tr_flatten tc)) -> 
    In t (map tr_rootid tcs) -> False) :
  tc_detach_nodes tcs tc = (tc, nil).
Proof.
  apply tc_detach_nodes_intact.
  intros t Hin.
  apply Hdj.
  rewrite (tree_recons tc); simpl; tauto.
Qed.

Corollary tc_detach_nodes_dom_partition' tcs tc :
  Permutation (map tr_rootinfo (tr_flatten tc))
    (map tr_rootinfo (tr_flatten (fst (tc_detach_nodes tcs tc))) ++ 
      map tr_rootinfo (snd (tc_detach_nodes tcs tc)) ++ 
      map tr_rootinfo (flat_map tr_flatten (flat_map tr_rootchn (snd (tc_detach_nodes tcs tc))))).
Proof.
  now rewrite tc_detach_nodes_dom_partition, -> map_app, 1 tr_flatten_root_chn_split, ! map_app.
Qed.

Corollary tc_detach_nodes_id_nodup tcs tc (Hnodup : tr_NoDupId tc) :
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

Corollary tc_detach_nodes_forest_recombine [tcs tc]
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
  apply trs_find_rearrangement_flat_map.
  - pose proof (tc_detach_nodes_id_nodup tcs tc Hnodup) as Hnodup_forest.
    now apply proj1, id_nodup_root_chn_split, proj1 in Hnodup_forest.
  - assumption.
  - (* use dom incl *)
    hnf.
    intros t (sub & <- & Hin)%in_map_iff.
    apply trs_find_in_iff.
    revert sub Hin.
    apply Forall_forall, tc_detach_nodes_dom_incl.
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

Fact simple_overlaytc_colocate (P : thread -> list treeclock) [tc tc']
  (Hoverlay : simple_overlaytc P tc tc') :
  forall [l sub] (H : tr_locate tc l = Some sub), 
    base.fmap tr_rootinfo (tr_locate tc' l) = Some (tr_rootinfo sub).
Proof.
  induction Hoverlay as [ ni chn1 chn2 Hinfosame Hcorr IH ] using simple_overlaytc_ind_2; intros.
  destruct l as [ | x l ].
  1: injection H as <-; reflexivity.
  simpl in H.
  destruct (nth_error chn1 x) as [ sub' | ] eqn:E; try discriminate.
  simpl.
  pose proof E as Hlt%nth_error_some_inrange.
  pose proof (list.Forall2_length _ _ _ Hcorr).
  rewrite nth_error_app1 by congruence.
  apply (Forall2_pointwise IH) in E.
  destruct E as (? & -> & HH).
  now apply HH.
Qed.

Corollary tc_attach_nodes_colocate [tc l sub] (H : tr_locate tc l = Some sub) forest : 
  base.fmap tr_rootinfo (tr_locate (tc_attach_nodes forest tc) l) = Some (tr_rootinfo sub).
Proof. erewrite simple_overlaytc_colocate; eauto. now apply tc_attach_nodes_result. Qed.

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

Lemma tc_attach_detached_nodes_id_nodup [tc tc']
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
  2: apply id_nodup_root_chn_split, tc_detach_nodes_id_nodup; assumption.
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
      destruct res as [ [] ]; simpl in *; auto.
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
    destruct res as [ [] ]; simpl in *; auto.
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

Corollary tc_attach_nodes_forest_congr' forest1 forest2 tc
  (Hnodup : trs_roots_NoDupId forest1) (Hperm : Permutation forest1 forest2) :
  tc_attach_nodes forest1 tc = tc_attach_nodes forest2 tc.
Proof.
  apply tc_attach_nodes_forest_congr, Foralltr_trivial.
  intros ?.
  set (tr_rootid tr) as t; clearbody t; clear tr.
  rewrite <- (option.option_fmap_id (trs_find_node t forest1)), <- (option.option_fmap_id (trs_find_node t forest2)).
  eapply id_nodup_find_congr_fmap; eauto.
  now rewrite ! map_id_eq.
Qed.

Corollary tc_attach_nodes_forest_cleanhd forest1 sub tc
  (Hnotin : ~ In (tr_rootid sub) (map tr_rootid (tr_flatten tc))) :
  tc_attach_nodes (sub :: forest1) tc = tc_attach_nodes forest1 tc.
Proof.
  apply tc_attach_nodes_forest_congr, Foralltr_Forall_subtree, Forall_forall.
  intros sub' Hin.
  simpl.
  unfold has_same_id.
  rewrite eqdec_must_right; auto.
  apply in_map with (f:=tr_rootid) in Hin.
  congruence.
Qed.
(* 
Corollary tc_attach_nodes_forest_congr_hdnotin forest sub sub' tc
  (Hnotin : ~ In (tr_rootid sub) (map tr_rootid (tr_flatten tc)))
  (Eid : tr_rootid sub = tr_rootid sub') :
  tc_attach_nodes (sub :: forest) tc = tc_attach_nodes (sub' :: forest) tc.
Proof. rewrite ! tc_attach_nodes_forest_cleanhd; auto; congruence. Qed.
*)
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
  destruct subtree_tc' as [ [] ] eqn:E, pivot as [ [] ] eqn:Epivot.
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
    destruct (tc_attach_nodes _ tc') as [ [] ].
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
    apply tr_getnode_in_iff_neg in Eres.
    destruct (find _ _) as [ res' | ] eqn:Eres' in |- *; simpl.
    - apply trs_find_has_id in Eres'.
      destruct Eres' as (Hin'%filter_In%proj1 & <-).
      rewrite tc_getclk_as_fmap, id_nodup_find_self_subtr; auto.
    - apply trs_find_in_iff_neg in Eres'.
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

  Fact tc_join_pointwise_max_pre_pre
    (Hroot_clk_lt : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') t :
    tc_getclk t (tc_join tc tc') = 
      match tr_getnode t (tc_get_updated_nodes_join tc tc') with
      | Some res => tc_rootclk res
      | None => tc_getclk t tc
      end.
  Proof.
    pose proof (tc_join_go tc tc' Hroot_clk_lt) as ->.
    pose proof (tc_join_partial_getclk (tid_nodup Hshape) 
      (id_nodup_prefix_preserve (tc_get_updated_nodes_join_is_prefix _ _) (tid_nodup Hshape')) 
      (tc_get_updated_nodes_root_notin Hshape' Hrespect Hroot_clk_lt Hroot_clk_le)) as Htmp.
    rewrite Htmp; reflexivity.
  Qed.

  Lemma tc_join_pointwise_max_pre
    (Hroot_clk_lt : tc_getclk (tr_rootid tc') tc < tc_rootclk tc') t :
    tc_getclk t (tc_join tc tc') = Nat.max (tc_getclk t tc) (tc_getclk t tc').
  Proof.
    rewrite tc_join_pointwise_max_pre_pre by assumption.
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
        destruct tc as [ [] ].
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

End TC_Join_Partial_And_Join.

(* The following section is for showing the equivalence between the functional join
    and the imperative join (implemented as a series of node removal and prepending). *)

Section TC_Join_Iterative.

(* We start by proving all auxiliary things. *)

Lemma tc_detach_attach_distr1_fst tc forest tcs
  (Hnotin : forall t, In t (map tr_rootid tcs) -> ~ In t (map tr_rootid (tr_flatten tc))) :
  fst (tc_detach_nodes tcs (tc_attach_nodes forest tc)) =
  tc_attach_nodes (map (fun tc' => fst (tc_detach_nodes tcs tc')) forest) tc.
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  simpl in Hnotin.
  cbn delta [tc_attach_nodes] iota beta zeta.
  remember (match trs_find_node (info_tid ni) forest with Some u => tr_rootchn u | None => nil end) as app_chn eqn:Eapp_chn.
  remember (map (tc_attach_nodes forest) chn) as old_chn eqn:Eold_chn.
  pose proof (tc_detach_nodes_eta ni (old_chn ++ app_chn) tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach.
  simpl.
  f_equal.
  subst new_chn' new_chn.
  (* split *)
  rewrite map_app, filter_app.
  f_equal.
  - subst old_chn.
    rewrite map_map.
    rewrite filter_all_true.
    + apply map_ext_Forall.
      revert IH.
      apply Forall_impl_impl, Forall_forall.
      intros ch Hin_ch HH.
      apply HH.
      intros t Hin Htmp.
      eapply Hnotin; eauto.
      right.
      eapply map_flat_map_In_conv; eauto.
    + intros ? (ch & <- & Hin)%in_map_iff.
      rewrite tc_detach_nodes_fst_rootid_same, negb_true_iff, isSome_false_is_None, 
        <- trs_find_in_iff_neg, (tr_rootinfo_id_inj (tc_attach_nodes_rootinfo_same _ _)).
      intros HH.
      eapply Hnotin; eauto.
      right.
      now apply in_map, trs_flatten_self_in.
  - subst app_chn.
    (* just do induction *)
    clear -forest.
    induction forest as [ | tc' forest IH ]; simpl; auto.
    erewrite -> tr_rootinfo_has_same_id_congr with (x:=(fst (tc_detach_nodes tcs tc'))).
    2: apply tc_detach_nodes_fst_rootinfo_same.
    destruct (has_same_id (info_tid ni) tc') eqn:E.
    + destruct tc' as [ ni' chn' ].
      pose proof (tc_detach_nodes_eta ni' chn' tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
      rewrite Edetach.
      simpl.
      now subst.
    + apply IH.
Qed.

(* FIXME: there are some parts (about In) repeating the proof above *)
Lemma tc_detach_attach_distr1_snd tc forest tcs
  (Hnotin : forall t, In t (map tr_rootid tcs) -> ~ In t (map tr_rootid (tr_flatten tc))) :
  Permutation 
    (snd (tc_detach_nodes tcs (tc_attach_nodes forest tc)))
    (flat_map (fun tc' =>
      match trs_find_node (tr_rootid tc') forest with 
      | Some u => snd (tc_detach_nodes tcs u) | None => nil end) (tr_flatten tc)).
Proof.
  induction tc as [ni chn IH] using tree_ind_2; intros.
  simpl in Hnotin.
  cbn delta [tc_attach_nodes] iota beta zeta.
  remember (match trs_find_node (info_tid ni) forest with Some u => tr_rootchn u | None => nil end) as app_chn eqn:Eapp_chn.
  remember (map (tc_attach_nodes forest) chn) as old_chn eqn:Eold_chn.
  pose proof (tc_detach_nodes_eta ni (old_chn ++ app_chn) tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
  rewrite Edetach.
  simpl.
  subst res res' new_chn.
  rewrite <- flat_map_concat_map, flat_map_app, map_app, filter_app.
  (* permute *)
  match goal with |- Permutation ((?l1 ++ ?l2) ++ ?l3 ++ ?l4) _ => 
    replace l3 with (@nil treeclock); 
    [ simpl; transitivity ((l2 ++ l4) ++ l1); [ list.solve_Permutation | ] | ] end.
  2:{
    subst old_chn.
    rewrite map_map, filter_all_false; try reflexivity.
    intros ? (ch & <- & Hin)%in_map_iff.
    rewrite tc_detach_nodes_fst_rootid_same, isSome_false_is_None, 
      <- trs_find_in_iff_neg, (tr_rootinfo_id_inj (tc_attach_nodes_rootinfo_same _ _)).
    intros HH.
    eapply Hnotin; eauto.
    right.
    now apply in_map, trs_flatten_self_in.
  }
  apply Permutation_app.
  - subst app_chn.
    destruct (trs_find_node _ _) as [ [ni' chn'] | ] eqn:E; auto.
    simpl tr_rootchn.
    clear.
    pose proof (tc_detach_nodes_eta ni' chn' tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
    rewrite Edetach.
    simpl.
    subst; now rewrite flat_map_concat_map.
  - subst old_chn.
    rewrite flat_map_concat_map, map_map, <- flat_map_concat_map, <- flat_map_flat_map.
    apply Permutation_Forall_flat_map.
    revert IH.
    apply Forall_impl_impl, Forall_forall.
    intros ch Hin_ch HH.
    apply HH.
    intros t Hin Htmp.
    eapply Hnotin; eauto.
    right.
    eapply map_flat_map_In_conv; eauto.
Qed.

Corollary tc_detach_attach_distr1_snd' tc forest tcs 
  (Hnotin : forall t, In t (map tr_rootid tcs) -> ~ In t (map tr_rootid (tr_flatten tc)))
  (Hdomincl : Forall (fun tc' => isSome (tr_getnode (tr_rootid tc') tc) = true) forest)
  (Hnodup_forest : trs_roots_NoDupId forest)
  (Hnodup : tr_NoDupId tc) :
  Permutation
    (snd (tc_detach_nodes tcs (tc_attach_nodes forest tc)))
    (flat_map (fun tc' => snd (tc_detach_nodes tcs tc')) forest).
Proof.
  rewrite tc_detach_attach_distr1_snd by assumption.
  rewrite (trs_find_rearrangement_flat_map (trs:=forest) (l:=map tr_rootid (tr_flatten tc))); try assumption.
  1: now rewrite ! flat_map_concat_map, ! map_map.
  intros ? (tc' & <- & Hin)%in_map_iff.
  apply tr_getnode_in_iff.
  revert tc' Hin.
  now apply Forall_forall.
Qed.

Corollary tc_detach_attach_distr1_snd'' tc tc' tcs 
  (Hnotin : forall t, In t (map tr_rootid tcs) -> ~ In t (map tr_rootid (tr_flatten tc')))
  (Hnodup : tr_NoDupId tc) (Hnodup' : tr_NoDupId tc') :
  Permutation
    (snd (tc_detach_nodes tcs (tc_attach_nodes (snd (tc_detach_nodes (tr_flatten tc') tc)) tc')))
    (flat_map (fun tc0 => snd (tc_detach_nodes tcs tc0)) (snd (tc_detach_nodes (tr_flatten tc') tc))).
Proof.
  apply tc_detach_attach_distr1_snd'; auto.
  - apply tc_detach_nodes_dom_incl.
  - now apply id_nodup_root_chn_split, tc_detach_nodes_id_nodup.
Qed.

(* show that detaching nodes with a single target is equal to removing a single subtree
    by a series of analytic proofs *)

Lemma tc_detach_nodes_single_fst_pre [tc] :
  forall [l sub] (Hsub : tr_locate tc l = Some sub)
    [tcs] (Hin : In (tr_rootid sub) (map tr_rootid tcs)),
  prefixtr (fst (tc_detach_nodes tcs tc)) (tr_remove_node tc l).
Proof.
  induction tc as [ni chn IH] using tree_ind_2'; intros.
  destruct l as [ | x l ].
  - change (tr_remove_node _ _) with (Node ni chn).
    apply tc_detach_nodes_fst_is_prefix.
  - pose proof (tc_detach_nodes_eta ni chn tcs) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
    rewrite Edetach.
    simpl in Hsub |- *.
    destruct (nth_error chn x) as [ ch | ] eqn:E; try discriminate.
    pose proof E as (Hle & Hlen & Echn & Esuf)%nth_error_mixin.
    (* unfold tr_locate_apply. *)
    destruct (list_rev_destruct l) as [ -> | (l' & y & ->) ]; simpl.
    + unfold tr_remove_node, tr_locate_apply.
      simpl.
      injection Hsub as ->.
      subst.
      eapply prefixtr_by_sublist_map.
      1: apply list.Forall_true, (tc_detach_nodes_fst_is_prefix tcs).
      rewrite Echn at 1. 
      rewrite map_app, filter_app at 1.
      simpl.
      rewrite tc_detach_nodes_fst_rootid_same, (proj1 (trs_find_in_iff (tr_rootid sub) tcs)) by assumption.
      simpl.
      rewrite <- filter_app, <- map_app.
      apply filter_sublist.
    + erewrite tr_remove_node_iota; eauto.
      subst new_chn' new_chn.
      rewrite Echn, upd_nth_exact by assumption.
      rewrite map_filter_comm.
      match goal with |- context[filter ?ff _] => set (f:=ff) end.
      (* need to be very precise here *)
      apply prefixtr_intro with (chn_sub:=filter f (firstn x chn) ++ 
        (if f ch then tr_remove_node ch (l' ++ y :: nil) :: nil else nil) ++ filter f (skipn (S x) chn)).
      1: apply list.sublist_app; [ apply filter_sublist 
          | destruct (f ch); [ apply list.sublist_skip | apply list.sublist_cons ]; apply filter_sublist ].
      rewrite filter_app, map_app.
      apply Forall2_app.
      1: apply Forall2_mapself_l, list.Forall_true, tc_detach_nodes_fst_is_prefix.
      simpl.
      destruct (f ch); simpl.
      1: constructor.
      2-3: apply Forall2_mapself_l, list.Forall_true, tc_detach_nodes_fst_is_prefix.
      eapply IH; eauto.
      eapply nth_error_In; eauto.
Qed.

Lemma tc_detach_nodes_single_snd [tc l sub] (Hsub : tr_locate tc l = Some sub)
  (Hnodup : tr_NoDupId tc) (Hnotnil : l <> nil) :
  snd (tc_detach_nodes (sub :: nil) tc) = sub :: nil.
Proof.
  assert (tr_rootid sub <> tr_rootid tc) as Hneq.
  1: eapply id_nodup_diff_by_pos; eauto; reflexivity.
  pose proof Hsub as Hsub'%subtr_witness_subtr.
  (* two steps: show that the list only contains one thing, and then unify it with "sub" *)
  assert (exists res, snd (tc_detach_nodes (sub :: nil) tc) = res :: nil) as (res & E).
  - pose proof (tc_detach_nodes_dom_partition'' (sub :: nil) tc
      ltac:(simpl; unfold has_same_id; now rewrite eqdec_must_right) Hnodup) as (_ & Hperm%Permutation_length).
    rewrite ! map_length in Hperm.
    simpl in Hperm.
    rewrite filter_ext with (g:=fun sub0 => has_same_id (tr_rootid sub0) sub) in Hperm.
    2: intros; destruct (has_same_id _ _); reflexivity.
    rewrite id_nodup_filter_self in Hperm; auto.
    simpl in Hperm.
    destruct (snd _) as [ | res [ | ] ]; simpl in Hperm; try discriminate.
    eauto.
  - rewrite E; f_equal.
    pose proof (tc_detach_nodes_snd2fst (sub :: nil) tc) as H1.
    pose proof (tc_detach_nodes_dom_incl (sub :: nil) tc) as H2.
    rewrite E in H1, H2.
    apply Forall_inv in H1, H2.
    simpl in H2.
    destruct (has_same_id (tr_rootid res) sub) eqn:EE; try discriminate.
    apply has_same_id_true in EE.
    destruct H1 as (sub' & Hin' & ->).
    (* unify "sub" and "sub'" *)
    rewrite tc_detach_nodes_fst_rootid_same in EE.
    eapply id_nodup_unify_by_id in EE; eauto.
    subst sub'.
    (* use intact *)
    rewrite tc_detach_nodes_intact; try reflexivity.
    simpl.
    intros t Hin [ <- | [] ].
    now apply (id_nodup_rootid_neq' (id_nodup_subtr Hsub' Hnodup)) in Hin.
Qed.

Corollary tc_detach_nodes_single_fst [tc l sub] (Hsub : tr_locate tc l = Some sub)
  (Hnodup : tr_NoDupId tc) (Hnotnil : l <> nil) :
  fst (tc_detach_nodes (sub :: nil) tc) = tr_remove_node tc l.
Proof.
  eapply prefixtr_size_eq_tr_eq.
  1: eapply tc_detach_nodes_single_fst_pre; eauto.
  1: simpl; tauto.
  (* play with info list *)
  pose proof (tc_detach_nodes_dom_partition (sub :: nil) tc) as Hperm.
  erewrite tc_detach_nodes_single_snd in Hperm; eauto.
  simpl in Hperm.
  rewrite app_nil_r, tr_remove_node_dom_partition, map_app in Hperm; eauto.
  apply Permutation_app_inv_r, Permutation_length in Hperm.
  now rewrite ! map_length in Hperm.
Qed.

Corollary tc_detach_nodes_single [tc l sub] (Hsub : tr_locate tc l = Some sub)
  (Hnodup : tr_NoDupId tc) (Hnotnil : l <> nil) :
  tc_detach_nodes (sub :: nil) tc = (tr_remove_node tc l, sub :: nil).
Proof.
  erewrite <- tc_detach_nodes_single_fst; eauto.
  erewrite <- tc_detach_nodes_single_snd at 3; eauto.
  now destruct (tc_detach_nodes _ _).
Qed.

Fact tc_detach_nodes_visited_prefix_pre2post
  [tc' pos' sub'] (H : tr_locate tc' pos' = Some sub') (Hnotnil : pos' <> nil) tc :
  tc_detach_nodes (tr_flatten (post_iter_visited_prefix tc' pos')) tc =
  tc_detach_nodes (sub' :: tr_flatten (pre_iter_visited_prefix tc' pos')) tc.
Proof.
  now apply tc_detach_nodes_tcs_congr, Permutation_in_mutual, Permutation_rootinfo2rootid, visited_prefix_dom.
Qed.

(* 2 in 1 *)
Fact tc_attach_nodes_single (b : bool) [tc pos sub'] (Hnodup : tr_NoDupId tc)
  (H : tr_locate tc pos = Some sub') (Hnotnil : pos <> nil)
  [sub] (Eid : tr_rootid sub' = tr_rootid sub) [forest] 
  (Hnotin : if b then True else trs_find_node (tr_rootid sub') forest = None) :
  tr_prepend_nodes
    (tc_attach_nodes forest (pre_iter_visited_prefix tc pos)) (repeat 0 (length pos - 1))
    (Node (tr_rootinfo sub') (if b then tr_rootchn sub else nil) :: nil) =
  tc_attach_nodes ((if b then sub :: nil else nil) ++ forest) (post_iter_visited_prefix tc pos).
Proof.
  unfold pre_iter_visited_prefix, post_iter_visited_prefix.
  revert tc Hnodup H sub Eid.
  induction pos as [ | x pos IH ]; intros [ni chn]; intros; try contradiction.
  assert (tr_rootid (Node ni chn) <> tr_rootid sub') as Hneq by (eapply id_nodup_diff_by_pos; eauto; try reflexivity).
  simpl in Hneq.
  clear Hnotnil.
  simpl in H |- *.
  destruct (nth_error chn x) as [ ch | ] eqn:E; try discriminate.
  pose proof E as (Hle & Hlen & Echn & Esuf)%nth_error_mixin.
  rewrite Nat.sub_0_r.
  simpl.
  (* simplify *)
  unfold trs_find_node.
  rewrite find_app.
  replace (find _ (if b then sub :: nil else nil)) with (@None treeclock).
  2: destruct b; simpl; [ now rewrite (proj2 (has_same_id_false _ _)) by now rewrite <- Eid | reflexivity ].
  rewrite map_ext_Forall with (g:=tc_attach_nodes forest).
  2:{
    destruct b; [ | now apply list.Forall_true ].
    simpl.
    rewrite Forall_forall.
    intros ch' (y & E')%In_nth_error.
    eapply tc_attach_nodes_forest_cleanhd. 
    unfold not; eapply id_nodup_diff_by_index with (y:=S (x + y)).
    1: apply id_nodup_tr_chn, Hnodup.
    1: apply E.
    2: lia.
    2: rewrite <- Eid; eapply in_map, subtr_witness_subtr; eauto.
    simpl tr_rootchn.
    rewrite Echn, nth_error_app2; rewrite Hlen.
    2: lia.
    now replace (S (x + y) - x) with (S y) by lia.
  }
  destruct (list_ifnil_destruct pos) as [ -> | Hnotnil ].
  - injection H as <-.
    cbn delta -[nth_error trs_find_node] beta iota.
    change (info_tid (tr_rootinfo ch)) with (tr_rootid ch). (* TODO this is bad! *)
    replace (match trs_find_node (tr_rootid ch) _ with Some _ => _ | None => _ end) 
      with (if b then tr_rootchn sub else nil).
    2: destruct b; simpl; [ now rewrite Eid, has_same_id_refl | now rewrite Hnotin ].
    destruct (nth_error chn (S x)) as [ ch' | ] eqn:E'.
    + cbn delta [isSome] beta match.
      rewrite <- (tree_recons ch'), <- (proj2 (proj2 (proj2 (nth_error_mixin E')))).
      reflexivity.
    + apply nth_error_None in E'.
      rewrite skipn_all2 by assumption.
      reflexivity.
  - rewrite ! pos_succ_cons' by assumption.
    replace (length pos) with (S (length pos - 1)) by (destruct pos; try contradiction; simpl; lia).
    simpl.
    rewrite E. 
    simpl. 
    unfold tr_prepend_nodes.
    rewrite tr_locate_apply_iota.
    simpl.
    do 2 f_equal.
    eapply IH; eauto.
    eapply id_nodup_ch; eauto.
    now apply nth_error_In in E.
Qed.

Section TC_Join_Iterative_Real.

  Context [tc tc' : treeclock].
  Hypotheses (Hnodup : tr_NoDupId tc)
    (Hnotin : ~ In (tr_rootid tc) (map tr_rootid (tr_flatten tc'))).

  (* note that these equations are not EXPLICITLY necessary for the imperaive proof
      (i.e., they can be derived during the proof), but listing them here will make
      the proof outline clear *)
  (* the proofs here are not meant to be reused, so they are written casually *)

  (* we write single detach node here; in the imperative proof, they will be replaced
      by removing single node *)

  Fact tc_join_partial_iterative_init :
    let: (pivot, forest) := tc_detach_nodes (tc' :: nil) tc in
    let: targ := 
      (* hd (Node (mkInfo (tr_rootid tc') 0%nat 0%nat) nil) forest in *)
      option.from_option tr_rootchn (@nil treeclock) (hd_error forest) in
    let: new_ch := Node (mkInfo (tr_rootid tc') (tc_rootclk tc') (tc_rootclk tc)) targ in
    (* 
    let: Node (mkInfo w _ _) chn_w :=
      hd (Node (mkInfo (tr_rootid tc') 0%nat 0%nat) nil) forest in
    let: new_ch := Node (mkInfo w (tc_rootclk tc') (tc_rootclk tc)) chn_w in
    *)
    let: pivot' := tr_prepend_nodes pivot nil (new_ch :: nil) in
    pivot' = tc_join_partial tc (Node (tr_rootinfo tc') nil).
  Proof.
    unfold tc_join_partial.
    simpl tr_flatten.
    rewrite tc_detach_nodes_tcs_congr with (tcs1:=Node _ _ :: nil) (tcs2:=tc' :: nil) by auto.
    destruct (tr_getnode (tr_rootid tc') tc) as [ sub | ] eqn:E.
    - pose proof E as ((l & Hsub)%subtr_subtr_witness & Eid)%trs_find_has_id.
      destruct (list_ifnil_destruct l) as [ -> | Hnotnil ].
      1: injection Hsub as <-; rewrite Eid in Hnotin; now pose proof (tr_self_id_in tc').
      rewrite tc_detach_nodes_tcs_congr with (tcs2:=sub :: nil).
      2: simpl; rewrite Eid; auto.
      simpl.
      pose proof (tc_detach_nodes_single Hsub Hnodup Hnotnil) as Edetach.
      rewrite Edetach.
      change (info_tid (tr_rootinfo tc')) with (tr_rootid tc').
      rewrite <- Eid. simpl.
      rewrite has_same_id_refl.
      unfold tr_prepend_nodes, tr_locate_apply. simpl.
      destruct sub as [ [] ] eqn:E1, (tr_remove_node tc l), (tr_rootinfo tc') eqn:E2.
      simpl in Eid |- *.
      unfold tr_rootid in Eid.
      rewrite E2 in Eid.
      simpl in Eid; rewrite Eid.
      unfold tc_rootclk.
      rewrite E2; simpl.
      erewrite <- (tc_detach_nodes_fst_rootinfo_same _ tc).
      rewrite Edetach. simpl. reflexivity.
    - apply tr_getnode_in_iff_neg in E.
      rewrite tc_detach_nodes_intact'.
      2: simpl; intros t Hin [ <- | [] ]; auto.
      simpl.
      unfold tr_prepend_nodes, tr_locate_apply. simpl.
      destruct tc.
      unfold tr_rootid, tc_rootclk.
      destruct (tr_rootinfo tc') eqn:E2.
      simpl. reflexivity.
  Qed.

  Hypothesis (Hnodup' : tr_NoDupId tc').

  Fact tc_join_partial_iterative_trans 
    [pos' sub'] (H : tr_locate tc' pos' = Some sub') (Hnotnil' : pos' <> nil) :
    let: (pivot, forest) := tc_detach_nodes (sub' :: nil) 
      (tc_join_partial tc (pre_iter_visited_prefix tc' pos')) in
    let: targ := 
      (* hd (Node (mkInfo (tr_rootid tc') 0%nat 0%nat) nil) forest in *)
      option.from_option tr_rootchn (@nil treeclock) (hd_error forest) in
    let: new_ch := Node (tr_rootinfo sub') targ in
    (*
    let: Node (mkInfo w _ _) chn_w :=
      hd (Node (mkInfo (tr_rootid sub') 0%nat 0%nat) nil) forest in
    let: new_ch := Node (mkInfo w (tc_rootclk sub') (tc_rootaclk sub')) chn_w in
    *)
    let: pivot' := tr_prepend_nodes pivot (List.repeat 0%nat (length pos')) (new_ch :: nil) in
    (* FIXME: this exposes something interesting: we need to know the parent when proving
        about prepending child in C (since we need to reset the parent field and link the child to its new parent),
        but we do not need to know the parent for detaching node! this is probably because that
        for detaching node, we always assume the existence of the node to be detached and thus 
        we know the existence of its parent, while here we assume nothing!
      can this be fixed later? *)
    base.fmap tr_rootid (tr_locate pivot (List.repeat 0%nat (length pos'))) = 
      base.fmap tr_rootid (tr_locate tc' (removelast pos')) /\
    pivot' = tc_join_partial tc (post_iter_visited_prefix tc' pos').
  Proof.
    assert (tr_rootid sub' <> tr_rootid tc) as Hneq_sub'.
    { revert Hnotin. apply ssrbool.contra_not. intros <-. now apply subtr_witness_subtr, (in_map tr_rootid) in H. }
    assert (tr_rootid sub' <> tr_rootid tc') as Hneq_sub''
      by (eapply id_nodup_diff_by_pos; eauto; try reflexivity).
    unfold tc_join_partial.
    pose proof (fun tr1 tr2 (H : prefixtr tr1 tr2) t => ssrbool.contra_not (prefixtr_flatten_id_incl H t)) as Hnotin_pf.

    (* a whole bunch of preparations *)
    pose proof (pre_iter_visited_is_prefix tc' pos') as Hpre_pf.
    pose proof (id_nodup_prefix_preserve Hpre_pf Hnodup') as Hnodup_pre_pf.
    remember (pre_iter_visited_prefix tc' pos') as prefix_pre eqn:Eprefix_pre.
    destruct (tc_detach_nodes (tr_flatten prefix_pre) tc) as (pivot_pre, forest_pre) eqn:Edetach_pre.
    destruct (tc_attach_nodes forest_pre prefix_pre) as [ni_pre chn_w_pre] eqn:Eattach_pre.
    pose proof (tc_attach_nodes_rootinfo_same forest_pre prefix_pre) as Eni_pre.
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Eni_z_pre.
    rewrite -> Eattach_pre, -> Eprefix_pre in Eni_pre.
    setoid_rewrite -> (prefixtr_rootinfo_same (tr_vsplitr_is_prefix _ _ _)) in Eni_pre.
    rewrite -> Edetach_pre in Eni_z_pre.
    destruct pivot_pre as [ni_z_pre chn_z_pre] eqn:Epivot_pre.
    simpl in Eni_pre, Eni_z_pre.
    subst ni_pre ni_z_pre.
    rewrite <- Epivot_pre in Edetach_pre.
    (* we need disjoint later! *)
    pose proof (tc_join_partial_id_nodup Hnodup Hnodup_pre_pf (Hnotin_pf _ _ Hpre_pf _ Hnotin)) as Hnodup_partialjoin.
    pose proof (tc_join_partial_dom_info tc prefix_pre) as Hperm_partialjoin.
    rewrite <- map_app in Hperm_partialjoin.
    apply Permutation_rootinfo2rootid in Hperm_partialjoin.
    rewrite Edetach_pre in Hperm_partialjoin. simpl in Hperm_partialjoin.
    rewrite map_app in Hperm_partialjoin.
    replace (map tr_rootid (tr_flatten (let 'Node _ _ := _ in _))) with (map tr_rootid (tr_flatten (tc_attach_nodes forest_pre prefix_pre))) in Hperm_partialjoin.
    2:{ rewrite Eattach_pre. now destruct (tr_rootinfo tc'). }
    pose proof Hnodup_partialjoin as Hdisjoint%(Permutation_NoDup Hperm_partialjoin).
    rewrite NoDup_app_ in Hdisjoint.
    destruct Hdisjoint as (Hnodup_pivot_pre & Hdisjoint & Hnodup_attach_pre).
    (* backup *)
    pose proof (eq_refl (tc_join_partial tc (pre_iter_visited_prefix tc' pos'))) as Heq_pre.
    unfold tc_join_partial in Heq_pre at 2.
    rewrite <- Eprefix_pre, Edetach_pre, Epivot_pre, Eattach_pre in Heq_pre.

    (* another bunch of preparations *)
    pose proof (post_iter_visited_is_prefix tc' pos') as Hpost_pf.
    pose proof (id_nodup_prefix_preserve Hpost_pf Hnodup') as Hnodup_post_pf.
    remember (post_iter_visited_prefix tc' pos') as prefix_post eqn:Eprefix_post.
    destruct (tc_detach_nodes (tr_flatten prefix_post) tc) as (pivot_post, forest_post) eqn:Edetach_post.
    destruct (tc_attach_nodes forest_post prefix_post) as [ni_post chn_w_post] eqn:Eattach_post.
    pose proof (tc_attach_nodes_rootinfo_same forest_post prefix_post) as Eni_post.
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Eni_z_post.
    rewrite -> Eattach_post, -> Eprefix_post in Eni_post.
    setoid_rewrite -> (prefixtr_rootinfo_same (tr_vsplitr_is_prefix _ _ _)) in Eni_post.
    rewrite -> Edetach_post in Eni_z_post.
    destruct pivot_post as [ni_z_post chn_z_post] eqn:Epivot_post.
    simpl in Eni_post, Eni_z_post.
    subst ni_post ni_z_post.
    rewrite <- Epivot_post in Edetach_post.
    (* show that "trs_roots_NoDupId forest_post" *)
    pose proof (tc_detach_nodes_id_nodup (tr_flatten prefix_post) tc Hnodup) as (Hnodup_forest_post & _ & _).
    apply id_nodup_root_chn_split, proj1 in Hnodup_forest_post.
    rewrite Edetach_post in Hnodup_forest_post. simpl in Hnodup_forest_post.
    (* backup *)
    pose proof (eq_refl (tc_join_partial tc (post_iter_visited_prefix tc' pos'))) as Heq_post.
    unfold tc_join_partial in Heq_post at 2.
    rewrite <- Eprefix_post, Edetach_post, Epivot_post, Eattach_post in Heq_post.

    destruct tc' as [(u', clk_u', aclk_u') chn_u'] eqn:Etc'.
    cbn delta -[tc_detach_nodes] zeta beta iota.
    rewrite <- Etc' in *.
    rewrite Etc' in Heq_pre, Heq_post, Hneq_sub''.
    simpl in Heq_pre, Heq_post, Hneq_sub''.
    fold (tc_rootclk tc) in Heq_pre, Heq_post |- *.

    pose proof (stack_top_not_visited H Hnotnil' Hnodup') as Hnotin_sub'.
    rewrite <- Eprefix_pre in Hnotin_sub'.

    (* detach decomposition *)
    epose proof (tc_detach_nodes_prepend_child (tr_rootinfo tc) 
      (Node (mkInfo u' clk_u' (tc_rootclk tc)) chn_w_pre) chn_z_pre (sub' :: nil) ?[Goalq]) as Edetach_decomp.
    [Goalq]:{ simpl. unfold has_same_id. rewrite eqdec_must_right; auto. }
    (* an awkward situation is that the attached clocks do not match, so need to work around *)
    pose (f:=fun '(Node (mkInfo a b c) d) => Node (mkInfo a b (tc_rootclk tc)) d).
    replace (Node (mkInfo u' _ _) _) with (f (tc_attach_nodes forest_pre prefix_pre)) 
      in Edetach_decomp, Heq_pre |- *
      by (subst f tc'; rewrite Eattach_pre; simpl; reflexivity).
    assert (tc_detach_nodes (sub' :: nil) (f (tc_attach_nodes forest_pre prefix_pre)) = 
      let: (res1, res2) := tc_detach_nodes (sub' :: nil) (tc_attach_nodes forest_pre prefix_pre) in
        (f res1, res2)) as Etmp.
    { subst f.
      rewrite Eattach_pre, Etc'.
      cbn delta -[tc_detach_nodes] zeta beta iota.
      pose proof (tc_detach_nodes_eta (mkInfo u' clk_u' aclk_u') chn_w_pre (sub' :: nil)) as (new_chn & res & res' & new_chn' & Esplit & Epar & Enew_chn & Eres & Eres' & Enew_chn' & Edetach).
      rewrite Edetach.
      simpl in Epar |- *.
      now rewrite Esplit, Epar.
    }
    (* da = detach attach, dp = detach pivot_pre *)
    destruct (tc_detach_nodes (sub' :: nil) (tc_attach_nodes forest_pre prefix_pre)) as (pivot_da, forest_da) eqn:Eda.
    rewrite Etmp, <- Epivot_pre in Edetach_decomp.
    destruct (tc_detach_nodes (sub' :: nil) pivot_pre) as (pivot_dp, forest_dp) eqn:Edp.
    (* unify some rootinfo *)
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Etmp2.
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Etmp3.
    rewrite -> Eda in Etmp2. rewrite -> Edp in Etmp3.
    destruct pivot_da as [ni_pda chn_pda] eqn:Epivot_da, pivot_dp as [ni_pdp chn_pdp] eqn:Epivot_dp.
    simpl in Etmp2, Etmp3.
    rewrite Eattach_pre in Etmp2.
    rewrite Epivot_pre in Etmp3.
    cbn delta [tr_rootinfo] beta iota in Etmp2, Etmp3.
    subst ni_pda ni_pdp.
    rewrite <- Epivot_da in Eda. rewrite <- Epivot_dp in Edp.
    rewrite Edetach_decomp. clear Etmp. (* DO NOT clear the decomposition; it might be used later *)
    rewrite <- Heq_pre, <- Epivot_da in Edetach_decomp.

    (* use detach-attach distribution *)
    pose proof (tc_detach_attach_distr1_fst prefix_pre forest_pre (sub' :: nil)) as Epivot_da'.
    simpl in Epivot_da'.
    specialize (Epivot_da' ltac:(intros t [ <- | [] ]; assumption)).
    rewrite Eda in Epivot_da'. simpl in Epivot_da'.
    pose proof (tc_detach_attach_distr1_snd'' tc prefix_pre (sub' :: nil)) as Eforest_da.
    simpl in Eforest_da.
    specialize (Eforest_da ltac:(intros t [ <- | [] ]; assumption) Hnodup (id_nodup_prefix_preserve Hpre_pf Hnodup')).
    rewrite Edetach_pre in Eforest_da. simpl in Eforest_da.
    rewrite Eda in Eforest_da. simpl in Eforest_da.

    (* use detach cascading to precisely describe "forest_post" and do some unification *)
    pose proof Edetach_post as Edetach_post'.
    erewrite Eprefix_post, tc_detach_nodes_visited_prefix_pre2post, <- Eprefix_pre in Edetach_post'; eauto.
    pose proof (tc_detach_nodes_tcs_app_fst (tr_flatten prefix_pre) (sub' :: nil) tc) as Etmp1.
    rewrite tc_detach_nodes_tcs_congr_app in Etmp1. simpl app in Etmp1.
    rewrite Edetach_post', Edetach_pre in Etmp1. simpl in Etmp1.
    rewrite Edp in Etmp1. simpl in Etmp1. 
    subst pivot_post. (* ! *)
    rewrite Epivot_dp in Etmp1. inversion Etmp1. subst chn_z_post. clear Etmp1.
    pose proof (tc_detach_nodes_tcs_app_snd (tr_flatten prefix_pre) (sub' :: nil) tc) as Eforest_post.
    rewrite tc_detach_nodes_tcs_congr_app in Eforest_post. simpl app in Eforest_post.
    rewrite Edetach_post', Edetach_pre in Eforest_post. simpl in Eforest_post.
    rewrite Edp in Eforest_post. simpl in Eforest_post.
    rewrite flat_map_concat_map, ! map_map, <- flat_map_concat_map, <- Eforest_da in Eforest_post.
    clear Edetach_post'.

    (* finally, get rid of "forest_post" *)
    replace (Node (mkInfo _ _ _) chn_w_post) with (f (tc_attach_nodes forest_post prefix_post)) in |- * 
      by (now rewrite Eattach_post, Etc').
    rewrite <- Permutation_app_rot in Eforest_post. (* this is important! avoid later rewriting *)
    erewrite tc_attach_nodes_forest_congr'; eauto.
    clear dependent forest_post.

    (* small lemma *)
    assert (tr_getnode (tr_rootid sub') (f (tc_attach_nodes forest_pre prefix_pre)) =
      tr_getnode (tr_rootid sub') (tc_attach_nodes forest_pre prefix_pre)) as Eff.
    { rewrite Eattach_pre, Etc'.
      subst f.
      simpl. rewrite eqdec_must_right; auto.
    }

    (* small preparation *)
    assert (forall (tr : treeclock) l ch, tr_prepend_nodes (f tr) l ch = f (tr_prepend_nodes tr l ch)) as prepend_f_comm.
    { unfold tr_prepend_nodes. intros [ [] ] [ | ] ch. 1: reflexivity. simpl. rewrite ! tr_locate_apply_iota. reflexivity. }    
    assert (forall (tr : treeclock) l, base.fmap tr_rootid (tr_locate (f tr) l) = base.fmap tr_rootid (tr_locate tr l)) as locate_f_comm
      by (intros [ [] ] [ | ]; reflexivity).
    replace (length pos') with (S (length pos' - 1)) by (destruct pos'; try contradiction; simpl; lia).
    simpl repeat.
    unfold tr_prepend_nodes. rewrite tr_locate_apply_iota. cbn delta [nth_error upd_nth] beta iota.
    (* reduce to prepending node over the old result of attaching nodes *)
    rewrite <- Epivot_da.
    setoid_rewrite prepend_f_comm. clear prepend_f_comm.
    simpl tr_locate. rewrite locate_f_comm. clear locate_f_comm.
    rewrite Epivot_da'. 
    split.
    1:{ 
      change tr_rootid with (Basics.compose info_id tr_rootinfo).
      rewrite 2 option.option_fmap_compose. f_equal.
      pose proof (visited_prefix_pre2post H Hnotnil') as (Htmp & _).
      apply tr_locate_parent in H; try assumption.
      destruct H as (tr_par & Epar & _).
      rewrite Epar in Htmp |- *. simpl in Htmp |- *.
      destruct (tr_locate _ _) as [ res | ] eqn:EE in Htmp; try discriminate.
      subst prefix_pre.
      erewrite tc_attach_nodes_colocate; eauto.
    }

    do 2 f_equal.

    (* now, discuss if we can find a node with "tr_rootid sub'" in "tc_join_partial tc prefix_pre" *)
    destruct (tr_getnode (tr_rootid sub') (tc_join_partial tc prefix_pre)) as [ sub | ] eqn:E.
    - (* if we can, then it must come from "pivot_pre" or "tc_attach_nodes forest_pre prefix_pre" *)
      rewrite Heq_pre in E.
      simpl in E.
      rewrite eqdec_must_right in E by auto.
      rewrite find_app in E.
      (* doing case analysis here is possibly the most convenient way *)
      fold (tr_getnode (tr_rootid sub') (f (tc_attach_nodes forest_pre prefix_pre))) in E.
      destruct (tr_getnode _ _) as [ ? | ] eqn:E' in E.
      + (* from "tc_attach_nodes forest_pre prefix_pre" *)
        (* use detach single on da part, use detach intact on dp part *)
        injection E as ->.
        rewrite Eff in E'. apply trs_find_has_id in E'.
        destruct E' as ((pos & Hin)%subtr_subtr_witness & Eid). 
        assert (pos <> nil) as Hnotnil.
        { intros ->. injection Hin as <-. rewrite Eattach_pre, Etc' in Eid. simpl in Eid. congruence. }
        rewrite tc_detach_nodes_tcs_congr with (tcs2:=sub :: nil) in Eda.
        2: simpl; rewrite Eid; auto.
        erewrite tc_detach_nodes_single in Eda; eauto.
        apply pair_equal_split in Eda. destruct Eda as (_ & <-). (* single remove is not useful here *)
        rewrite tc_detach_nodes_intact' in Edp.
        2:{
          simpl. intros t Hin' [ <- | [] ]. eapply Hdisjoint; eauto.
          rewrite <- Eid. eapply in_map, subtr_witness_subtr; eauto.
        }
        apply pair_equal_split in Edp. destruct Edp as (_ & <-).

        (* finally *)
        subst prefix_pre prefix_post.
        setoid_rewrite <- (tc_attach_nodes_single true); eauto.
      + (* from "pivot_pre" *)
        (* use detach single on dp part, use detach intact on da part *)
        rewrite Eff in E'. apply trs_find_has_id in E.
        destruct E as ((ch & (x & Enth)%In_nth_error & (pos & Hin)%subtr_subtr_witness)%in_flat_map & Eid).
        assert (tr_locate pivot_pre (x :: pos) = Some sub) as Hin' by (rewrite Epivot_pre; simpl; now rewrite Enth).
        rewrite tc_detach_nodes_tcs_congr with (tcs2:=sub :: nil) in Edp.
        2: simpl; rewrite Eid; auto.
        erewrite tc_detach_nodes_single in Edp; eauto.
        apply pair_equal_split in Edp. destruct Edp as (_ & <-). (* single remove is not useful here *)
        rewrite tc_detach_nodes_intact' in Eda.
        2:{
          simpl. intros t Hin'' [ <- | [] ]. eapply (Hdisjoint (tr_rootid sub')); eauto.
          rewrite <- Eid. eapply in_map, subtr_witness_subtr; eauto.
        }
        apply pair_equal_split in Eda. destruct Eda as (_ & <-).

        (* the following part is ALMOST THE SAME as the branch above; we come to the same proof goal *)
        subst prefix_pre prefix_post.
        setoid_rewrite <- (tc_attach_nodes_single true); eauto.
    - (* reuse the decomposition *)
      apply trs_find_in_iff_neg in E.
      rewrite tc_detach_nodes_intact' in Edetach_decomp.
      2: intros ? ? [ <- | [] ]; auto.
      apply pair_equal_split in Edetach_decomp. 
      destruct Edetach_decomp as (Epartialjoin' & (-> & ->)%eq_sym%app_eq_nil).

      (* the following preparation is almost the same as the branch above *)
      (* but the proof goal is different! *)
      subst prefix_pre prefix_post.
      setoid_rewrite <- (tc_attach_nodes_single false); eauto.
      apply trs_find_in_iff_neg.
      setoid_rewrite map_map.
      rewrite map_ext with (g:=tr_rootid) by (intros; apply tc_detach_nodes_fst_rootid_same).
      intros (el & Eid' & Hin)%in_map_iff.
      replace forest_pre with (snd (tc_detach_nodes (tr_flatten (pre_iter_visited_prefix tc' pos')) tc)) in Hin by now rewrite Edetach_pre.
      eapply (proj1 (Forall_forall _ _) (tc_detach_nodes_dom_incl _ _)), trs_find_in_iff in Hin.
      congruence.
  Qed.

  (* during join, clock will be obtained from partial join, so need some congruence lemmas *)
  (* here we treat "tc'" as the original tree from which we get "tc_get_updated_nodes_join" prefix *)
  Corollary tc_get_updated_nodes_join_aux_tc_congr_partialjoin
    [pos' sub'] (H : tr_locate (tc_get_updated_nodes_join tc tc') pos' = Some sub') 
    (Hnotin' : ~ In (tr_rootid tc) (map tr_rootid (tr_flatten (tc_get_updated_nodes_join tc tc'))))
    [sub] (Hsub : subtr sub tc') (Esub' : sub' = tc_get_updated_nodes_join tc sub) clk :
    map tr_rootinfo (tc_get_updated_nodes_join_aux 
      (tc_join_partial tc (post_iter_visited_prefix (tc_get_updated_nodes_join tc tc') pos')) clk (tr_rootchn sub)) = 
    map tr_rootinfo (tc_get_updated_nodes_join_aux tc clk (tr_rootchn sub)).
  Proof using -Hnotin. clear Hnotin.
    pose proof (fun tr1 tr2 (H : prefixtr tr1 tr2) t => ssrbool.contra_not (prefixtr_flatten_id_incl H t)) as Hnotin_pf.
    pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hpf1.
    pose proof (post_iter_visited_is_prefix (tc_get_updated_nodes_join tc tc') pos') as Hpf2.
    pose proof (prefixtr_trans Hpf2 Hpf1) as Hpf.
    apply tc_get_updated_nodes_join_aux_tc_congr, Forall_forall.
    intros x Hin.
    rewrite tc_join_partial_getclk; auto.
    3: eapply Hnotin_pf; auto using post_iter_visited_is_prefix.
    2: eapply id_nodup_prefix_preserve; eauto.
    destruct (tr_getnode _ _) eqn:E; [ | reflexivity ].
    (* need to show that the disjointness of the id of any child of "sub"
        and any id in "post_iter_visited_prefix tc' pos'" *)
    (* do this by showing that (1) after adding all children of "sub" to "post_iter_visited_prefix tc' pos'", 
        the result is still a prefix of "tc'" and thus enjoys the "tr_NoDupId" property; then
        (2) the disjointness is derived by "NoDup (... ++ ...)", which is in turn by
        the domain addition property of "tr_prepend_nodes" *)
    pose proof (tr_vsplitr_locate false H) as Hloc.
    simpl in Hloc.
    rewrite Esub', (prefixtr_rootinfo_same (tc_get_updated_nodes_join_is_prefix tc sub)) in Hloc.
    eapply prefixtr_concatenate with (l:=List.repeat 0%nat (length pos')) (sub_prefix':=sub) in Hpf.
    5: reflexivity.
    all: try assumption.
    apply id_nodup_prefix_preserve in Hpf; try assumption.
    pose proof (tr_prepend_nodes_dom_addition (f_equal (@isSome _) Hloc) (tr_rootchn sub)) as Hperm.
    rewrite <- map_app in Hperm.
    apply Permutation_rootinfo2rootid in Hperm.
    eapply Permutation_NoDup in Hpf; [ | apply Hperm ].
    rewrite map_app, NoDup_app_ in Hpf.
    exfalso.
    eapply (proj1 (proj2 Hpf)).
    2: eapply map_flat_map_In_conv; [ apply Hin | apply in_map, tr_flatten_self_in ].
    apply tr_getnode_in_iff.
    now setoid_rewrite E.
  Qed.

End TC_Join_Iterative_Real.

End TC_Join_Iterative.

End TreeClock.

Global Arguments nodeinfo : clear implicits.

#[export] Existing Instance EqDec_nodeinfo.
#[export] Existing Instance nodeinfo_IdGetter.
