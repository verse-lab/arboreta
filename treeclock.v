From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.

(* Coq's list library is not very complete.  *)
From stdpp Require list.

Tactic Notation "removehead" hyp(H) :=
  let qq := fresh "nobody_will_use_this" in
  let qq2 := fresh "nobody_will_use_this2" in
  match (type of H) with
  ?HH -> _ => enough HH as qq; 
    [ pose proof (H qq) as qq2; clear H; rename qq2 into H; clear qq | ]
  end
.

(* TODO is this in somewhere of Coq std lib? *)
(* Search "ind" inside PeanoNat. *)
Lemma nat_ind_2 : forall P : nat -> Prop,
  P 0 -> 
  (forall n : nat, (forall m : nat, m <= n -> P m) -> P (S n)) -> 
  forall n : nat, P n.
Proof.
  intros P H IH.
  set (Q:=fun n => (forall m : nat, m <= n -> P m)).
  assert (forall n, Q n) as Hfinal.
  {
    induction n; unfold Q in *; intros.
    - inversion H0. subst. auto.
    - inversion H0; subst.
      + now apply IH.
      + now apply IHn.
  }
  intros. unfold Q in Hfinal. now apply Hfinal with (n:=n).
Qed.

Lemma nat_ind_3 : forall P : nat -> Prop,
  (forall n : nat, (forall m : nat, m < n -> P m) -> P n) -> 
  forall n : nat, P n.
Proof.
  intros P IH.
  set (Q:=fun n => (forall m : nat, m < n -> P m)).
  assert (forall n, Q n) as Hfinal.
  {
    induction n; unfold Q in *; intros.
    - lia.
    - inversion H; subst.
      + now apply IH.
      + now apply IHn.
  }
  intros. unfold Q in Hfinal. apply Hfinal with (n:=S n). lia.
Qed.

(* These are ad-hoc. *)
(*
Fixpoint map_filter_some [A : Type] (l : list (option A)) : list A :=
  match l with
  | nil => nil
  | o :: l' => match o with 
               | Some e => (e :: map_filter_some l') 
               | None => map_filter_some l' 
               end
  end.

Lemma map_filter_some_correct [A : Type] (l : list (option A)) : 
  (map Some (map_filter_some l)) = List.filter isSome l.
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl.
    rewrite <- IH.
    now destruct x.
Qed.

Lemma find_app [A : Type] (f : A -> bool) (l1 l2 : list A) : 
  find f (l1 ++ l2) = 
  match find f l1 with
  | Some res => Some res
  | None => find f l2
  end.
Proof.
  revert l2.
  induction l1 as [ | x l1 IH ]; intros.
  - reflexivity.
  - simpl.
    destruct (f x) eqn:E.
    + reflexivity.
    + now apply IH.
Qed.
*)

(* seemingly a wrapper of find *)

Fixpoint find_first_some [A : Type] (l : list (option A)) : option A :=
  match l with
  | nil => None
  | o :: l' => match o with 
               | Some e => Some e
               | None => find_first_some l'
               end
  end.

Lemma find_first_some_correct [A : Type] (l : list (option A)) : 
  find_first_some l = match find isSome l with Some res => res | None => None end.
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl. now destruct x.
Qed.

Lemma sublist_In [A : Type] (x : A) (l1 l2 : list A) 
  (Hsub : list.sublist l1 l2) (Hin : In x l1) : In x l2.
Proof. 
  eapply list.sublist_submseteq, list.elem_of_submseteq with (x:=x) in Hsub.
  all: now apply base.elem_of_list_In.
Qed.

Corollary sublist_cons_remove [A : Type] (x : A) (l1 l2 : list A) 
  (Hsub : list.sublist (x :: l1) l2) : list.sublist l1 l2.
Proof.
  induction l2 as [ | y l2 IH ].
  - inversion Hsub.
  - inversion Hsub; subst.
    + now constructor.
    + apply list.sublist_cons.
      intuition.
Qed.

Corollary sublist_cons_In [A : Type] (x : A) (l1 l2 : list A) 
  (Hsub : list.sublist (x :: l1) l2) : In x l2.
Proof.
  eapply sublist_In; eauto.
  simpl.
  intuition.
Qed.

Lemma NoDup_concat [A : Type] (l : list (list A)) 
  (H : (@List.NoDup A) (concat l)) : Forall (@List.NoDup A) l.
Proof.
  induction l as [ | xs l IH ].
  - auto.
  - simpl in H.
    rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in H.
    destruct H as (H1 & _ & H2).
    constructor; intuition.
Qed.

Lemma NoDup_map_inj [A B : Type] (l : list A) 
  (f : A -> B) (H : List.NoDup (map f l))
  x y (Heq : f x = f y) (Hinx : In x l) (Hiny : In y l) : x = y.
Proof.
  apply base.elem_of_list_In, list.elem_of_Permutation in Hinx.
  destruct Hinx as (l' & Hperm).
  pose proof Hperm as Hperm_backup.
  apply Permutation.Permutation_map with (f:=f), Permutation.Permutation_NoDup in Hperm.
  2: assumption.
  simpl in Hperm.
  apply NoDup_cons_iff in Hperm.
  eapply Permutation.Permutation_in in Hperm_backup.
  2: apply Hiny.
  simpl in Hperm_backup.
  destruct Hperm_backup as [ | Htmp ].
  1: assumption.
  apply in_map with (f:=f) in Htmp.
  intuition congruence.
Qed.

Section TreeClock.

Context {thread : Type} (thread_eqdec : forall (t1 t2 : thread), {t1 = t2} + {t1 <> t2}).

(* OK, let's try making info_aclk not an option by making the aclk of the root useless. *)

Record nodeinfo : Type := mkInfo {
  info_tid : thread;
  info_clk : nat;
  info_aclk : nat
}.

Definition nodeinfo_eqdec (ni ni' : nodeinfo) : {ni = ni'} + {ni <> ni'}.
Proof.
  decide equality.
  all: apply Nat.eq_dec.
Qed.

Inductive treeclock : Type :=
  Node (ni : nodeinfo) (chn : list treeclock).

(* The automatically generated induction principle is useless.  *)
(* seems can be solved with "Scheme", but that would require a mutually recursive inductive type? *)

Fixpoint tc_height tc : nat := 
  let: Node _ chn := tc in 
  S (List.list_max (map tc_height chn)).

(* maybe no longer useful, but  *)
Fact tc_height_le n chn ch (Hin : In ch chn) (Hle : List.list_max (map tc_height chn) <= n) :
  tc_height ch <= n.
Proof.
  eapply list_max_le, Forall_map, List.Forall_forall in Hle.
  2: apply Hin.
  assumption.
Qed.

Fact tc_height_map_nil chn : List.list_max (map tc_height chn) <= 0 <-> chn = nil.
Proof. 
  split; intros H.
  - destruct chn as [| [(?, ?, ?) ?] ?].
    all: simpl in *; try lia; auto.
  - subst chn. simpl. lia.
Qed.

(* step-indexing is useful. *)
(* emmm, there are other approaches for establishing this, 
  (e.g., check CoqArt book; this is called ltree or rose tree in the literature)
  but anyway.  *)

Lemma treeclock_ind_bounded_height (P : treeclock -> Prop)
  (Hind : forall (ni : nodeinfo) (chn : list treeclock), 
    Forall P chn -> P (Node ni chn)) n : 
  forall (tc : treeclock) (Hh : tc_height tc <= n), P tc.
Proof.
  induction n as [ | n IH ] using nat_ind_2; intros.
  all: destruct tc as (ni & chn); simpl in Hh.
  - lia.
  - apply le_S_n, list_max_le, Forall_map in Hh. 
    apply Hind, List.Forall_impl with (P:=fun x => tc_height x <= n).
    2: assumption.
    intros.
    apply IH with (m:=n).
    + lia.
    + assumption.
Qed.

Lemma treeclock_ind_2 (P : treeclock -> Prop)
  (Hind : forall (ni : nodeinfo) (chn : list treeclock), 
    Forall P chn -> P (Node ni chn)) : 
  forall (tc : treeclock), P tc.
Proof.
  intros tc.
  apply treeclock_ind_bounded_height with (n:=tc_height tc). 
  - assumption.
  - lia.
Qed.

Fixpoint treeclock_eqb tc tc' :=
  let: Node ni chn := tc in
  let: Node ni' chn' := tc' in
  if nodeinfo_eqdec ni ni'
  then 
    (if Nat.eq_dec (length chn) (length chn')
      then 
        List.forallb (fun pp => (fst pp) (snd pp))
          (List.combine (map treeclock_eqb chn) chn')
        (* List.forallb (fun tcp => uncurry treeclock_eqb tcp)
        (List.combine chn chn') *)
        (* this does not pass the decrease check *)
      else false)
  else false.

Lemma treeclock_eqP tc : forall tc', treeclock_eqb tc tc' <-> tc = tc'.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2. 
  intros [ni' chn'].
  simpl.
  destruct (nodeinfo_eqdec ni ni') as [ <- | Hnineq ].
  2: intuition congruence.
  transitivity (chn = chn').
  2: intuition congruence.
  clear ni.
  destruct (Nat.eq_dec (length chn) (length chn')) as [ El | Hlneq ].
  2: intuition congruence.
  unfold is_true.
  rewrite -> forallb_forall.
  rewrite -> List.Forall_forall in IH.
  (* a local induction *)
  revert chn' El.
  induction chn as [ | ch chn IH' ]; intros.
  - destruct chn'.
    2: discriminate.
    intuition.
  - destruct chn' as [ | ch' chn' ].
    1: discriminate.
    simpl in El.
    injection El as El.
    simpl in IH |- *.
    pose proof (IH _ (or_introl eq_refl) ch') as Hch.
    apply IH' in El.
    2: intros x HH; apply IH; intuition.
    split; intros H.
    + f_equal.
      * specialize (H _ (or_introl eq_refl)).
        now apply Hch.
      * apply El.
        intros ? ?.
        eapply H; eauto.
    + injection H as <-.
      subst chn'.
      intros (cmp, tc') [ <- | ]; intuition.
Qed.

Definition treeclock_eqdec (tc tc' : treeclock) : {tc = tc'} + {tc <> tc'}.
Proof.
  destruct (treeclock_eqb tc tc') eqn:E.
  - apply treeclock_eqP in E.
    now left.
  - right.
    intros EE.
    apply treeclock_eqP in EE.
    intuition congruence.
Qed.

(*
(* return a ThrMap ? *)

Fixpoint tc_flatten tc :=
  let: Node ni chn := tc in ni :: (List.flat_map tc_flatten chn).

Definition thrmap_getnode thrmap t :=
  List.find (fun ni => thread_eqdec t (info_tid ni)) thrmap.

Fact thrmap_getnode_correct thrmap t ni 
  (Hres : thrmap_getnode thrmap t = Some ni) : info_tid ni = t.
Proof. apply find_some in Hres. now destruct (thread_eqdec t (info_tid ni)). Qed.

(* maybe this should be defined as a recursive process on tree ...
    but the current one also seems well. *)

Definition tc_getnode tc t :=
  thrmap_getnode (tc_flatten tc) t.

Fact tc_getnode_correct tc t ni 
  (Hres : tc_getnode tc t = Some ni) : info_tid ni = t.
Proof. now apply thrmap_getnode_correct in Hres. Qed.

Lemma tc_getnode_step ni chn t :
  tc_getnode (Node ni chn) t =
  if thread_eqdec t (info_tid ni)
  then Some ni
  else thrmap_getnode (List.flat_map tc_flatten chn) t.
Proof.
  unfold tc_getnode.
  simpl.
  now destruct (thread_eqdec t (info_tid ni)).
Qed.

Definition thrmap_getclk thrmap t :=
  match thrmap_getnode thrmap t with
  | Some res => info_clk res
  | _ => 0
  end.
*)
Definition tc_init t := Node (mkInfo t 0 0) nil.

Definition tc_rootinfo tc :=
  let: Node ni _ := tc in ni.

Definition tc_rootchn tc :=
  let: Node _ chn := tc in chn.

Definition tc_roottid tc := info_tid (tc_rootinfo tc).

Definition tc_rootclk tc := info_clk (tc_rootinfo tc).

Definition tc_rootaclk tc := info_aclk (tc_rootinfo tc).

Global Arguments tc_roottid !_ /.
Global Arguments tc_rootclk !_ /.
Global Arguments tc_rootaclk !_ /.

Fixpoint tc_getnode t tc :=
  let: Node ni chn := tc in 
  if thread_eqdec t (info_tid ni)
  then Some tc
  else find_first_some (map (tc_getnode t) chn).

(* only for some domain-based reasoning; not for finding *)

Fixpoint tc_flatten tc :=
  let: Node ni chn := tc in tc :: (List.flat_map tc_flatten chn).

Definition subtc tc1 tc2 : Prop := In tc1 (tc_flatten tc2).

Fact tc_flatten_in_ch_chn tc ch chn 
  (Hin_ch : In ch chn) (Hin : In tc (tc_flatten ch)) : In tc (flat_map tc_flatten chn).
Proof.
  rewrite -> flat_map_concat_map, -> in_concat.
  setoid_rewrite -> in_map_iff.
  firstorder.
Qed.

Fact tc_flatten_in_chn_ch tc chn (Hin : In tc (flat_map tc_flatten chn)) :
  exists ch, In ch chn /\ In tc (tc_flatten ch).
Proof.
  rewrite -> flat_map_concat_map, -> in_concat in Hin.
  setoid_rewrite -> in_map_iff in Hin.
  destruct Hin as (? & (ch & <- & Hin_ch) & Hin).
  firstorder.
Qed.

(* the same as paper, use 0 as default clk *)

Definition tc_getclk t tc :=
  match tc_getnode t tc with
  | Some res => tc_rootclk res
  | _ => 0
  end.

(* Forall over all subtrees *)
(* it is hard to define this as a recursive function, so use indprop instead *)

Inductive Foralltc (P : treeclock -> Prop) : treeclock -> Prop :=
  Foralltc_intro : forall ni chn, 
    P (Node ni chn) -> Forall (Foralltc P) chn -> Foralltc P (Node ni chn). 

Fact Foralltc_cons_iff P ni chn :
  Foralltc P (Node ni chn) <-> (P (Node ni chn) /\ Forall (Foralltc P) chn).
Proof.
  split; intros.
  - now inversion H.
  - now apply Foralltc_intro.
Qed.

Fact Foralltc_self P tc (H : Foralltc P tc) : P tc.
Proof. destruct tc. now apply Foralltc_cons_iff in H. Qed.

Lemma Foralltc_impl (P Q : treeclock -> Prop) (Hpq : forall tc, P tc -> Q tc) tc 
  (H : Foralltc P tc) : Foralltc Q tc.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  rewrite -> Foralltc_cons_iff in H |- *.
  destruct H as (H & H0).
  split.
  - now apply Hpq.
  - rewrite -> Forall_forall in *. 
    firstorder. 
Qed.

Lemma Foralltc_and (P Q : treeclock -> Prop) tc :
  Foralltc (fun tc => P tc /\ Q tc) tc <-> Foralltc P tc /\ Foralltc Q tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> ! Foralltc_cons_iff, -> ! List.Forall_forall.
  rewrite -> List.Forall_forall in IH.
  firstorder.
Qed.

Lemma Foralltc_idempotent (P : treeclock -> Prop) tc :
  Foralltc (Foralltc P) tc <-> Foralltc P tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> ! Foralltc_cons_iff, -> ! List.Forall_forall.
  rewrite -> List.Forall_forall in IH.
  firstorder.
Qed.

Lemma Foralltc_Forall_subtree (P : treeclock -> Prop) tc :
  Foralltc P tc <-> Forall P (tc_flatten tc).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> ! Foralltc_cons_iff, List.Forall_cons_iff, -> ! List.Forall_forall.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  apply and_iff_compat_l.
  split; intros H.
  - intros sub Hin.
    apply tc_flatten_in_chn_ch in Hin.
    firstorder.
  - intros ch Hin_ch.
    apply IH.
    1: assumption.
    intros sub Hin.
    eapply H, tc_flatten_in_ch_chn; eauto.
Qed.

Inductive prefixtc : treeclock -> treeclock -> Prop :=
  prefixtc_intro : forall ni chn chn_sub prefix_chn, 
    list.sublist chn_sub chn ->
    Forall2 prefixtc prefix_chn chn_sub ->
    prefixtc (Node ni prefix_chn) (Node ni chn).

Fact prefixtc_inv ni1 ni2 chn1 chn2 (Hprefix: prefixtc (Node ni1 chn1) (Node ni2 chn2)) :
  ni1 = ni2 /\ exists chn2_sub, list.sublist chn2_sub chn2 /\ Forall2 prefixtc chn1 chn2_sub.
Proof. inversion Hprefix; subst. firstorder. Qed.

#[export] Instance prefixtc_refl : Reflexive prefixtc.
Proof.
  hnf.
  intros tc.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  econstructor.
  1: reflexivity.
  now apply list.Forall_Forall2_diag.
Qed.

Lemma prefixtc_nil_l ni chn : prefixtc (Node ni nil) (Node ni chn).
Proof.
  econstructor.
  2: reflexivity.
  apply list.sublist_nil_l.
Qed.

Lemma prefixtc_flatten_sublist tc1 tc2 (Hprefix : prefixtc tc1 tc2) :
  list.sublist (map tc_rootinfo (tc_flatten tc1)) (map tc_rootinfo (tc_flatten tc2)).
Proof.
  revert tc2 Hprefix.
  induction tc1 as [ni chn1 IH] using treeclock_ind_2; intros.
  destruct tc2 as [ni2 chn2].
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (<- & (chn2_sub & Hsub & Hprefix)).
  simpl.
  apply list.sublist_skip.
  (* seems only induction works here ... *)
  revert chn1 IH Hprefix.
  induction Hsub as [ | ch2 chn2_sub chn2 Hsub IHsub | ch2 chn2_sub chn2 Hsub IHsub ]; intros.
  - destruct chn1; inversion Hprefix.
    reflexivity.
  - destruct chn1 as [ | ch1 chn1 ]. 
    1: inversion Hprefix.
    apply list.Forall2_cons in Hprefix.
    destruct Hprefix as (Hpf & Hprefix).
    apply Forall_cons_iff in IH.
    destruct IH as (IHsingle & IH).
    simpl.
    rewrite -> ! map_app.
    apply list.sublist_app.
    all: firstorder.
  - simpl.
    rewrite -> map_app.
    apply list.sublist_inserts_l.
    firstorder.
Qed.

Fact tc_getnode_some t tc res
  (Hres : tc_getnode t tc = Some res) : In res (tc_flatten tc) /\ tc_roottid res = t.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  simpl in Hres.
  destruct (thread_eqdec t u) as [ <- | Hneq ].
  1:{
    simpl.
    injection Hres as <-.
    intuition.
  }
  rewrite -> find_first_some_correct in Hres.
  destruct (find isSome (map (tc_getnode t) chn)) as [ res_chn | ] eqn:E.
  - apply find_some in E.
    destruct res_chn; [ injection Hres as -> | discriminate ].
    destruct E as (E & _).
    (* OK. after some attempts now I do not think I can solve this easily. *)
    simpl.
    rewrite -> in_map_iff in E.
    pose proof tc_flatten_in_ch_chn.
    rewrite -> List.Forall_forall in IH.
    firstorder.
  - discriminate.
Qed.

(* just an excerpt of the proof above ... *)

Fact tc_getnode_some_list t chn res
  (Hres : In (Some res) (map (tc_getnode t) chn)) : In res (flat_map tc_flatten chn) /\ tc_roottid res = t.
Proof.
  rewrite -> in_map_iff in Hres.
  destruct Hres as (ch & Hres & Hin_ch).
  apply tc_getnode_some in Hres.
  pose proof tc_flatten_in_ch_chn.
  firstorder.
Qed.

Fact tc_getnode_complete t tc sub (Hin : In sub (tc_flatten tc))
  (Et : tc_roottid sub = t) : exists res, tc_getnode t tc = Some res.
Proof.
  revert sub Hin Et.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  simpl in Hin |- *.
  destruct (thread_eqdec t u) as [ <- | Hneq ].
  1: eauto.
  destruct Hin as [ <- | Hin ].
  1: simpl in Et; congruence.
  apply tc_flatten_in_chn_ch in Hin.
  destruct Hin as (ch & Hin_ch & Hin_sub).
  rewrite -> List.Forall_forall in IH.
  specialize (IH _ Hin_ch _ Hin_sub Et).
  destruct IH as (res_ch & IH).
  rewrite -> find_first_some_correct.
  destruct (find isSome (map (tc_getnode t) chn)) as [ res_chn | ] eqn:E.
  - apply find_some in E.
    destruct res_chn; [ eauto | intuition discriminate ].
  - eapply find_none in E; eauto.
    2: apply in_map, Hin_ch.
    now destruct (tc_getnode t ch).
Qed.

Fact tc_getnode_complete_nodup t tc sub (Hin : In sub (tc_flatten tc))
  (Et : tc_roottid sub = t) (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc))) : 
  tc_getnode t tc = Some sub.
Proof.
  pose proof (tc_getnode_complete _ _ _ Hin Et) as (res & Hres).
  pose proof Hres as Hres_backup.
  apply tc_getnode_some in Hres.
  destruct Hres as (Hin' & <-).
  eapply NoDup_map_inj in Hnodup.
  2: apply Et.
  2-3: assumption.
  now subst.
Qed.

(* just an excerpt of the proof above ... *)

Fact tc_getnode_complete_list t chn sub
  (Hin_flat : In sub (flat_map tc_flatten chn))
  (Et : tc_roottid sub = t) : exists res, In (Some res) (map (tc_getnode t) chn).
Proof.
  apply tc_flatten_in_chn_ch in Hin_flat.
  destruct Hin_flat as (ch & Hin_ch & Hin_flat).
  eapply tc_getnode_complete in Hin_flat.
  2: apply Et.
  destruct Hin_flat as (res & Hin_flat).
  setoid_rewrite -> in_map_iff.
  eauto.
Qed.

Fact tc_getnode_complete_nodup_list t chn sub
  (Hin_flat : In sub (flat_map tc_flatten chn))
  (Et : tc_roottid sub = t) 
  (Hnodup : List.NoDup (map tc_roottid (flat_map tc_flatten chn))) : 
  (* the final statement can be stronger ... *)
  forall ch res, In ch chn -> tc_getnode t ch = Some res -> sub = res.
Proof.
  pose proof (tc_getnode_complete_list _ _ _ Hin_flat Et) as (res & Hres).
  pose proof Hres as Hres_backup.
  apply tc_getnode_some_list in Hres.
  destruct Hres as (Hin_flat' & <-).
  pose proof Hnodup as Hnodup_backup.
  eapply NoDup_map_inj in Hnodup.
  2: apply Et.
  2-3: assumption.
  subst.
  rewrite -> in_map_iff in Hres_backup.
  destruct Hres_backup as (ch & Hres & Hin_ch).
  intros ch' res' Hin_ch' Hres'.
  apply tc_getnode_some in Hres, Hres'.
  destruct Hres' as (Hin' & Et').
  assert (In res' (flat_map tc_flatten chn)) by (eapply tc_flatten_in_ch_chn; eauto).
  eapply NoDup_map_inj in Hnodup_backup.
  2: apply Et'.
  2-3: assumption.
  now subst.
Qed.

Corollary tc_getnode_none t tc (Hres : tc_getnode t tc = None) : 
  forall sub, In sub (tc_flatten tc) -> tc_roottid sub <> t.
Proof.
  intros sub Hin <-.
  apply tc_getnode_complete with (t:=(tc_roottid sub)) in Hin; auto.
  firstorder congruence.
Qed.

(* domain inclusion property of prefix *)

Lemma dom_incl_tc_getnode_impl tc tc' 
  (Hincl : incl (map tc_rootinfo (tc_flatten tc)) (map tc_rootinfo (tc_flatten tc')))
  t res (Hres : tc_getnode t tc = Some res) : exists res', tc_getnode t tc' = Some res'.
Proof.
  (* destruct (tc_getnode t tc) as [ res | ] eqn:E.
  2: discriminate. *)
  apply tc_getnode_some in Hres.
  destruct Hres as (Hin & Et).
  hnf in Hincl.
  repeat setoid_rewrite -> in_map_iff in Hincl.
  specialize (Hincl (tc_rootinfo res)).
  removehead Hincl.
  2: now exists res.
  destruct Hincl as (res' & Einfo & Hin').
  assert (tc_roottid res' = t) as Et' by (destruct res as [(?, ?, ?) ?], res' as [(?, ?, ?) ?]; simpl in *; intuition congruence).
  eapply tc_getnode_complete in Hin'; eauto.
Qed.

Corollary prefix_tc_getnode_impl tc tc' (Hprefix : prefixtc tc tc')
  t res (Hres : tc_getnode t tc = Some res) : exists res', tc_getnode t tc' = Some res'.
Proof.
  revert Hres.
  apply dom_incl_tc_getnode_impl.
  hnf.
  intros ?.
  now apply sublist_In, prefixtc_flatten_sublist.
Qed.

(* since this is for prefix, maybe not entire subtree equal *)

Corollary prefix_tc_getnode_nodup_sameinfo tc tc' (Hprefix : prefixtc tc tc')
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc')))
  t res (Hres : tc_getnode t tc = Some res) 
  res' (Hres' : tc_getnode t tc' = Some res') : tc_rootinfo res = tc_rootinfo res'.
Proof.
  pose proof (tc_getnode_some _ _ _ Hres) as (Hin & <-).
  pose proof (tc_getnode_some _ _ _ Hres') as (Hin' & Et).
  apply in_map with (f:=tc_rootinfo) in Hin, Hin'.
  pose proof (prefixtc_flatten_sublist _ _ Hprefix) as HH.
  eapply sublist_In in Hin.
  2: apply HH.
  unfold tc_roottid in Hnodup.
  rewrite <- map_map in Hnodup.
  eapply NoDup_map_inj in Hnodup.
  2: apply Et.
  2-3: assumption.
  congruence.
Qed.

(*
Notation "tc '@' t" := (tc_getnode t tc) (at level 50).
Notation "tc '@clk' t" := (tc_getclk t tc) (at level 50).
*)

(*
Fact tc_thrmap_getclk_same tc t : 
  tc_getclk tc t = thrmap_getclk (tc_flatten tc) t.
Proof. auto. Qed.

Lemma tc_getclk_step ni chn t :
  tc_getclk (Node ni chn) t =
  if thread_eqdec t (info_tid ni)
  then info_clk ni
  else thrmap_getclk (List.flat_map tc_flatten chn) t.
Proof.
  unfold tc_getclk.
  rewrite -> tc_getnode_step.
  now destruct (thread_eqdec t (info_tid ni)).
Qed.

Lemma thrmap_getnode_app_step t thrmap1 thrmap2 :
  thrmap_getnode (thrmap1 ++ thrmap2) t =
  match thrmap_getnode thrmap1 t with
  | Some ni => Some ni
  | None => thrmap_getnode thrmap2 t
  end.
Proof.
  unfold thrmap_getnode.
  now rewrite -> ! find_app.
Qed.

Corollary thrmap_getclk_app_step t thrmap1 thrmap2 :
  thrmap_getclk (thrmap1 ++ thrmap2) t =
  match thrmap_getnode thrmap1 t with
  | Some ni => info_clk ni
  | None => thrmap_getclk thrmap2 t
  end.
Proof.
  unfold thrmap_getclk.
  rewrite -> thrmap_getnode_app_step.
  now destruct (thrmap_getnode thrmap1 t).
Qed.

Corollary thrmap_getclk_cons_step t tc thrmap :
  thrmap_getclk (tc_flatten tc ++ thrmap) t =
  match tc_getnode tc t with
  | Some ni => info_clk ni
  | None => thrmap_getclk thrmap t
  end.
Proof. now rewrite -> thrmap_getclk_app_step. Qed. 

(* get clk from a list of trees = map_filter_some *)

Lemma tc_flatten_getclk t chn :
  thrmap_getclk (List.flat_map tc_flatten chn) t = 
  match map_filter_some (map (fun tc => tc_getnode tc t) chn) with
  | nil => 0
  | ni :: _ => info_clk ni
  end.
Proof.
  induction chn as [ | ch chn IH ].
  - reflexivity.
  - simpl.
    rewrite -> thrmap_getclk_cons_step, IH.
    now destruct (tc_getnode ch t) eqn:E.
Qed.
*)

(*
Definition tid_in_tree_dec t tc :=
  in_dec thread_eqdec t (map info_tid (tc_flatten tc)). 
*)

Definition tid_in_tree t tc : bool := isSome (tc_getnode t tc).

(* return a tree instead of a stack? *)
(* compute prefix(tc') that should be updated in tc; assume that 
    at least the root of tc' must be updated in tc
*)
(* considering the simulation with imperative code, maybe this process 
    should not be too declarative. therefore takes a recursion on list
    as a sub-procedure
*)

Fixpoint tc_get_updated_nodes_join tc tc' : treeclock :=
  let fix tc_get_updated_nodes_join_aux tc u' chn_u' : list treeclock :=
  match chn_u' with
  | nil => nil
  | tc' :: chn_u'' => 
    let: Node (mkInfo v' clk_v' aclk_v') chn_v' := tc' in
    (* <? is slightly hard to use *)
    if clk_v' <=? (tc_getclk v' tc)
    then 
      (if aclk_v' <=? (tc_getclk u' tc)
        then nil
        else (tc_get_updated_nodes_join_aux tc u' chn_u''))
    else (tc_get_updated_nodes_join tc tc') :: (tc_get_updated_nodes_join_aux tc u' chn_u'')
  end in
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (info_tid info_u') chn_u')
.

(* TODO this is awkward. the inner aux must be an external function to work with
    since implementing it as a mutual recursion does not pass the arg decrease check *)

Fixpoint tc_get_updated_nodes_join_aux tc u' chn_u' : list treeclock :=
  match chn_u' with
  | nil => nil
  | tc' :: chn_u'' => 
    let: Node (mkInfo v' clk_v' aclk_v') chn_v' := tc' in
    if clk_v' <=? (tc_getclk v' tc)
    then 
      (if aclk_v' <=? (tc_getclk u' tc)
        then nil
        else (tc_get_updated_nodes_join_aux tc u' chn_u''))
    else (tc_get_updated_nodes_join tc tc') :: (tc_get_updated_nodes_join_aux tc u' chn_u'')
  end.

Lemma tc_get_updated_nodes_join_eta tc tc' : 
  tc_get_updated_nodes_join tc tc' = 
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (info_tid info_u') chn_u').
Proof. destruct tc'. reflexivity. Qed.

Tactic Notation "tc_get_updated_nodes_join_unfold" :=
  cbn delta -[tc_get_updated_nodes_join] iota beta;
  rewrite -> tc_get_updated_nodes_join_eta.

Tactic Notation "tc_get_updated_nodes_join_unfold" "in_" hyp(H) :=
  cbn delta -[tc_get_updated_nodes_join] iota beta in H;
  rewrite -> tc_get_updated_nodes_join_eta in H.

(* given a tree and a list of targets, return a pivot tree and a list of splitted trees *)

Fixpoint tc_detach_nodes subtree_tc' tc : treeclock * list treeclock :=
  let: Node ni chn := tc in
  let: (new_chn, res) := List.split (map (tc_detach_nodes subtree_tc') chn) in
  let: (res', new_chn') := List.partition (fun tc' => tid_in_tree (tc_roottid tc') subtree_tc')
    new_chn in
  (Node ni new_chn', (List.concat res) ++ res').

(* return a reconstructed tree to be added into the pivot *)

Fixpoint tc_attach_nodes forest tc' : treeclock :=
  let: Node info_u' chn' := tc' in
  (* try finding a tree in the forest with the same root thread *)
  let: u_pre := List.find (fun tc => thread_eqdec (tc_roottid tc) (info_tid info_u')) forest in
  let: chn_u := (match u_pre with Some u => tc_rootchn u | None => nil end) in
  (* for u', inherit clk and aclk anyway; prepend all children of u' *)
  Node info_u' ((map (tc_attach_nodes forest) chn') ++ chn_u).

Definition tc_join tc tc' :=
  let: mkInfo z' clk_z' aclk_z' := tc_rootinfo tc' in
  if clk_z' <=? (tc_getclk z' tc)
  then tc
  else 
    let: subtree_tc' := tc_get_updated_nodes_join tc tc' in
    let: (pivot, forest) := tc_detach_nodes subtree_tc' tc in
    let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
    let: Node info_z chn_z := pivot in 
    Node info_z ((Node (mkInfo w clk_w (info_clk info_z)) chn_w) :: chn_z).

(*
Lemma Foralltc_Forall_subtree (P : treeclock -> Prop) tc :
  Foralltc P tc <-> Forall P (tc_flatten tc).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> ! Foralltc_cons_iff, List.Forall_cons_iff, -> ! List.Forall_forall.
  rewrite -> List.Forall_forall in IH.
  firstorder.
*)

(* switch between Forall over nodeinfos or Foralltc over all subtrees *)
(*
Lemma tc_Forall_Foralltc_iff (P : treeclock -> Prop) (Q : nodeinfo -> Prop)
  (Hpq : forall ni chn, P (Node ni chn) <-> Q ni) :
  forall tc, Forall Q (tc_flatten tc) <-> Foralltc P tc.
Proof.
  intros tc.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> Forall_cons_iff, -> Forall_flat_map, -> Foralltc_cons_iff, -> Hpq.
  apply and_iff_compat_l.
  split; intros H.
  all: rewrite -> Forall_forall in H, IH |- *.
  all: firstorder.
Qed.

Corollary tc_Forall_Foralltc_iff_chn (Q : nodeinfo -> Prop) :
  forall chn, Forall (Foralltc (fun tc' => Q (tc_rootinfo tc'))) chn <-> 
    Forall Q (flat_map tc_flatten chn).
Proof.
  intros chn.
  rewrite -> Forall_flat_map, -> ! Forall_forall.
  setoid_rewrite -> tc_Forall_Foralltc_iff with (Q:=Q) (P:=(fun tc' => Q (tc_rootinfo tc'))).
  2: reflexivity.
  reflexivity.
Qed.
*)
(* treeclock specific properties *)
(*
Definition tc_ge' (thrmap : list nodeinfo) tc : Prop :=
  Foralltc (fun tc' => let: Node (mkInfo w clk_w _) _ := tc' in 
    clk_w <= thrmap_getclk thrmap w) tc.
*)
Definition tc_ge (tc_larger tc : treeclock) : Prop := 
  Foralltc (fun tc'' => let: Node (mkInfo w clk_w _) _ := tc'' in 
    clk_w <= tc_getclk w tc_larger) tc.
(*
Definition dmono_single (thrmap : list nodeinfo) tc : Prop :=
  let: Node (mkInfo u clk_u _) _ := tc in
  clk_u <= (thrmap_getclk thrmap u) -> Foralltc (tc_ge' thrmap) tc.

Definition imono_single (thrmap : list nodeinfo) tc: Prop :=
  let: Node (mkInfo u _ _) chn := tc in
  Forall (fun tc' => let: Node (mkInfo v _ aclk_v) chn' := tc' in
    aclk_v <= (thrmap_getclk thrmap u) -> Foralltc (tc_ge' thrmap) tc') chn. 

Record tc_respect' tc (thrmap : list nodeinfo) : Prop := {
  dmono : Foralltc (dmono_single thrmap) tc;
  imono : Foralltc (imono_single thrmap) tc
}.

*)

Definition dmono_single (tc_larger : treeclock) tc : Prop :=
  let: Node (mkInfo u clk_u _) _ := tc in
  clk_u <= (tc_getclk u tc_larger) -> tc_ge tc_larger tc.

Definition imono_single (tc_larger : treeclock) tc: Prop :=
  let: Node (mkInfo u _ _) chn := tc in
  Forall (fun tc_v => let: Node (mkInfo v _ aclk_v) _ := tc_v in
    aclk_v <= (tc_getclk u tc_larger) -> tc_ge tc_larger tc_v) chn. 

Record tc_respect tc (tc' : treeclock) : Prop := {
  dmono : Foralltc (dmono_single tc') tc;
  imono : Foralltc (imono_single tc') tc
}.

Fact tc_respect_chn ni chn tc' (H : tc_respect (Node ni chn) tc') :
  Forall (fun ch => tc_respect ch tc') chn.
Proof.
  rewrite -> List.Forall_forall.
  intros ch Hin.
  constructor.
  1: apply dmono in H.
  2: apply imono in H.
  all: rewrite -> Foralltc_cons_iff, List.Forall_forall in H.
  all: firstorder.
Qed.

(* Definition tc_respect tc tc' := tc_respect' tc (tc_flatten tc'). *)

Definition tc_chn_aclk_decsorted tc := 
  let: Node _ chn := tc in
  StronglySorted ge (map tc_rootaclk chn). 

Definition tc_chn_aclk_ub tc: Prop :=
  let: Node (mkInfo _ clk_u _) chn := tc in
  Forall (fun tc' => tc_rootaclk tc' <= clk_u) chn. 

(* TODO make this record or class? *)

Record tc_shape_inv tc : Prop := {
  (* tid_nodup: List.NoDup (map info_tid (tc_flatten tc)); *)
  tid_nodup: List.NoDup (map tc_roottid (tc_flatten tc));
  aclk_upperbound: Foralltc tc_chn_aclk_ub tc;
  aclk_decsorted: Foralltc tc_chn_aclk_decsorted tc;
  clk_lowerbound: Foralltc (fun tc' => 0 < tc_rootclk tc') tc
}.

Lemma tid_nodup_chn_ch chn ch
  (H : List.NoDup (map tc_roottid (flat_map tc_flatten chn)))
  (Hin : In ch chn) : List.NoDup (map tc_roottid (tc_flatten ch)).
Proof.
  rewrite -> flat_map_concat_map, -> concat_map, -> map_map in H.
  apply NoDup_concat in H.
  rewrite -> List.Forall_map, List.Forall_forall in H.
  now apply H.
Qed.

Lemma tid_nodup_Foralltc_id tc : 
  List.NoDup (map tc_roottid (tc_flatten tc)) <->
  Foralltc (fun tc => List.NoDup (map tc_roottid (tc_flatten tc))) tc.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> Foralltc_cons_iff.
  simpl.
  split; [ | intuition ].
  intros H.
  split.
  1: assumption.
  rewrite -> List.Forall_forall in IH |- *.
  intros tc Hin.
  rewrite <- IH.
  2: assumption.
  apply NoDup_cons_iff in H.
  destruct H as (_ & H).
  now eapply tid_nodup_chn_ch; eauto.
Qed.

Fact tc_shape_inv_conj_iff tc : 
  tc_shape_inv tc <-> 
    (List.NoDup (map tc_roottid (tc_flatten tc))
    /\ Foralltc tc_chn_aclk_ub tc
    /\ Foralltc tc_chn_aclk_decsorted tc
    /\ Foralltc (fun tc' => 0 < tc_rootclk tc') tc).
Proof.
  split.
  - now intros [? ? ? ?].
  - intros.
    now constructor.
Qed.

Lemma tc_shape_inv_chn ni chn (Hshape : tc_shape_inv (Node ni chn)) :
  Forall (Foralltc tc_shape_inv) chn.
Proof.
  apply List.Forall_forall.
  intros ch Hin.
  eapply Foralltc_impl.
  1: apply tc_shape_inv_conj_iff.
  apply Foralltc_and; split.
  2: apply Foralltc_and; split.
  3: apply Foralltc_and; split.
  2-4: rewrite -> Foralltc_idempotent.
  2: apply aclk_upperbound in Hshape.
  3: apply aclk_decsorted in Hshape.
  4: apply clk_lowerbound in Hshape.
  2-4: apply Foralltc_cons_iff in Hshape.
  2-4: rewrite -> List.Forall_forall in Hshape.
  2-4: firstorder.
  apply tid_nodup in Hshape.
  simpl in Hshape.
  apply NoDup_cons_iff in Hshape.
  destruct Hshape as (_ & Hnodup).
  now eapply tid_nodup_Foralltc_id, tid_nodup_chn_ch; eauto.
Qed.

(* a condition on arbitrary thrmap_getnode *)
(*
Lemma thrmap_getnode_iff Q thrmap (Hnodup : List.NoDup (map info_tid thrmap)) : 
  (forall t, match thrmap_getnode thrmap t with Some res => Q res | None => True end) <-> 
  Forall Q thrmap.
Proof.
  induction thrmap as [ | ni thrmap IH ].
  - simpl.
    intuition.
  - simpl in Hnodup |- *.
    rewrite -> NoDup_cons_iff in Hnodup.
    destruct Hnodup as (Hnotin & Hnodup).
    specialize (IH Hnodup).
    rewrite -> Forall_cons_iff, <- IH.
    split.
    + intros H.
      split.
      * specialize (H (info_tid ni)).
        now destruct (thread_eqdec (info_tid ni) (info_tid ni)).
      * intros t.
        specialize (H t).
        destruct (thread_eqdec t (info_tid ni)) as [ -> | Hneq ].
        --(* None; troublesome though *)
          unfold thrmap_getnode.
          match goal with |- (match ?e with Some _ => _ | None => _ end) => destruct e eqn:E end.
          2: auto.
          apply find_some in E.
          destruct E as (Hin & E).
          destruct (thread_eqdec (info_tid ni) (info_tid n)) as [ Htideq | ].
          2: discriminate.
          rewrite -> Htideq, -> in_map_iff in Hnotin.
          firstorder.
        --now simpl in H.
    + intros (Hq & H) t.
      destruct (thread_eqdec t (info_tid ni)) as [ -> | Hneq ]; simpl.
      * assumption.
      * now apply H.
Qed.

Corollary tc_getnode_iff Q tc (Hnodup : List.NoDup (map info_tid (tc_flatten tc))) :
  (forall t, match tc_getnode tc t with Some res => Q res | None => True end) <-> 
  Forall Q (tc_flatten tc).
Proof. now apply thrmap_getnode_iff. Qed.

Corollary thrmap_getclk_le_Foralltc_iff thrmap (getclk : thread -> nat) (Hnodup : List.NoDup (map info_tid thrmap)) :
  (forall t, thrmap_getclk thrmap t <= getclk t) <-> 
  Forall (fun ni => info_clk ni <= getclk (info_tid ni)) thrmap.
Proof.
  rewrite <- thrmap_getnode_iff.
  2: assumption.
  unfold thrmap_getclk.
  split; intros H t.
  all: specialize (H t).
  all: destruct (thrmap_getnode thrmap t) as [ (?, ?, ?) | ] eqn:E.
  all: auto; try lia.
  all: apply thrmap_getnode_correct in E; now subst t.
Qed.

Corollary tc_getclk_le_Foralltc_iff tc (getclk : thread -> nat) (Hnodup : List.NoDup (map info_tid (tc_flatten tc))) :
  (forall t, tc_getclk tc t <= getclk t) <-> 
  Foralltc (fun tc' => let: Node (mkInfo w clk_w _) _ := tc' in 
    clk_w <= getclk w) tc.
Proof.
  setoid_rewrite -> thrmap_getclk_le_Foralltc_iff.
  2: assumption.
  rewrite <- tc_Forall_Foralltc_iff with (Q:=fun ni => info_clk ni <= getclk (info_tid ni)).
  1: reflexivity.
  now intros (?, ?, ?) _.
Qed.
*)

Lemma tc_get_updated_nodes_join_aux_result tc u' chn_u'
  (Haclk_impl_P : forall tc', In tc' chn_u' -> 
    tc_rootaclk tc' <= (tc_getclk u' tc) -> 
    tc_rootclk tc' <= (tc_getclk (tc_roottid tc') tc)) 
  (Hsorted: StronglySorted ge (map tc_rootaclk chn_u')) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc u' chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => In tc' chn_u'' <-> 
      (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc') chn_u').
Proof.
  induction chn_u' as [ | tc_v' chn_u' IH ].
  - exists nil.
    intuition.
  - simpl in Haclk_impl_P, Hsorted.
    apply StronglySorted_inv in Hsorted.
    destruct Hsorted as (Hsorted & Hallle).
    destruct tc_v' as [(v', clk_v', aclk_v') chn_v'] eqn:Etc_v'.
    simpl in Hallle.
    rewrite <- Etc_v' in *.
    removehead IH.
    2:{
      intros tc' ?.
      specialize (Haclk_impl_P tc').
      apply Haclk_impl_P.
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
      destruct (aclk_v' <=? tc_getclk u' tc) eqn:Ecmp_aclk_v'.
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
          specialize (Haclk_impl_P _ (or_intror Hin')).
          removehead Haclk_impl_P.
          2: lia.
          exfalso.
          revert Haclk_impl_P.
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
      exists (tc_v' :: chn_u'').
      split.
      1: now constructor.
      split; [ | split; [ split | ] ].
      * rewrite -> Etc_v'.
        tc_get_updated_nodes_join_unfold.
        now f_equal.
      * simpl.
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
        intuition.
Qed.

(* a weaker result; did not find a good way to combine with the statement above *)

Lemma tc_get_updated_nodes_join_aux_result_submap tc u chn :
  exists chn', list.sublist chn' chn /\
    (tc_get_updated_nodes_join_aux tc u chn) = map (tc_get_updated_nodes_join tc) chn'.
Proof.
  induction chn as [ | ch chn IH ]; intros.
  - now exists nil.
  - tc_get_updated_nodes_join_unfold.
    destruct ch as [(v, clk_v, aclk_v) chn_v] eqn:Ech.
    cbn.
    destruct IH as (chn' & Hsub & ->).
    rewrite <- Ech.
    destruct (clk_v <=? tc_getclk v tc) eqn:E.
    + destruct (aclk_v <=? tc_getclk u tc) eqn:E2.
      * exists nil.
        split; [ apply list.sublist_nil_l | reflexivity ].
      * exists chn'.
        split; [ now constructor | reflexivity ].
    + exists (ch :: chn').
      split; [ now constructor | ].
      simpl.
      now subst ch.
Qed.

Corollary tc_get_updated_nodes_join_is_prefix tc tc' :
  prefixtc (tc_get_updated_nodes_join tc tc') tc'.
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  tc_get_updated_nodes_join_unfold.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_submap tc u' chn')
    as (chn'' & Hsub & ->).
  econstructor.
  1: apply Hsub.
  revert chn' IH Hsub.
  induction chn'' as [ | ch chn'' IH' ]; intros.
  - now simpl.
  - simpl.
    constructor.
    + apply sublist_cons_In in Hsub.
      rewrite -> Forall_forall in IH.
      firstorder.
    + apply sublist_cons_remove in Hsub.
      firstorder.
Qed.

Lemma tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn_u' 
  (Hshape_tc' : tc_shape_inv (Node (mkInfo u' clk_u' aclk_u') chn_u')) 
  (Hrespect : tc_respect (Node (mkInfo u' clk_u' aclk_u') chn_u') tc) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc u' chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => ~ In tc' chn_u'' <-> tc_ge tc tc') chn_u') /\
    (Forall (fun tc' => In tc' chn_u'' <-> (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc') chn_u').
Proof.
  pose proof (tc_get_updated_nodes_join_aux_result tc u' chn_u') as H.
  removehead H.
  2:{
    intros tc_v' Hin' Hle.
    (* use imono *)
    apply imono, Foralltc_cons_iff in Hrespect.
    destruct Hrespect as (Himono & _).
    simpl in Himono.
    rewrite -> List.Forall_forall in Himono.
    specialize (Himono _ Hin').
    destruct tc_v' as [(v', clk_v', aclk_v') chn_v'].
    simpl in Hle, Himono |- *.
    now apply Himono, Foralltc_self in Hle.
  }
  removehead H.
  2: now apply aclk_decsorted, Foralltc_cons_iff in Hshape_tc'.
  destruct H as (chn_u'' & Hsub & Hres & Halllt).
  exists chn_u''.
  split.
  1: assumption.
  split.
  1: assumption.
  split.
  2: assumption.
  rewrite -> List.Forall_forall in Halllt |- *.
  intros ch Hin.
  specialize (Halllt _ Hin).
  rewrite -> Halllt, Nat.nlt_ge.
  split; intros H.
  2: apply Foralltc_self in H; now destruct ch as [(?, ?, ?) ?].
  (* use dmono *)
  apply dmono, Foralltc_cons_iff in Hrespect.
  destruct Hrespect as (_ & Hdmono).
  rewrite -> List.Forall_forall in Hdmono.
  specialize (Hdmono _ Hin).
  apply Foralltc_self in Hdmono.
  destruct ch as [(?, ?, ?) ?].
  firstorder.
Qed.

(* a node is in the gathered prefix iff it needs update *)

Lemma tc_get_updated_nodes_join_sound : forall tc' (Hshape_tc': tc_shape_inv tc') 
  tc (Hrespect: tc_respect tc' tc) 
  (* root clk le is NECESSARY for sound and completeness since root is always in the gathered prefix *)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') t,
  tc_getnode t (tc_get_updated_nodes_join tc tc') <-> 
  tc_getclk t tc < tc_getclk t tc'.
Proof.
  intros tc' Hshape_tc'.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  unfold tc_getclk at 2.
  cbn.
  destruct (thread_eqdec t u') as [ <- | Htneq ] eqn:Etdec.
  1: simpl; unfold isSome; intuition.
  (* get sub inv *)
  assert (NoDup (map tc_roottid (flat_map tc_flatten chn'))) as Hnodup_chn'
    by (now apply tid_nodup, NoDup_cons_iff in Hshape_tc').
  (* get the result of tc_get_updated_nodes_join_aux *)
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & -> & Hgetjoinres & Halllt).
  rewrite -> List.Forall_forall in Hgetjoinres, Halllt.
  (* now check if t is in chn' *)
  rewrite -> ! find_first_some_correct.
  (* TODO ... should be some way to simplify the proof *)
  split.
  - (* know that t is in some gathered subtree *)
    destruct (find isSome
      (map (tc_getnode t) (map (tc_get_updated_nodes_join tc) chn_u''))) as [ res | ] eqn:E.
    2: unfold isSome; intuition.
    intros _.
    apply find_some in E.
    destruct res as [ res | ].
    2: unfold isSome in E; intuition.
    destruct E as (E & _).
    rewrite -> map_map, in_map_iff in E.
    destruct E as (ch & Hres & Hin).
    pose proof Hin as Hin_sublist.
    eapply sublist_In in Hin.
    2: apply Hsub.

    pose proof Hres as Hres_ch.
    eapply prefix_tc_getnode_impl in Hres_ch.
    2: apply tc_get_updated_nodes_join_is_prefix.
    destruct Hres_ch as (res_ch & Hres_ch).
    pose proof Hres_ch as Einfo.
    eapply prefix_tc_getnode_nodup_sameinfo in Einfo.
    2: apply tc_get_updated_nodes_join_is_prefix.
    2: now eapply tid_nodup_chn_ch with (chn:=chn').
    2: apply Hres.

    pose proof Hres_ch as Hin_flat.
    apply tc_getnode_some in Hin_flat.
    destruct Hin_flat as (Hin_flat & Et).
    eapply tc_flatten_in_ch_chn in Hin_flat.
    2: apply Hin.
    (* now show that res must be the result of "find isSome (map (tc_getnode t) chn')" *)
    destruct (find isSome (map (tc_getnode t) chn')) as [ res' | ] eqn:E.
    + apply find_some in E.
      destruct E as (Hin' & E), res' as [ res' | ].
      2: discriminate.
      (* unify res' and res *)
      pose proof Hin' as Hin_flat'.
      apply tc_getnode_some_list in Hin_flat'.
      destruct Hin_flat' as (Hin_flat' & <-).
      rewrite -> in_map_iff in Hin'.
      destruct Hin' as (ch' & Hres' & Hin').
      pose proof Hres_ch as Htmp.
      eapply tc_getnode_complete_nodup_list with (sub:=res') in Htmp.
      2-5: eauto.
      subst res'.
      replace (tc_rootclk res_ch) with (tc_getclk (tc_roottid res_ch) ch) by (unfold tc_getclk; now rewrite -> Hres_ch).
      eapply List.Forall_forall in IH.
      2: apply Hin.
      apply IH.
      * eapply tc_shape_inv_chn, List.Forall_forall, Foralltc_self in Hshape_tc'; eauto.
      * eapply tc_respect_chn, List.Forall_forall in Hrespect; eauto.
      * now apply Halllt in Hin_sublist.
      * now rewrite -> Hres.
    + (* deriving contradiction *)
      eapply find_none in E.
      2: apply in_map, Hin.
      now destruct (tc_getnode t ch).
  - destruct (find isSome (map (tc_getnode t) chn')) as [ res | ] eqn:E.
    2: lia.
    intros Hlt.

    apply find_some in E.
    destruct res as [ res | ].
    2: intuition.
    destruct E as (Hin & _).

    pose proof Hin as Hin_flat.
    apply tc_getnode_some_list in Hin_flat.
    destruct Hin_flat as (Hin_flat & <-).
    rewrite -> in_map_iff in Hin.
    destruct Hin as (ch & Hres & Hin).

    (* now decide in or not? *)
    destruct (in_dec treeclock_eqdec ch chn_u'') as [ Hin_ch | Hnotin ].
    + (* in the selected tree; use IH *)
      assert (tc_getnode (tc_roottid res) (tc_get_updated_nodes_join tc ch)) as Htmp.
      { 
        rewrite -> List.Forall_forall in IH.
        eapply IH.
        all: auto.
        - eapply tc_shape_inv_chn, List.Forall_forall, Foralltc_self in Hshape_tc'; eauto.
        - eapply tc_respect_chn, List.Forall_forall in Hrespect; eauto.
        - now apply Halllt in Hin_ch.
        - unfold tc_getclk at 2.
          now rewrite -> Hres.
      }
      destruct (tc_getnode (tc_roottid res) (tc_get_updated_nodes_join tc ch)) as [ res' | ] eqn:E.
      2: discriminate.
      assert (In (Some res') (map (tc_getnode (tc_roottid res)) (map (tc_get_updated_nodes_join tc) chn_u''))) as Hin'.
      {
        rewrite -> map_map, -> in_map_iff.
        eauto.
      }
      destruct (find isSome (map (tc_getnode (tc_roottid res)) (map (tc_get_updated_nodes_join tc) chn_u''))) eqn:Efind.
      * apply find_some in Efind.
        destruct o; intuition.
      * eapply find_none in Efind.
        2: apply Hin'.
        discriminate.
    + (* make contradiction *)
      rewrite -> Hgetjoinres in Hnotin.
      2: assumption.
      apply tc_getnode_some in Hres.
      destruct Hres as (Hres & _).
      eapply Foralltc_Forall_subtree, List.Forall_forall in Hnotin.
      2: apply Hres.
      destruct res as [(?, ?, ?) ?].
      simpl in *.
      lia.
Qed.
(*
      apply Foralltc_Forall_subtree


      (* in the selected tree; use IH *)
      rewrite -> List.Forall_forall in IH.
      apply IH.
      all: try assumption.
      + now apply Foralltc_self.
      + (* slightly difficult *)
        rewrite -> in_map_iff in Hnotin |- *.
        rewrite -> flat_map_concat_map, -> map_map in Hnotin.
        intros (ni_ & Heq_ & Hin_).
        apply Hnotin.
        exists ni_.
        split; [ assumption | ].
        rewrite -> in_concat.
        exists (tc_flatten (tc_get_updated_nodes_join tc tc_v')).
        split; [ | assumption ].
        apply in_map_iff.
        eauto.
    - rewrite -> List.Forall_forall in Hres.
      apply Hres in Hnotin'.
      2: assumption.
      apply tc_getclk_le_Foralltc_iff.
      1: now apply Foralltc_self, tid_nodup in Hshape_tc_v'.
      assumption.



    pose proof Hres_ch as Htmp.
    eapply tc_getnode_complete_nodup_list with (sub:=res') in Htmp.





    (* TODO why need both some and complete here? *)
    apply tc_getnode_some_list in Hin.
    destruct Hin as (Hin & Et).
    eapply tc_getnode_complete_list in Hin.
    2: apply Et.
    setoid_rewrite -> in_map_iff in Hin.
    destruct Hin as (res' & ch & Hres' & Hin).
    (* need to use IH here *)






    intros Hlt.





  transitivity (exists ch, In ch chn_u'' /\ tc_getnode t (tc_get_updated_nodes_join tc ch)).
  {



    rewrite -> in_map_iff, -> flat_map_concat_map, -> map_map.
    setoid_rewrite -> in_concat.
    setoid_rewrite -> in_map_iff.
    (* evar (ch : treeclock).
    pose proof (prefixtc_flatten_sublist _ _ (tc_get_updated_nodes_join_is_prefix tc ch)) 
      as Hsub_flat. *)
    split.
    - intros (ch_sub & Et & (ch_flat & (ch & <- & Hin_ch) & Hin_sub)).
      exists ch.
      split; [ assumption | ].
      pose proof (prefixtc_flatten_sublist _ _ (tc_get_updated_nodes_join_is_prefix tc ch)) 
        as Hsub_flat.
      apply in_map with (f:=tc_rootinfo) in Hin_sub.
      eapply sublist_In in Hin_sub.
      2: apply Hsub_flat.
      apply in_map_iff in Hin_sub.
      destruct Hin_sub as (ch_sub' & Einfo & Hin_sub_real).
      destruct ch_sub as [(?, ?, ?) ?], ch_sub' as [(?, ?, ?) ?].
      eapply tc_getnode_complete; eauto.
      simpl in *.
      congruence.
    - intros (ch & Hin_ch & Hsome).
      destruct (tc_getnode t ch) as [ch_sub | ] eqn:Egn; try discriminate.
      apply tc_getnode_some in Egn.
      destruct Egn as (Hin_sub & Et).
      exists ch_sub.
      split; [ assumption | ].
      exists (tc_flatten (tc_get_updated_nodes_join tc ch)).
      split; [ eauto | ].

      
      


      eapply sublist_In in Hin_ch.
      2: apply Hsub.
      apply in_map with (f:=tc_getnode t) in Hin_ch.
      eapply find_none in Hin_ch.
      2: rewrite -> Elq; apply Eqres.

    (* destruct Hin as (ch_sub & Et & Hin). *)
    (* destruct Hin as (ch_flat & Hin_flat & Hin_sub). *)
    (* destruct Hin_flat as (ch & <- & Hin_ch). *)


    evar (ch : treeclock).
    pose proof (prefixtc_flatten_sublist _ _ (tc_get_updated_nodes_join_is_prefix tc ch)) 
      as Hsub_flat.
    apply in_map with (f:=tc_rootinfo) in Hin_sub.
    eapply sublist_In in Hin_sub.
    2: apply Hsub_flat.
    apply in_map_iff in Hin_sub.
    destruct Hin_sub as (ch_sub' & Einfo & Hin_sub_real).
    eapply sublist_In in Hin_ch.
    2: apply Hsub.
    apply in_map with (f:=tc_getnode t) in Hin_ch.
    eapply find_none in Hin_ch.
    2: rewrite -> Elq; apply Eqres.
    destruct (tc_getnode t ch) eqn:Egn; try discriminate.
    eapply tc_getnode_none in Egn.
    2: apply Hin_sub_real.
    destruct ch_sub as [(?, ?, ?) ?], ch_sub' as [(?, ?, ?) ?].
    simpl in *. 
    congruence.
  }

  rewrite -> find_first_some_correct. 
  remember (map (tc_getnode t) chn') as lq eqn:Elq.
  remember (List.find isSome lq) as qres eqn:Eqres.
  symmetry in Eqres.
  symmetry in Elq.

  destruct qres as [ qres | ].
  2:{
    split; [ | lia ].
    intros [ | Hin ]; [ congruence | ].
    (* by contradiction; TODO tedious *)
    rewrite -> in_map_iff, -> flat_map_concat_map, -> map_map in Hin.
    destruct Hin as (ch_sub & Et & Hin).
    rewrite -> in_concat in Hin.
    destruct Hin as (ch_flat & Hin_flat & Hin_sub).
    rewrite -> in_map_iff in Hin_flat.
    destruct Hin_flat as (ch & <- & Hin_ch).
    pose proof (prefixtc_flatten_sublist _ _ (tc_get_updated_nodes_join_is_prefix tc ch)) 
      as Hsub_flat.
    apply in_map with (f:=tc_rootinfo) in Hin_sub.
    eapply sublist_In in Hin_sub.
    2: apply Hsub_flat.
    apply in_map_iff in Hin_sub.
    destruct Hin_sub as (ch_sub' & Einfo & Hin_sub_real).
    eapply sublist_In in Hin_ch.
    2: apply Hsub.
    apply in_map with (f:=tc_getnode t) in Hin_ch.
    eapply find_none in Hin_ch.
    2: rewrite -> Elq; apply Eqres.
    destruct (tc_getnode t ch) eqn:Egn; try discriminate.
    eapply tc_getnode_none in Egn.
    2: apply Hin_sub_real.
    destruct ch_sub as [(?, ?, ?) ?], ch_sub' as [(?, ?, ?) ?].
    simpl in *. 
    congruence.
  }




    
      
    eapply tc_getnode_complete in Hin_sub.
    2: apply Et.
    eapply sublist_In in Hin_ch.
    2: apply Hsub.
    apply in_map with (f:=tc_getnode t) in Hin_ch.
    eapply find_none in Hin_ch.
    2: rewrite -> Elq; apply Eqres.


    
    (* intros (ni_ & Heq_ & Hin_). *)
    (* apply Hnotin. *)
    (* exists ni_. *)
    (* split; [ assumption | ]. *)
    
    exists (tc_flatten (tc_get_updated_nodes_join tc tc_v')).
    split; [ | assumption ].
    apply in_map_iff.
    eauto.

    eapply find_some in Eqres.



  rewrite -> find_first_some_correct, -> flat_map_concat_map, -> map_map. 
  rewrite -> in_map_iff.
  setoid_rewrite -> in_concat.
  setoid_rewrite -> in_map_iff.
  , -> concat_map, -> map_map.
  
  setoid_rewrite -> in_concat.
  remember (map (tc_getnode t) chn') as lq eqn:Elq.
  remember (List.find isSome lq) as qres eqn:Eqres.
  symmetry in Eqres.
  symmetry in Elq.

  
  destruct qres as [ qres | ].
  2:{
    eapply find_some in Eqres.

  1:{
    rewrite <- map_filter_some_correct in Elquery'.
    symmetry in Elquery'.
    apply map_eq_nil in Elquery'.
    rewrite -> Elquery'.
    intuition congruence.
    lia.
  }
  assert (exists tc_v' ni, In tc_v' chn' /\ tc_getnode tc_v' t = Some ni /\ some_ni = Some ni) as (tc_v' & ni & Hin & Hfound & ->).
  {
    assert (In some_ni (List.filter isSome lquery)) as Htmp by (rewrite <- Elquery'; simpl; intuition).
    apply filter_In in Htmp.
    destruct some_ni.
    - rewrite -> Elquery, in_map_iff in Htmp.
      destruct Htmp as ((? & ? & ?) & _).
      eauto.
     - intuition discriminate.
  }
  rewrite <- map_filter_some_correct in Elquery'.
  destruct (map_filter_some lquery) as [ | ni' ll ] eqn:Emapfilter.
  1: lia. (* though also in contradiction *)
  simpl in Elquery'.
  injection Elquery' as <-.
  clear dependent ll.
  replace (info_clk ni) with (tc_getclk tc_v' t).
  2: unfold tc_getclk; now rewrite -> Hfound.
  (* discuss if tc_v' is in the sublist or not; before that ... *)
  pose proof (tc_shape_inv_chn _ _ Hshape_tc') as Hshape_tc_v'.
  pose proof (tc_respect'_chn _ _ _ Hrespect) as Hrespect_tc_v'.
  rewrite -> List.Forall_forall in Hshape_tc_v', Hrespect_tc_v'.
  specialize (Hshape_tc_v' _ Hin).
  specialize (Hrespect_tc_v' _ Hin).
  
  (* now destruct whether in or not *)
  (* just use decidable discussion. *)
  rewrite -> Ejoin_res in Hnotin.
  clear Ejoin_res.
  destruct (in_dec treeclock_eqdec tc_v' chn_u'') as [ Hin' | Hnotin' ].
  - (* in the selected tree; use IH *)
    rewrite -> List.Forall_forall in IH.
    apply IH.
    all: try assumption.
    + now apply Foralltc_self.
    + (* slightly difficult *)
      rewrite -> in_map_iff in Hnotin |- *.
      rewrite -> flat_map_concat_map, -> map_map in Hnotin.
      intros (ni_ & Heq_ & Hin_).
      apply Hnotin.
      exists ni_.
      split; [ assumption | ].
      rewrite -> in_concat.
      exists (tc_flatten (tc_get_updated_nodes_join tc tc_v')).
      split; [ | assumption ].
      apply in_map_iff.
      eauto.
  - rewrite -> List.Forall_forall in Hres.
    apply Hres in Hnotin'.
    2: assumption.
    apply tc_getclk_le_Foralltc_iff.
    1: now apply Foralltc_self, tid_nodup in Hshape_tc_v'.
    assumption.
Qed.

Lemma tc_get_updated_nodes_join_sound : forall tc' (Hshape_tc': tc_shape_inv tc') 
  tc (Hrespect: tc_respect tc' tc) 
  (* root clk le is NECESSARY for sound and completeness since root is always in the gathered prefix *)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') t,
  In t (map tc_roottid (tc_flatten (tc_get_updated_nodes_join tc tc'))) <-> 
  tc_getclk t tc < tc_getclk t tc'.
Proof.
  intros tc' Hshape_tc'.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  unfold tc_getclk at 2.
  cbn.
  destruct (thread_eqdec t u') as [ <- | Htneq ] eqn:Etdec.
  1: intuition congruence.
  (* get the result of tc_get_updated_nodes_join_aux *)
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & -> & Hgetjoinres & Halllt).
  (* now check if t is in chn' *)
  match goal with |- (_ \/ ?a <-> ?b) => enough (a <-> b) by intuition end.
  rewrite -> List.Forall_forall in Hgetjoinres.
  rewrite -> find_first_some_correct.
  split.
  - (* know that t is in some gathered subtree *)
    rewrite -> in_map_iff.
    intros (res' & Et & Hin').
    eapply tc_getnode_complete_list in Hin'.
    2: apply Et.

    setoid_rewrite -> in_map_iff in IH.

    destruct Hin' as (res'' & Hin').
    rewrite -> map_map, -> in_map_iff in Hin'.
    destruct Hin' as (ch' & Hres' & Hin').
    eapply prefix_tc_getnode_impl in Hres'.
    2: apply tc_get_updated_nodes_join_is_prefix.
    destruct Hres' as (res''' & Hres').
    eapply sublist_In in Hin'.
    2: apply Hsub.


    rewrite -> 

    destruct (find isSome (map (tc_getnode t) chn')) as [ res | ] eqn:E.
    + apply find_some in E.
      destruct E as (Hin & E), res as [ res | ].
      2: discriminate.
      rewrite -> in_map_iff in Hin |- *.
      intros (res' & Et & Hin').
      destruct Hin as (ch & Hres & Hin).
      replace (tc_rootclk res) with (tc_getclk t ch) by (unfold tc_getclk; now rewrite -> Hres).
      eapply List.Forall_forall in IH.
      2: apply Hin.
      (* need to use IH here; but before that need to unify res and res' and show "In ch chn_u''" *)
      eapply tc_getnode_complete_list in Hin'.
      2: apply Et.
      rewrite -> 

      apply IH.
      * eapply tc_shape_inv_chn, List.Forall_forall, Foralltc_self in Hshape_tc'; eauto.
      * eapply tc_respect_chn, List.Forall_forall in Hrespect; eauto.
      * 

        



      In map
    + (* deriving contradiction *)
      rewrite -> in_map_iff.
      intros (res & Et & Hin).
      eapply tc_getnode_complete_list in Hin.
      2: apply Et.
      destruct Hin as (res' & Hin).
      rewrite -> map_map, -> in_map_iff in Hin.
      destruct Hin as (ch & Hres & Hin).
      eapply prefix_tc_getnode_impl in Hres.
      2: apply tc_get_updated_nodes_join_is_prefix.
      destruct Hres as (res'' & Hres).
      eapply sublist_In in Hin.
      2: apply Hsub.
      eapply find_none in E.
      2: apply in_map, Hin.
      now destruct (tc_getnode t ch).
  - destruct (find isSome (map (tc_getnode t) chn')) as [ res | ] eqn:E.
    2: lia.
    (* TODO this seems to be a proof pattern *)
    apply find_some in Efind.
    destruct res as [ res | ].
    2: intuition.
    destruct Efind as (Hin & _).
    (* TODO why need both some and complete here? *)
    apply tc_getnode_some_list in Hin.
    destruct Hin as (Hin & Et).
    eapply tc_getnode_complete_list in Hin.
    2: apply Et.
    setoid_rewrite -> in_map_iff in Hin.
    destruct Hin as (res' & ch & Hres' & Hin).
    (* need to use IH here *)






    intros Hlt.





  transitivity (exists ch, In ch chn_u'' /\ tc_getnode t (tc_get_updated_nodes_join tc ch)).
  {



    rewrite -> in_map_iff, -> flat_map_concat_map, -> map_map.
    setoid_rewrite -> in_concat.
    setoid_rewrite -> in_map_iff.
    (* evar (ch : treeclock).
    pose proof (prefixtc_flatten_sublist _ _ (tc_get_updated_nodes_join_is_prefix tc ch)) 
      as Hsub_flat. *)
    split.
    - intros (ch_sub & Et & (ch_flat & (ch & <- & Hin_ch) & Hin_sub)).
      exists ch.
      split; [ assumption | ].
      pose proof (prefixtc_flatten_sublist _ _ (tc_get_updated_nodes_join_is_prefix tc ch)) 
        as Hsub_flat.
      apply in_map with (f:=tc_rootinfo) in Hin_sub.
      eapply sublist_In in Hin_sub.
      2: apply Hsub_flat.
      apply in_map_iff in Hin_sub.
      destruct Hin_sub as (ch_sub' & Einfo & Hin_sub_real).
      destruct ch_sub as [(?, ?, ?) ?], ch_sub' as [(?, ?, ?) ?].
      eapply tc_getnode_complete; eauto.
      simpl in *.
      congruence.
    - intros (ch & Hin_ch & Hsome).
      destruct (tc_getnode t ch) as [ch_sub | ] eqn:Egn; try discriminate.
      apply tc_getnode_some in Egn.
      destruct Egn as (Hin_sub & Et).
      exists ch_sub.
      split; [ assumption | ].
      exists (tc_flatten (tc_get_updated_nodes_join tc ch)).
      split; [ eauto | ].

      
      


      eapply sublist_In in Hin_ch.
      2: apply Hsub.
      apply in_map with (f:=tc_getnode t) in Hin_ch.
      eapply find_none in Hin_ch.
      2: rewrite -> Elq; apply Eqres.

    (* destruct Hin as (ch_sub & Et & Hin). *)
    (* destruct Hin as (ch_flat & Hin_flat & Hin_sub). *)
    (* destruct Hin_flat as (ch & <- & Hin_ch). *)


    evar (ch : treeclock).
    pose proof (prefixtc_flatten_sublist _ _ (tc_get_updated_nodes_join_is_prefix tc ch)) 
      as Hsub_flat.
    apply in_map with (f:=tc_rootinfo) in Hin_sub.
    eapply sublist_In in Hin_sub.
    2: apply Hsub_flat.
    apply in_map_iff in Hin_sub.
    destruct Hin_sub as (ch_sub' & Einfo & Hin_sub_real).
    eapply sublist_In in Hin_ch.
    2: apply Hsub.
    apply in_map with (f:=tc_getnode t) in Hin_ch.
    eapply find_none in Hin_ch.
    2: rewrite -> Elq; apply Eqres.
    destruct (tc_getnode t ch) eqn:Egn; try discriminate.
    eapply tc_getnode_none in Egn.
    2: apply Hin_sub_real.
    destruct ch_sub as [(?, ?, ?) ?], ch_sub' as [(?, ?, ?) ?].
    simpl in *. 
    congruence.
  }

  rewrite -> find_first_some_correct. 
  remember (map (tc_getnode t) chn') as lq eqn:Elq.
  remember (List.find isSome lq) as qres eqn:Eqres.
  symmetry in Eqres.
  symmetry in Elq.

  destruct qres as [ qres | ].
  2:{
    split; [ | lia ].
    intros [ | Hin ]; [ congruence | ].
    (* by contradiction; TODO tedious *)
    rewrite -> in_map_iff, -> flat_map_concat_map, -> map_map in Hin.
    destruct Hin as (ch_sub & Et & Hin).
    rewrite -> in_concat in Hin.
    destruct Hin as (ch_flat & Hin_flat & Hin_sub).
    rewrite -> in_map_iff in Hin_flat.
    destruct Hin_flat as (ch & <- & Hin_ch).
    pose proof (prefixtc_flatten_sublist _ _ (tc_get_updated_nodes_join_is_prefix tc ch)) 
      as Hsub_flat.
    apply in_map with (f:=tc_rootinfo) in Hin_sub.
    eapply sublist_In in Hin_sub.
    2: apply Hsub_flat.
    apply in_map_iff in Hin_sub.
    destruct Hin_sub as (ch_sub' & Einfo & Hin_sub_real).
    eapply sublist_In in Hin_ch.
    2: apply Hsub.
    apply in_map with (f:=tc_getnode t) in Hin_ch.
    eapply find_none in Hin_ch.
    2: rewrite -> Elq; apply Eqres.
    destruct (tc_getnode t ch) eqn:Egn; try discriminate.
    eapply tc_getnode_none in Egn.
    2: apply Hin_sub_real.
    destruct ch_sub as [(?, ?, ?) ?], ch_sub' as [(?, ?, ?) ?].
    simpl in *. 
    congruence.
  }




    
      
    eapply tc_getnode_complete in Hin_sub.
    2: apply Et.
    eapply sublist_In in Hin_ch.
    2: apply Hsub.
    apply in_map with (f:=tc_getnode t) in Hin_ch.
    eapply find_none in Hin_ch.
    2: rewrite -> Elq; apply Eqres.


    
    (* intros (ni_ & Heq_ & Hin_). *)
    (* apply Hnotin. *)
    (* exists ni_. *)
    (* split; [ assumption | ]. *)
    
    exists (tc_flatten (tc_get_updated_nodes_join tc tc_v')).
    split; [ | assumption ].
    apply in_map_iff.
    eauto.

    eapply find_some in Eqres.



  rewrite -> find_first_some_correct, -> flat_map_concat_map, -> map_map. 
  rewrite -> in_map_iff.
  setoid_rewrite -> in_concat.
  setoid_rewrite -> in_map_iff.
  , -> concat_map, -> map_map.
  
  setoid_rewrite -> in_concat.
  remember (map (tc_getnode t) chn') as lq eqn:Elq.
  remember (List.find isSome lq) as qres eqn:Eqres.
  symmetry in Eqres.
  symmetry in Elq.

  
  destruct qres as [ qres | ].
  2:{
    eapply find_some in Eqres.

  1:{
    rewrite <- map_filter_some_correct in Elquery'.
    symmetry in Elquery'.
    apply map_eq_nil in Elquery'.
    rewrite -> Elquery'.
    intuition congruence.
    lia.
  }
  assert (exists tc_v' ni, In tc_v' chn' /\ tc_getnode tc_v' t = Some ni /\ some_ni = Some ni) as (tc_v' & ni & Hin & Hfound & ->).
  {
    assert (In some_ni (List.filter isSome lquery)) as Htmp by (rewrite <- Elquery'; simpl; intuition).
    apply filter_In in Htmp.
    destruct some_ni.
    - rewrite -> Elquery, in_map_iff in Htmp.
      destruct Htmp as ((? & ? & ?) & _).
      eauto.
     - intuition discriminate.
  }
  rewrite <- map_filter_some_correct in Elquery'.
  destruct (map_filter_some lquery) as [ | ni' ll ] eqn:Emapfilter.
  1: lia. (* though also in contradiction *)
  simpl in Elquery'.
  injection Elquery' as <-.
  clear dependent ll.
  replace (info_clk ni) with (tc_getclk tc_v' t).
  2: unfold tc_getclk; now rewrite -> Hfound.
  (* discuss if tc_v' is in the sublist or not; before that ... *)
  pose proof (tc_shape_inv_chn _ _ Hshape_tc') as Hshape_tc_v'.
  pose proof (tc_respect'_chn _ _ _ Hrespect) as Hrespect_tc_v'.
  rewrite -> List.Forall_forall in Hshape_tc_v', Hrespect_tc_v'.
  specialize (Hshape_tc_v' _ Hin).
  specialize (Hrespect_tc_v' _ Hin).
  
  (* now destruct whether in or not *)
  (* just use decidable discussion. *)
  rewrite -> Ejoin_res in Hnotin.
  clear Ejoin_res.
  destruct (in_dec treeclock_eqdec tc_v' chn_u'') as [ Hin' | Hnotin' ].
  - (* in the selected tree; use IH *)
    rewrite -> List.Forall_forall in IH.
    apply IH.
    all: try assumption.
    + now apply Foralltc_self.
    + (* slightly difficult *)
      rewrite -> in_map_iff in Hnotin |- *.
      rewrite -> flat_map_concat_map, -> map_map in Hnotin.
      intros (ni_ & Heq_ & Hin_).
      apply Hnotin.
      exists ni_.
      split; [ assumption | ].
      rewrite -> in_concat.
      exists (tc_flatten (tc_get_updated_nodes_join tc tc_v')).
      split; [ | assumption ].
      apply in_map_iff.
      eauto.
  - rewrite -> List.Forall_forall in Hres.
    apply Hres in Hnotin'.
    2: assumption.
    apply tc_getclk_le_Foralltc_iff.
    1: now apply Foralltc_self, tid_nodup in Hshape_tc_v'.
    assumption.
Qed.

Lemma tc_get_updated_nodes_join_sound : forall tc' (Hshape_tc': tc_shape_inv tc') 
  tc (Hrespect: tc_respect tc' tc)
  t (Hnotin: ~ In t (map tc_roottid (tc_flatten (tc_get_updated_nodes_join tc tc')))), 
  tc_getclk tc' t <= tc_getclk tc t.
Proof.
  intros tc' Hshape_tc'.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  rewrite -> tc_get_updated_nodes_join_eta in Hnotin.
  cbn in Hnotin.
  apply Decidable.not_or in Hnotin.
  destruct (thread_eqdec t u') as [ | Htneq ] eqn:Etdec.
  1: intuition congruence.
  destruct Hnotin as (_ & Hnotin).
  rewrite -> tc_getclk_step.  (* step *)
  simpl.
  rewrite -> Etdec, -> tc_flatten_getclk. 
  (* first check if chn' is nil *)
  destruct chn' as [ | [(v', clk_v', aclk_v') chn_v'] chn'' ] eqn:Echn'.
  1: unfold thrmap_getclk; simpl; lia.
  rewrite <- Echn' in *.
  (* now check if t is in chn' *)
  remember (map (fun tc0 => tc_getnode tc0 t) chn') as lquery eqn:Elquery.
  remember (List.filter isSome lquery) as lquery' eqn:Elquery'.
  destruct lquery' as [ | some_ni lquery' ].
  1:{
    rewrite <- map_filter_some_correct in Elquery'.
    symmetry in Elquery'.
    apply map_eq_nil in Elquery'.
    rewrite -> Elquery'.
    lia.
  }
  assert (exists tc_v' ni, In tc_v' chn' /\ tc_getnode tc_v' t = Some ni /\ some_ni = Some ni) as (tc_v' & ni & Hin & Hfound & ->).
  {
    assert (In some_ni (List.filter isSome lquery)) as Htmp by (rewrite <- Elquery'; simpl; intuition).
    apply filter_In in Htmp.
    destruct some_ni.
    - rewrite -> Elquery, in_map_iff in Htmp.
      destruct Htmp as ((? & ? & ?) & _).
      eauto.
     - intuition discriminate.
  }
  rewrite <- map_filter_some_correct in Elquery'.
  destruct (map_filter_some lquery) as [ | ni' ll ] eqn:Emapfilter.
  1: lia. (* though also in contradiction *)
  simpl in Elquery'.
  injection Elquery' as <-.
  clear dependent ll.
  replace (info_clk ni) with (tc_getclk tc_v' t).
  2: unfold tc_getclk; now rewrite -> Hfound.
  (* discuss if tc_v' is in the sublist or not; before that ... *)
  pose proof (tc_shape_inv_chn _ _ Hshape_tc') as Hshape_tc_v'.
  pose proof (tc_respect'_chn _ _ _ Hrespect) as Hrespect_tc_v'.
  rewrite -> List.Forall_forall in Hshape_tc_v', Hrespect_tc_v'.
  specialize (Hshape_tc_v' _ Hin).
  specialize (Hrespect_tc_v' _ Hin).
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  removehead Htmp.
  2: assumption.
  removehead Htmp.
  2: assumption.
  destruct Htmp as (chn_u'' & Hsub & Ejoin_res & Hres).
  (* now destruct whether in or not *)
  (* just use decidable discussion. *)
  rewrite -> Ejoin_res in Hnotin.
  clear Ejoin_res.
  destruct (in_dec treeclock_eqdec tc_v' chn_u'') as [ Hin' | Hnotin' ].
  - (* in the selected tree; use IH *)
    rewrite -> List.Forall_forall in IH.
    apply IH.
    all: try assumption.
    + now apply Foralltc_self.
    + (* slightly difficult *)
      rewrite -> in_map_iff in Hnotin |- *.
      rewrite -> flat_map_concat_map, -> map_map in Hnotin.
      intros (ni_ & Heq_ & Hin_).
      apply Hnotin.
      exists ni_.
      split; [ assumption | ].
      rewrite -> in_concat.
      exists (tc_flatten (tc_get_updated_nodes_join tc tc_v')).
      split; [ | assumption ].
      apply in_map_iff.
      eauto.
  - rewrite -> List.Forall_forall in Hres.
    apply Hres in Hnotin'.
    2: assumption.
    apply tc_getclk_le_Foralltc_iff.
    1: now apply Foralltc_self, tid_nodup in Hshape_tc_v'.
    assumption.
Qed.
*)
(* 
  finally needed:
  - join implements pointwise-max
  - join preserves shape inv
  - join preserves respect in both directions
*)

End TreeClock.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant is_left => "(fun x -> x)".
Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ].
Extract Constant PeanoNat.Nat.leb => "( <= )".

(* FIXME: simply Import stdpp will result in mysterious extracted code. 
    Currently do not know why and there is no related report in Iris/stdpp/issues ...
    will investigate it later. For now, ignore this
*)
Extraction "extraction/lib/tcimpl.ml" tc_join.
