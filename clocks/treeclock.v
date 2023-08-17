From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
From distributedclocks.utils Require Export util libtac.
Import ssreflect.SsrSyntax.

From stdpp Require list.

(* TODO maybe this should be replaced with eqType in the future *)

Class EqDec (A : Type) := {
  eqdec : forall (x y : A), {x = y} + {x <> y}
}.

Section TreeClock.

Context {thread : Type} `{thread_eqdec : EqDec thread}.

(* OK, let's try making info_aclk not an option by making the aclk of the root useless. *)

Record nodeinfo : Type := mkInfo {
  info_tid : thread;
  info_clk : nat;
  info_aclk : nat
}.

Definition nodeinfo_eqdec (ni ni' : nodeinfo) : {ni = ni'} + {ni <> ni'}.
Proof.
  decide equality.
  1-2: apply Nat.eq_dec.
  apply eqdec.
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

Definition tc_init t := Node (mkInfo t 0 0) nil.

Definition tc_incr tc amount := 
  let: Node (mkInfo t clk aclk) chn := tc in Node (mkInfo t (PeanoNat.Nat.add clk amount) aclk) chn.

Definition tc_rootinfo tc :=
  let: Node ni _ := tc in ni.

Definition tc_rootinfo_partial tc :=
  let: Node (mkInfo u clk _) _ := tc in (u, clk).

Definition tc_rootchn tc :=
  let: Node _ chn := tc in chn.

Definition tc_roottid tc := info_tid (tc_rootinfo tc).

Definition tc_rootclk tc := info_clk (tc_rootinfo tc).

Definition tc_rootaclk tc := info_aclk (tc_rootinfo tc).

Global Arguments tc_roottid !_ /.
Global Arguments tc_rootclk !_ /.
Global Arguments tc_rootaclk !_ /.

Fact tc_rootinfo_tid_inj : forall x y, tc_rootinfo x = tc_rootinfo y -> tc_roottid x = tc_roottid y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

Fact tc_rootinfo_clk_inj : forall x y, tc_rootinfo x = tc_rootinfo y -> tc_rootclk x = tc_rootclk y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

Fact tc_rootinfo_aclk_inj : forall x y, tc_rootinfo x = tc_rootinfo y -> tc_rootaclk x = tc_rootaclk y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

(* this is_left is for better printing of find (has_same_tid t) *)

Definition has_same_tid t tc := is_left (eqdec (tc_roottid tc) t).

Global Arguments has_same_tid _ !_ /.

Fact has_same_tid_true t tc : has_same_tid t tc = true <-> t = tc_roottid tc.
Proof. unfold has_same_tid. destruct (eqdec (tc_roottid tc) t) as [ <- | ]; simpl; intuition congruence. Qed.

Fact has_same_tid_false t tc : has_same_tid t tc = false <-> t <> tc_roottid tc.
Proof. unfold has_same_tid. destruct (eqdec (tc_roottid tc) t) as [ <- | ]; simpl; intuition congruence. Qed.

Fact tc_rootinfo_has_same_tid_congr : forall x y, tc_rootinfo x = tc_rootinfo y -> 
  forall t, has_same_tid t x = has_same_tid t y.
Proof. intros. unfold has_same_tid. now rewrite tc_rootinfo_tid_inj with (x:=x) (y:=y). Qed.

(* only for some domain-based reasoning; not for finding *)

Fixpoint tc_flatten tc :=
  let: Node ni chn := tc in tc :: (List.flat_map tc_flatten chn).

Definition subtc tc1 tc2 : Prop := In tc1 (tc_flatten tc2).

Global Arguments subtc _ _/.

Fact tc_flatten_self_in tc : In tc (tc_flatten tc).
Proof. destruct tc as [? ?]. simpl. now left. Qed.

Fact subtc_chn tc ch : In ch (tc_rootchn tc) -> subtc ch tc.
Proof. 
  destruct tc as [(u, clk, aclk) chn]. simpl. intros. 
  right. apply in_flat_map. exists ch. split; auto. apply tc_flatten_self_in.
Qed.

Lemma subtc_trans tc tc' tc'' : subtc tc'' tc' -> subtc tc' tc -> subtc tc'' tc.
Proof.
  revert tc'' tc'.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in H, H0. 
  destruct H0 as [ <- | H0 ]; auto.
  rewrite -> in_flat_map in H0.
  destruct H0 as (ch & Hin_ch & H0).
  rewrite -> Forall_forall in IH. 
  specialize (IH _ Hin_ch _ _ H H0).
  hnf. right. apply in_flat_map. now exists ch.
Qed.

(* proof-relevant witness of subtree *)

Fixpoint tc_locate (tc : treeclock) (pos : list nat) : option treeclock :=
  match pos with
  | nil => Some tc
  | x :: pos' => 
    match nth_error (tc_rootchn tc) x with
    | Some ch => tc_locate ch pos'
    | None => None
    end
  end.

Definition subtc_witness (l : list nat) sub tc := tc_locate tc l = Some sub.

Lemma subtc_witness_subtc l :
  forall sub tc, subtc_witness l sub tc -> subtc sub tc.
Proof.
  induction l as [ | x l IH ]; intros; hnf in H; simpl in H.
  - injection H as <-. 
    apply tc_flatten_self_in.
  - destruct (nth_error (tc_rootchn tc) x) as [ res | ] eqn:E; try eqsolve.
    apply IH in H.
    apply nth_error_In in E.
    eapply subtc_trans; [ apply H | ].
    now apply subtc_chn.
Qed.

Lemma subtc_subtc_witness tc :
  forall sub, subtc sub tc -> exists l, subtc_witness l sub tc.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  hnf in H. 
  destruct H as [ <- | ].
  - now exists nil.
  - apply in_flat_map in H.
    destruct H as (ch & Hin_ch & Hin).
    rewrite -> Forall_forall in IH. 
    specialize (IH _ Hin_ch).
    apply IH in Hin. 
    destruct Hin as (l & H).
    apply In_nth_error in Hin_ch. 
    destruct Hin_ch as (n & E).
    exists (n :: l); hnf; simpl; now rewrite E.
Qed. 

Corollary subtc_witness_iff sub tc :
  subtc sub tc <-> exists l, subtc_witness l sub tc.
Proof.
  split; intros.
  - now apply subtc_subtc_witness in H.
  - destruct H as (l & H). now apply subtc_witness_subtc in H.
Qed.

(* TODO may revise later *)
Fact par_subtc_trace tc res l tc_par (Hsub : subtc_witness l tc_par tc) (Hin : In res (tc_rootchn tc_par)) :
  exists ch, In ch (tc_rootchn tc) /\ subtc res ch.
Proof.
  destruct tc as [(u, clk, aclk) chn], l as [ | x l ].
  - hnf in Hsub. simpl in Hsub. injection Hsub as <-. simpl in Hin.
    exists res. split; auto. hnf. apply tc_flatten_self_in.
  - hnf in Hsub. simpl in Hsub.
    destruct (nth_error chn x) as [ ch | ] eqn:Enth; try eqsolve.
    pose proof Enth as Hin_ch. apply nth_error_In in Hin_ch.
    exists ch. split; auto. eapply subtc_trans.
    + apply subtc_chn, Hin.
    + apply subtc_witness_iff. eauto.
Qed.

Fact tc_flatten_root_chn_split tcs :
  Permutation.Permutation (flat_map tc_flatten tcs)
    (tcs ++ (flat_map tc_flatten (flat_map tc_rootchn tcs))).
Proof.
  induction tcs as [ | [ni chn] tcs IH ].
  1: constructor.
  simpl.
  constructor.
  rewrite -> flat_map_app.
  etransitivity.
  2: apply Permutation.Permutation_app_swap_app.
  now apply Permutation.Permutation_app_head.
Qed.

Fact tc_height_subtree_lt tc :
  Forall (fun tc' => tc_height tc' < tc_height tc) (flat_map tc_flatten (tc_rootchn tc)).
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  rewrite -> List.Forall_forall in IH |- *.
  simpl.
  setoid_rewrite -> in_flat_map.
  intros sub ([ni_ch chn_ch] & Hin_ch & Hin).
  simpl in Hin.
  specialize (IH _ Hin_ch).
  rewrite -> List.Forall_forall in IH.
  simpl in IH.
  unfold lt in IH |- *.
  assert (tc_height (Node ni_ch chn_ch) <= list_max (map tc_height chn)) as H.
  {
    eapply tc_height_le; eauto.
  }
  destruct Hin as [ <- | Hin ].
  - lia.
  - transitivity (S (list_max (map tc_height chn_ch))).
    1: now apply IH.
    simpl in H.
    lia.
Qed.

(* a height-based argument *)

Fact self_not_in_tc_flatten_chn ni chn : ~ In (Node ni chn) (flat_map tc_flatten chn).
Proof.
  pose proof (tc_height_subtree_lt (Node ni chn)) as Hlt.
  simpl in Hlt.
  rewrite -> List.Forall_forall in Hlt.
  intros Hin.
  apply Hlt in Hin.
  simpl in Hin.
  lia.
Qed.

Definition tc_getnode t tc := find (has_same_tid t) (tc_flatten tc).

Global Arguments tc_getnode _ !_ /.

Fact tc_getnode_self tc : tc_getnode (tc_roottid tc) tc = Some tc.
Proof.
  destruct tc as [(u, ?, ?) ?].
  simpl.
  now destruct (eqdec u u).
Qed.

Tactic Notation "tc_getnode_unfold" :=
  repeat match goal with
  | |- context[find (has_same_tid ?t) (tc_flatten ?ch ++ flat_map tc_flatten ?chn)] =>
    rewrite -> find_app; change (find (has_same_tid t) (tc_flatten ch)) with (tc_getnode t ch)
  end.

(* the same as paper, use 0 as default clk *)

Definition tc_getclk t tc :=
  match tc_getnode t tc with
  | Some res => tc_rootclk res
  | _ => 0
  end.

Section Old_Complaints.
(* things here can be still kept, but no longer useful *)
(*
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

  Corollary find_first_some_correct' [A : Type] (l : list (option A)) : 
    find_first_some l <-> find isSome l.
  Proof. 
    rewrite -> find_first_some_correct. 
    destruct (find isSome l) as [ res | ] eqn:E.
    2: auto.
    apply find_some in E.
    now destruct res.
  Qed.

  Fixpoint tc_getnode_deprecated t tc :=
    let: Node ni chn := tc in 
    if eqdec t (info_tid ni)
    then Some tc
    else find_first_some (map (tc_getnode_deprecated t) chn).

  Fact tc_getnode_deprecated_has_tid t tc res
    (Hres : tc_getnode_deprecated t tc = Some res) : tc_roottid res = t.
  Proof.
    induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
    simpl in Hres.
    destruct (eqdec t u) as [ <- | Hneq ].
    1:{
      simpl.
      injection Hres as <-.
      intuition.
    }
    rewrite -> find_first_some_correct in Hres.
    destruct (find isSome (map (tc_getnode_deprecated t) chn)) as [ res_chn | ] eqn:E.
    - apply find_some in E.
      destruct res_chn; [ injection Hres as -> | discriminate ].
      destruct E as (E & _).
      rewrite -> in_map_iff in E.
      rewrite -> List.Forall_forall in IH.
      firstorder.
    - discriminate.
  Qed.

  (* essentially not useful ... only add redundancy *)

  Fact tc_getnode_deprecated_useless t tc : tc_getnode_deprecated t tc = tc_getnode t tc.
  Proof.
    induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
    simpl.
    destruct (eqdec t u) as [ <- | ] eqn:E.
    - now rewrite -> E.
    - destruct (eqdec u t) as [ -> | ].
      1: congruence.
      simpl.
      rewrite -> find_first_some_correct.
      clear -IH.
      induction chn as [ | ch chn IH' ].
      1: auto.
      apply Forall_cons_iff in IH.
      destruct IH as (HH & IH).
      specialize (IH' IH).
      simpl.
      tc_getnode_unfold.
      destruct (tc_getnode_deprecated t ch) as [ res | ] eqn:E; simpl.
      + now rewrite <- HH.
      + now rewrite <- HH.
  Qed.
*)
End Old_Complaints.

(* Forall over all subtrees *)
(* it is hard to define this as a recursive function, so use indprop instead *)

Inductive Foralltc (P : treeclock -> Prop) : treeclock -> Prop :=
  Foralltc_intro : forall ni chn, 
    P (Node ni chn) -> Forall (Foralltc P) chn -> Foralltc P (Node ni chn). 

(* TODO maybe make this the prime version later ... *)
Fact Foralltc_cons_iff P ni chn :
  Foralltc P (Node ni chn) <-> (P (Node ni chn) /\ Forall (Foralltc P) chn).
Proof.
  split; intros.
  - now inversion H.
  - now apply Foralltc_intro.
Qed.

Fact Foralltc_cons_iff' P tc : Foralltc P tc <-> (P tc /\ Forall (Foralltc P) (tc_rootchn tc)).
Proof. destruct tc. now apply Foralltc_cons_iff. Qed.

Fact Foralltc_self P tc (H : Foralltc P tc) : P tc.
Proof. destruct tc. now apply Foralltc_cons_iff in H. Qed.

Fact Foralltc_chn P tc (H : Foralltc P tc) : Forall (Foralltc P) (tc_rootchn tc).
Proof. destruct tc. now apply Foralltc_cons_iff in H. Qed.

Fact Foralltc_chn_selves P tc (H : Foralltc P tc) : Forall P (tc_rootchn tc).
Proof. eapply List.Forall_impl. 1: apply Foralltc_self. now apply Foralltc_chn. Qed.

Lemma Foralltc_Forall_subtree (P : treeclock -> Prop) tc :
  Foralltc P tc <-> Forall P (tc_flatten tc).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> ! Foralltc_cons_iff, List.Forall_cons_iff, -> ! List.Forall_forall.
  setoid_rewrite in_flat_map.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  firstorder. 
  apply IH; firstorder. 
Qed.

Corollary Foralltc_trivial (P : treeclock -> Prop) (H : forall tc, P tc) tc : Foralltc P tc.
Proof. now apply Foralltc_Forall_subtree, List.Forall_forall. Qed.

Lemma Foralltc_impl_pre (P Q : treeclock -> Prop) tc 
  (Hf : Foralltc (fun tc' => P tc' -> Q tc') tc) (H : Foralltc P tc) : Foralltc Q tc.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  rewrite -> Foralltc_cons_iff in Hf, H |- *.
  destruct H as (H & H0), Hf as (Hf & Hf0).
  rewrite -> Forall_forall in *. 
  split; try firstorder.
Qed.

Corollary Foralltc_impl (P Q : treeclock -> Prop) (Hpq : forall tc, P tc -> Q tc) tc 
  (H : Foralltc P tc) : Foralltc Q tc.
Proof. eapply Foralltc_impl_pre. 2: apply H. now apply Foralltc_trivial. Qed.

Lemma Foralltc_Forall_chn_comm P tc : 
  Foralltc (fun tc' => Forall P (tc_rootchn tc')) tc <-> Forall (Foralltc P) (tc_rootchn tc).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> Foralltc_cons_iff at 1. simpl.
  rewrite <- list.Forall_and. 
  repeat rewrite -> List.Forall_forall in *.
  setoid_rewrite -> Foralltc_cons_iff' at 2.
  (* TODO will firstorder use something unrelated, like EqDec? 
    possibly this can be fixed by clearing thread_eqdec at first, but ignore it for now ... *)
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

Corollary Foralltc_Foralltc_subtree (P : treeclock -> Prop) tc :
  Foralltc P tc <-> Forall (Foralltc P) (tc_flatten tc).
Proof. now rewrite <- Foralltc_idempotent, -> Foralltc_Forall_subtree. Qed.

Fact Foralltc_subtc P tc sub (Hsub : subtc sub tc) (H : Foralltc P tc) : P sub.
Proof. rewrite -> Foralltc_Forall_subtree, -> Forall_forall in H. auto. Qed. 

Inductive prefixtc : treeclock -> treeclock -> Prop :=
  prefixtc_intro : forall ni chn chn_sub prefix_chn, 
    list.sublist chn_sub chn ->
    Forall2 prefixtc prefix_chn chn_sub ->
    prefixtc (Node ni prefix_chn) (Node ni chn).

Fact prefixtc_inv ni1 ni2 chn1 chn2 (Hprefix: prefixtc (Node ni1 chn1) (Node ni2 chn2)) :
  ni1 = ni2 /\ exists chn2_sub, list.sublist chn2_sub chn2 /\ Forall2 prefixtc chn1 chn2_sub.
Proof. inversion Hprefix; subst. firstorder. Qed.

Fact prefixtc_rootinfo_same tc tc' (Hprefix : prefixtc tc tc') :
  tc_rootinfo tc = tc_rootinfo tc'.
Proof. 
  destruct tc, tc'.
  apply prefixtc_inv in Hprefix.
  intuition congruence.
Qed.

#[export] Instance prefixtc_refl : Reflexive prefixtc.
Proof.
  hnf.
  intros tc.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  econstructor.
  1: reflexivity.
  now apply list.Forall_Forall2_diag.
Qed.

Fact prefixtc_nil_l ni chn : prefixtc (Node ni nil) (Node ni chn).
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

Corollary prefixtc_size_le tc1 tc2 (Hprefix : prefixtc tc1 tc2) :
  length (tc_flatten tc1) <= length (tc_flatten tc2).
Proof. rewrite <- ! map_length with (f:=tc_rootinfo). now apply list.sublist_length, prefixtc_flatten_sublist. Qed.

Corollary prefixtc_flatten_info_incl tc1 tc2 (Hprefix : prefixtc tc1 tc2) :
  incl (map tc_rootinfo (tc_flatten tc1)) (map tc_rootinfo (tc_flatten tc2)).
Proof.
  intros ni Hin.
  eapply sublist_In.
  1: eapply prefixtc_flatten_sublist; eauto.
  assumption.
Qed.

Lemma prefixtc_size_eq_tc_eq tc1 tc2 (Hprefix : prefixtc tc1 tc2) 
  (H : length (tc_flatten tc1) = length (tc_flatten tc2)) : tc1 = tc2.
Proof.
  revert tc2 Hprefix H.
  induction tc1 as [ni chn1 IH] using treeclock_ind_2; intros.
  destruct tc2 as [ni2 chn2].
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (<- & (chn2_sub & Hsub & Hprefix)).
  simpl in H.
  injection H as H.
  f_equal; clear ni.
  assert (length (flat_map tc_flatten chn1) <= length (flat_map tc_flatten chn2_sub)) as H1.
  {
    rewrite -> ! flat_map_concat_map.
    eapply length_concat_le, list.Forall2_fmap_2, list.Forall2_impl.
    1: apply Hprefix.
    apply prefixtc_size_le.
  }
  pose proof (length_concat_sum (map tc_flatten chn2_sub)) as E'.
  pose proof (length_concat_sum (map tc_flatten chn2)) as E.
  rewrite <- ! flat_map_concat_map in E, E'.
  pose proof Hsub as H2.
  apply sublist_map with (f:=fun t => length (tc_flatten t)), sublist_sum_le in H2.
  assert (chn2_sub = chn2) as ->.
  {
    apply sublist_map_sum_eq_ with (f:=fun t => length (tc_flatten t)); auto.
    2: rewrite -> map_map in E, E'; lia.
    intros [? ?]; simpl; lia.
  }
  (* why is this so troublesome? *)
Abort.

Lemma tc_getnode_in_iff t tcs : 
  In t (map tc_roottid tcs) <-> find (has_same_tid t) tcs.
Proof.
  rewrite -> in_map_iff.
  split.
  - intros (sub & <- & Hin).
    destruct (find (has_same_tid (tc_roottid sub)) tcs) eqn:E.
    1: auto.
    eapply find_none in E.
    2: apply Hin.
    now rewrite -> has_same_tid_false in E.
  - destruct (find (has_same_tid t) tcs) as [ res | ] eqn:E.
    2: intros; discriminate.
    intros _.
    apply find_some in E.
    destruct E as (Hin & E).
    rewrite -> has_same_tid_true in E.
    eauto.
Qed.

(* FIXME: this naming is weird ... *)
Corollary tc_getnode_subtc_iff t tc : 
  In t (map tc_roottid (tc_flatten tc)) <-> tc_getnode t tc.
Proof. apply tc_getnode_in_iff. Qed.

Fact tc_getnode_has_tid t tc res
  (Hres : tc_getnode t tc = Some res) : In res (tc_flatten tc) /\ tc_roottid res = t.
Proof. 
  apply find_some in Hres.
  now rewrite -> has_same_tid_true in Hres.
Qed.

Fact tc_getnode_res_Foralltc [t tc res] [P : treeclock -> Prop]
  (Hp : Foralltc P tc) (Hres : tc_getnode t tc = Some res) : 
  P res /\ tc_roottid res = t.
Proof.
  apply find_some in Hres.
  rewrite -> has_same_tid_true in Hres.
  destruct Hres as (Hin & ->).
  rewrite -> Foralltc_Forall_subtree, -> Forall_forall in Hp.
  firstorder. 
Qed.

Fact tid_nodup_find_self tcs (Hnodup : List.NoDup (map tc_roottid tcs)) :
  Forall (fun tc => find (has_same_tid (tc_roottid tc)) tcs = Some tc) tcs.
Proof.
  induction tcs as [ | tc tcs IH ].
  1: constructor.
  simpl in Hnodup |- *.
  apply NoDup_cons_iff in Hnodup.
  destruct Hnodup as (Hnotin & Hnodup).
  specialize (IH Hnodup).
  constructor.
  - unfold has_same_tid.
    destruct (eqdec (tc_roottid tc) (tc_roottid tc)).
    2: contradiction.
    now simpl.
  - rewrite -> List.Forall_forall in IH |- *.
    intros tc' Hin.
    destruct (has_same_tid (tc_roottid tc') tc) eqn:E.
    + rewrite -> has_same_tid_true in E.
      apply in_map with (f:=tc_roottid) in Hin.
      congruence.
    + now apply IH.
Qed.

Corollary tid_nodup_find_self_sub tc (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc))) 
  sub (Hin_sub : In sub (tc_flatten tc)) :
  base.fmap tc_rootinfo (tc_getnode (tc_roottid sub) tc) = Some (tc_rootinfo sub).
Proof.
  pose proof (tid_nodup_find_self (tc_flatten tc) Hnodup) as H.
  rewrite -> List.Forall_forall in H.
  specialize (H _ Hin_sub).
  unfold tc_getnode.
  now rewrite -> H.
Qed.

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

Fixpoint tc_detach_nodes tcs tc : treeclock * list treeclock :=
  let: Node ni chn := tc in
  let: (new_chn, res) := List.split (map (tc_detach_nodes tcs) chn) in
  let: (res', new_chn') := List.partition (fun tc' => find (has_same_tid (tc_roottid tc')) tcs)
    new_chn in
  (Node ni new_chn', (List.concat res) ++ res').

(* return a reconstructed tree to be added into the pivot *)

Fixpoint tc_attach_nodes forest tc' : treeclock :=
  let: Node info_u' chn' := tc' in
  (* try finding a tree in the forest with the same root thread *)
  (* let: u_pre := List.find (fun tc => eqdec (tc_roottid tc) (info_tid info_u')) forest in *)
  let: u_pre := List.find (has_same_tid (info_tid info_u')) forest in
  let: chn_u := (match u_pre with Some u => tc_rootchn u | None => nil end) in
  (* for u', inherit clk and aclk anyway; prepend all children of u' *)
  Node info_u' ((map (tc_attach_nodes forest) chn') ++ chn_u).

Definition tc_join tc tc' :=
  let: mkInfo z' clk_z' aclk_z' := tc_rootinfo tc' in
  if clk_z' <=? (tc_getclk z' tc)
  then tc
  else 
    let: subtree_tc' := tc_get_updated_nodes_join tc tc' in
    let: (pivot, forest) := tc_detach_nodes (tc_flatten subtree_tc') tc in
    let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
    let: Node info_z chn_z := pivot in 
    Node info_z ((Node (mkInfo w clk_w (info_clk info_z)) chn_w) :: chn_z).

Definition tc_ge (tc_larger tc : treeclock) : Prop := 
  Foralltc (fun tc'' => let: Node (mkInfo w clk_w _) _ := tc'' in 
    clk_w <= tc_getclk w tc_larger) tc.

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

Fact tc_respect_nochn_trivial ni tc' : tc_respect (Node ni nil) tc'.
Proof.
  constructor.
  - constructor; auto.
    hnf.
    destruct ni.
    intros Hle.
    unfold tc_ge.
    constructor; simpl; auto.
  - constructor; auto.
    hnf.
    now destruct ni.
Qed.

Fact tc_ge_all_getclk_ge tc tc_larger (H : tc_ge tc_larger tc) 
  t : tc_getclk t tc <= tc_getclk t tc_larger.
Proof.
  unfold tc_getclk at 1.
  destruct (tc_getnode t tc) as [ [(t', clk', aclk') chn'] | ] eqn:E.
  - apply find_some in E.
    rewrite -> has_same_tid_true in E.
    simpl in E.
    destruct E as (Hin' & <-).
    hnf in H.
    rewrite -> Foralltc_Forall_subtree, List.Forall_forall in H.
    specialize (H _ Hin').
    firstorder.
  - lia.
Qed.

Fact all_getclk_ge_tc_ge tc tc_larger
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc)))
  (H : forall t, tc_getclk t tc <= tc_getclk t tc_larger) :
  tc_ge tc_larger tc.
Proof.
  unfold tc_ge.
  pose proof (tid_nodup_find_self _ Hnodup) as Hself.
  rewrite -> Foralltc_Forall_subtree.
  rewrite -> List.Forall_forall in Hself |- *.
  intros [(t, clk, aclk) chn] Hin.
  specialize (Hself _ Hin).
  simpl in Hself.
  replace clk with (tc_getclk t tc).
  2: unfold tc_getclk, tc_getnode; now rewrite -> Hself.
  now apply H.
Qed.

#[export] Instance tc_ge_trans : Transitive tc_ge.
Proof.
  hnf.
  intros tc_x tc_y tc_z Hge1 Hge2.
  hnf in Hge2 |- *.
  rewrite -> Foralltc_Forall_subtree, List.Forall_forall in Hge2 |- *.
  intros [(t, clk, aclk) chn] Hin.
  specialize (Hge2 _ Hin).
  simpl in Hge2.
  pose proof (tc_ge_all_getclk_ge _ _ Hge1 t).
  lia.
Qed.

(* a typical corr proof. TODO summarize? *)

Fact tc_ge_prefix_preserve tc : 
  forall tc' (Hprefix : prefixtc tc' tc)
    tc_larger (Hge : tc_ge tc_larger tc),
  tc_ge tc_larger tc'.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  injection Htmp as ->.
  subst clk' aclk'.
  unfold tc_ge in Hge |- *.
  rewrite -> Foralltc_cons_iff in Hge |- *.
  destruct Hge as (Ele & Hle).
  split; [ assumption | ].
  pose proof (sublist_In _ _ Hsub) as Hsub_in.
  pose proof (Forall2_forall_exists_l _ _ _ Hcorr) as Hcorr_in.
  rewrite -> List.Forall_forall in IH, Hle |- *.
  intros ch' Hin'.
  destruct (Hcorr_in _ Hin') as (ch & Hin_ch & Hprefix).
  specialize (Hle _ (Hsub_in _ Hin_ch)).
  eapply IH; eauto.
Qed.

Section Pointwise_Treeclock.

  Variables (tc1 tc2 tc_max : treeclock).
  Hypotheses (Hpmax : forall t, tc_getclk t tc_max = Nat.max (tc_getclk t tc1) (tc_getclk t tc2))
    (Hnodup1 : List.NoDup (map tc_roottid (tc_flatten tc1)))
    (Hnodup2 : List.NoDup (map tc_roottid (tc_flatten tc2))).

  Fact tc_ge_from_pointwise_max : tc_ge tc_max tc1 /\ tc_ge tc_max tc2.
  Proof.
    eapply all_getclk_ge_tc_ge with (tc_larger:=tc_max) in Hnodup1, Hnodup2.
    2-3: intros t; rewrite -> Hpmax; lia.
    intuition.
  Qed.

  Lemma dmono_single_pointwise_max_preserve tc 
    (Hdmono1 : dmono_single tc1 tc)
    (Hdmono2 : dmono_single tc2 tc) :
    dmono_single tc_max tc.
  Proof.
    hnf in Hdmono1, Hdmono2 |- *.
    destruct tc as [(t, clk, aclk) chn].
    intros Hle.
    pose proof tc_ge_from_pointwise_max as Hge.
    rewrite -> Hpmax in Hle.
    apply Nat.max_le in Hle.
    destruct Hle as [ Hle | Hle ].
    1: specialize (Hdmono1 Hle); transitivity tc1; auto.
    2: specialize (Hdmono2 Hle); transitivity tc2; auto.
    all: intuition.
  Qed.

  Lemma imono_single_pointwise_max_preserve tc 
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

  Corollary tc_respect_pointwise_max_preserve tc 
    (Hrespect1 : tc_respect tc tc1)
    (Hrespect2 : tc_respect tc tc2) :
    tc_respect tc tc_max.
  Proof.
    destruct Hrespect1 as (Hdmono1 & Himono1), Hrespect2 as (Hdmono2 & Himono2).
    constructor.
    - rewrite -> Foralltc_Forall_subtree, List.Forall_forall in Hdmono1, Hdmono2 |- *.
      intros sub Hin.
      apply dmono_single_pointwise_max_preserve; firstorder.
    - rewrite -> Foralltc_Forall_subtree, List.Forall_forall in Himono1, Himono2 |- *.
      intros sub Hin.
      apply imono_single_pointwise_max_preserve; firstorder.
  Qed.

End Pointwise_Treeclock.

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

Fact tc_respect_sub tc tc' (H : tc_respect tc tc') :
  Foralltc (fun sub => tc_respect sub tc') tc.
Proof.
  pose proof (conj (dmono _ _ H) (imono _ _ H)) as HH.
  rewrite <- Foralltc_and, <- Foralltc_idempotent in HH.
  eapply Foralltc_impl.
  2: apply HH.
  simpl.
  setoid_rewrite -> Foralltc_and.
  intros. 
  now constructor.
Qed.

Lemma dmono_prefix_preserve tc : 
  forall tc' (Hprefix : prefixtc tc' tc)
    tc_larger (Hdmono : Foralltc (dmono_single tc_larger) tc),
  Foralltc (dmono_single tc_larger) tc'.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  pose proof Hprefix as Hprefix_backup.
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  injection Htmp as ->.
  subst clk' aclk'.
  rewrite -> Foralltc_cons_iff in Hdmono |- *.
  destruct Hdmono as (Hdmono & Hdmono_chn).
  split.
  - hnf in Hdmono |- *.
    intros Hle.
    eapply tc_ge_prefix_preserve.
    1: apply Hprefix_backup.
    intuition.
  - pose proof (sublist_In _ _ Hsub) as Hsub_in.
    pose proof (Forall2_forall_exists_l _ _ _ Hcorr) as Hcorr_in.
    rewrite -> List.Forall_forall in IH, Hdmono_chn |- *.
    intros ch' Hin'.
    destruct (Hcorr_in _ Hin') as (ch & Hin_ch & Hprefix).
    specialize (Hdmono_chn _ (Hsub_in _ Hin_ch)).
    eapply IH; eauto.
Qed.

Lemma imono_prefix_preserve tc : 
  forall tc' (Hprefix : prefixtc tc' tc)
    tc_larger (Himono : Foralltc (imono_single tc_larger) tc),
  Foralltc (imono_single tc_larger) tc'.
Proof.
  induction tc as [(u, clk_u, aclk_u) chn IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  injection Htmp as ->.
  subst clk' aclk'.
  rewrite -> Foralltc_cons_iff in Himono |- *.
  destruct Himono as (Himono & Himono_chn).
  pose proof (sublist_In _ _ Hsub) as Hsub_in.
  pose proof (Forall2_forall_exists_l _ _ _ Hcorr) as Hcorr_in.
  split.
  - hnf in Himono |- *.
    rewrite -> List.Forall_forall in Himono |- *.
    intros [(v', clk_v', aclk_v') chn_v'] Hin' Hle.
    destruct (Hcorr_in _ Hin') as (ch & Hin_ch & Hprefix).
    specialize (Himono _ (Hsub_in _ Hin_ch)).
    destruct ch as [(v, clk_v, aclk_v) chn_v].
    pose proof Hprefix as Hprefix_backup.
    apply prefixtc_inv in Hprefix.
    destruct Hprefix as (Htmp & _).
    injection Htmp as ->.
    subst clk_v' aclk_v'.
    eapply tc_ge_prefix_preserve.
    1: apply Hprefix_backup.
    intuition.
  - rewrite -> List.Forall_forall in IH, Himono_chn |- *.
    intros ch' Hin'.
    destruct (Hcorr_in _ Hin') as (ch & Hin_ch & Hprefix).
    specialize (Himono_chn _ (Hsub_in _ Hin_ch)).
    eapply IH; eauto.
Qed.

Lemma tc_respect_prefix_preserve tc tc' (Hprefix : prefixtc tc' tc)
  tc_larger (Hrespect : tc_respect tc tc_larger) :
  tc_respect tc' tc_larger.
Proof.
  constructor.
  - apply dmono in Hrespect.
    eapply dmono_prefix_preserve; eauto.
  - apply imono in Hrespect.
    eapply imono_prefix_preserve; eauto.
Qed.

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
  aclk_decsorted: Foralltc tc_chn_aclk_decsorted tc
  (* this is only useful to guarantee that the domain of join is the union of two operands *)
  (* clk_lowerbound: Foralltc (fun tc' => 0 < tc_rootclk tc') tc *)
}.

Lemma tid_nodup_chn_ch chn
  (H : List.NoDup (map tc_roottid (flat_map tc_flatten chn)))
  ch (Hin : In ch chn) : List.NoDup (map tc_roottid (tc_flatten ch)).
Proof.
  rewrite -> flat_map_concat_map, -> concat_map, -> map_map in H.
  apply NoDup_concat in H.
  rewrite -> List.Forall_map, List.Forall_forall in H.
  now apply H.
Qed.

(* this essentially tells that tid_nodup iff all subtrees are tid_nodup *)

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

Lemma tid_nodup_prefix_preserve tc tc' (Hprefix : prefixtc tc tc') 
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc'))) : 
  List.NoDup (map tc_roottid (tc_flatten tc)).
Proof.
  (* use prefix domain *)
  revert tc' Hprefix Hnodup.
  induction tc as [(u, clk, aclk) chn_sp IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn].
  pose proof (prefixtc_flatten_sublist _ _ Hprefix) as Hdomsub. 
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  injection Htmp as <-.
  subst clk' aclk'.
  simpl in Hnodup, Hdomsub |- *.
  apply sublist_map with (f:=info_tid) in Hdomsub.
  simpl in Hdomsub.
  rewrite -> ! map_map in Hdomsub.
  fold tc_roottid in Hdomsub.
  eapply sublist_NoDup; eauto.
Qed.

Lemma tid_nodup_root_chn_split tcs
  (Hnodup : List.NoDup (map tc_roottid (flat_map tc_flatten tcs))) : 
  List.NoDup (map tc_roottid tcs) /\ List.NoDup (map tc_roottid (flat_map tc_flatten (flat_map tc_rootchn tcs))).
Proof.
  pose proof (tc_flatten_root_chn_split tcs) as Hperm.
  apply Permutation.Permutation_map with (f:=tc_roottid) in Hperm.
  rewrite -> map_app in Hperm.
  apply Permutation.Permutation_NoDup in Hperm.
  2: assumption.
  now rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hperm.
Qed.

Fact tc_shape_inv_conj_iff tc : 
  tc_shape_inv tc <-> 
    (List.NoDup (map tc_roottid (tc_flatten tc))
    /\ Foralltc tc_chn_aclk_ub tc
    /\ Foralltc tc_chn_aclk_decsorted tc).
Proof.
  split.
  - now intros [? ? ?].
  - intros.
    now constructor.
Qed.

Fact tc_shape_inv_root_aclk_useless u clk aclk aclk' chn 
  (Hshape : tc_shape_inv (Node (mkInfo u clk aclk) chn)) :
  tc_shape_inv (Node (mkInfo u clk aclk') chn).
Proof.
  constructor.
  - apply tid_nodup in Hshape.
    now simpl in *.
  - apply aclk_upperbound in Hshape.
    rewrite -> ! Foralltc_cons_iff in Hshape |- *.
    now simpl in *.
  - apply aclk_decsorted in Hshape.
    rewrite -> ! Foralltc_cons_iff in Hshape |- *.
    now simpl in *.
Qed.

Lemma tc_shape_inv_sub tc (Hshape : tc_shape_inv tc) : Forall tc_shape_inv (tc_flatten tc).
Proof.
  apply tc_shape_inv_conj_iff in Hshape.
  rewrite -> ! Foralltc_Forall_subtree in Hshape.
  change tc_shape_inv with (fun tc' => tc_shape_inv tc').
  setoid_rewrite -> tc_shape_inv_conj_iff.
  repeat apply Forall_and.
  2-3: now rewrite <- Foralltc_Forall_subtree, -> Foralltc_idempotent, -> Foralltc_Forall_subtree.
  now rewrite <- Foralltc_Forall_subtree, <- tid_nodup_Foralltc_id.
Qed.

Corollary tc_shape_inv_chn ni chn (Hshape : tc_shape_inv (Node ni chn)) :
  Forall tc_shape_inv chn.
Proof.
  apply tc_shape_inv_sub in Hshape.
  simpl in Hshape.
  apply Forall_cons_iff, proj2, Forall_flat_map in Hshape.
  rewrite -> List.Forall_forall in Hshape |- *.
  intros [? ?] Hin.
  specialize (Hshape _ Hin).
  simpl in Hshape.
  now apply Forall_cons_iff, proj1 in Hshape.
Qed.

(* prefix also have shape inv *)

Lemma tc_shape_inv_prefix_preserve tc tc' (Hprefix : prefixtc tc tc') 
  (Hshape : tc_shape_inv tc') : tc_shape_inv tc.
Proof.
  revert tc' Hprefix Hshape.
  induction tc as [(u, clk, aclk) chn_sp IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn].
  apply prefixtc_inv in Hprefix.
  destruct Hprefix as (Htmp & (chn_sub & Hsub & Hcorr)).
  injection Htmp as <-.
  subst clk' aclk'.
  pose proof (sublist_In _ _ Hsub) as Hsub_in.
  pose proof (Forall2_forall_exists_l _ _ _ Hcorr) as Hcorr_in.
  pose proof (tc_shape_inv_chn _ _ Hshape) as Hshape_chn.
  rewrite -> List.Forall_forall in IH, Hshape_chn.
  assert (forall x, In x chn_sp -> tc_shape_inv x) as Hshape_sp.
  {
    intros x Hin.
    destruct (Hcorr_in _ Hin) as (y & Hin_sub & Hprefix_sub).
    specialize (Hsub_in _ Hin_sub).
    firstorder.
  }
  pose proof Hcorr as Hrootinfo.
  eapply list.Forall2_impl in Hrootinfo.
  2: apply prefixtc_rootinfo_same.
  pose proof (Forall2_forall_exists_l _ _ _ Hrootinfo) as Hrootinfo_in.
  constructor.
  - apply tid_nodup in Hshape.
    eapply tid_nodup_prefix_preserve; eauto.
    econstructor; eauto.
  - constructor.
    + apply aclk_upperbound, Foralltc_self in Hshape.
      simpl in Hshape |- *.
      rewrite -> List.Forall_forall in Hshape |- *.
      unfold tc_rootaclk in Hshape |- *.
      firstorder congruence.
    + rewrite -> List.Forall_forall.
      firstorder.
  - constructor.
    + apply aclk_decsorted, Foralltc_self in Hshape.
      simpl in Hshape |- *.
      assert (map tc_rootaclk chn_sp = map tc_rootaclk chn_sub) as ->.
      {
        clear -Hrootinfo.
        induction Hrootinfo.
        - auto.
        - simpl. unfold tc_rootaclk in *. congruence.
      }
      eapply sublist_map with (f:=tc_rootaclk) in Hsub.
      eapply sublist_StronglySorted; eauto.
    + rewrite -> List.Forall_forall.
      firstorder.
Qed.

(* exploit some simple cases, which may be not generalizable but simpler ... *)

Lemma tc_shape_inv_prepend_child ni chn (Hshape : tc_shape_inv (Node ni chn))
  tc_new (Hshape_new : tc_shape_inv tc_new)
  (Hnointersect : forall t, tc_getnode t tc_new -> tc_getnode t (Node ni chn) -> False)
  (Haclk_bounded : tc_rootaclk tc_new <= info_clk ni)
  (Haclk_ge : tc_rootaclk tc_new >= match chn with ch :: _ => tc_rootaclk ch | nil => 0 end) :
  tc_shape_inv (Node ni (tc_new :: chn)).
Proof.
  constructor.
  - repeat setoid_rewrite <- tc_getnode_subtc_iff in Hnointersect.
    eapply Permutation.Permutation_NoDup with 
      (l:=map tc_roottid ((tc_flatten tc_new) ++ (tc_flatten (Node ni chn)))).
    + simpl.
      rewrite -> ! map_app.
      simpl.
      symmetry.
      apply Permutation.Permutation_middle.
    + rewrite -> map_app.
      rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
      setoid_rewrite -> base.elem_of_list_In.
      now apply tid_nodup in Hshape, Hshape_new.
  - constructor.
    + apply aclk_upperbound, Foralltc_self in Hshape.
      simpl in Hshape |- *.
      destruct ni as (?, ?, ?).
      simpl in Haclk_bounded.
      constructor; auto.
    + apply aclk_upperbound in Hshape, Hshape_new.
      apply Foralltc_cons_iff in Hshape.
      now constructor.
  - constructor.
    + apply aclk_decsorted, Foralltc_self in Hshape.
      simpl in Hshape |- *.
      constructor.
      1: assumption.
      destruct chn as [ | ch chn ].
      * now simpl.
      * simpl.
        constructor.
        1: assumption.
        simpl in Hshape.
        apply StronglySorted_inv in Hshape.
        rewrite -> List.Forall_forall in Hshape |- *.
        intros x Hin.
        pose proof (proj2 Hshape _ Hin).
        lia.
    + apply aclk_decsorted in Hshape, Hshape_new.
      apply Foralltc_cons_iff in Hshape.
      now constructor.
Qed.

(* purely computational *)

Fact tc_get_updated_nodes_join_aux_app tc u' chn1 chn2 
  (H : Forall (fun tc' => (tc_getclk u' tc) < tc_rootaclk tc' \/ (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc') chn1) :
  tc_get_updated_nodes_join_aux tc u' (chn1 ++ chn2) =
  tc_get_updated_nodes_join_aux tc u' chn1 ++ tc_get_updated_nodes_join_aux tc u' chn2.
Proof.
  revert chn2. 
  induction chn1 as [ | [ (v', clk_v', aclk_v') ? ] chn1 IH ]; intros; simpl; auto.
  rewrite Forall_cons_iff in H.
  destruct H as (H1 & H2).
  simpl in H1.
  rewrite IH; auto.
  destruct (clk_v' <=? tc_getclk v' tc) eqn:E1, (aclk_v' <=? tc_getclk u' tc) eqn:E2; auto.
  apply Nat.leb_le in E1, E2; lia.
Qed.

Lemma tc_get_updated_nodes_join_aux_result tc u' chn_u'
  (Haclk_impl_clk : forall tc', In tc' chn_u' -> 
    tc_rootaclk tc' <= (tc_getclk u' tc) -> 
    tc_rootclk tc' <= (tc_getclk (tc_roottid tc') tc)) 
  (Hsorted: StronglySorted ge (map tc_rootaclk chn_u')) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc u' chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => In tc' chn_u'' <-> 
      ((tc_getclk (tc_roottid tc') tc) < tc_rootclk tc' /\
        (tc_getclk u' tc) < tc_rootaclk tc')) chn_u').
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
  apply Forall2_mapself_l.
  pose proof (sublist_In _ _ Hsub).
  rewrite -> List.Forall_forall in IH |- *.
  firstorder.
Qed.

Fact imono_single_aclk_impl_clk tc u' clk_u' aclk_u' chn_u'
  (Himono : imono_single tc (Node (mkInfo u' clk_u' aclk_u') chn_u')) :
  forall tc', In tc' chn_u' -> 
    tc_rootaclk tc' <= (tc_getclk u' tc) -> 
    tc_rootclk tc' <= (tc_getclk (tc_roottid tc') tc).
Proof.
  intros tc_v' Hin' Hle.
  (* use imono *)
  simpl in Himono.
  rewrite -> List.Forall_forall in Himono.
  specialize (Himono _ Hin').
  destruct tc_v' as [(v', clk_v', aclk_v') chn_v'].
  simpl in Hle, Himono |- *.
  now apply Himono, Foralltc_self in Hle.
Qed.

Lemma tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn_u' 
  (Hshape_tc' : tc_shape_inv (Node (mkInfo u' clk_u' aclk_u') chn_u')) 
  (Hrespect : tc_respect (Node (mkInfo u' clk_u' aclk_u') chn_u') tc) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc u' chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => ~ In tc' chn_u'' <-> tc_ge tc tc') chn_u') /\
    (Forall (fun tc' => In tc' chn_u'' <-> (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc') chn_u') /\
    (Forall (fun tc' => (tc_getclk u' tc) < tc_rootaclk tc') chn_u'').
Proof.
  pose proof (tc_get_updated_nodes_join_aux_result tc u' chn_u') as H.
  (* get aclk_impl_clk *)
  pose proof (imono _ _ Hrespect) as Himono.
  apply Foralltc_cons_iff, proj1 in Himono.
  pose proof (imono_single_aclk_impl_clk _ _ _ _ _ Himono) as Haclk_impl_clk.
  pose proof (fun tc' H => contra_not (Haclk_impl_clk tc' H)) as Haclk_impl_clk'.
  repeat setoid_rewrite -> Nat.nle_gt in Haclk_impl_clk'.
  removehead H.
  2: assumption.
  removehead H.
  2: now apply aclk_decsorted, Foralltc_cons_iff in Hshape_tc'.
  destruct H as (chn_u'' & Hsub & Hres & Halllt).
  exists chn_u''.
  split.
  1: assumption.
  split.
  1: assumption.
  (* the subsumption part *)
  rewrite -> List.Forall_forall in Halllt.
  assert (forall x : treeclock, In x chn_u' ->
    ~ In x chn_u'' <-> tc_rootclk x <= tc_getclk (tc_roottid x) tc) as Halllt'.
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
    2: apply Foralltc_self in H; now destruct ch as [(?, ?, ?) ?].
    (* use dmono *)
    apply dmono, Foralltc_cons_iff in Hrespect.
    destruct Hrespect as (_ & Hdmono).
    rewrite -> List.Forall_forall in Hdmono.
    specialize (Hdmono _ Hin).
    apply Foralltc_self in Hdmono.
    destruct ch as [(?, ?, ?) ?].
    firstorder.
  - firstorder.
  - intros ch Hin.
    pose proof (sublist_In _ _ Hsub _ Hin).
    firstorder.
Qed.

(* make it over the whole tree; also soundness *)

Corollary tc_get_updated_nodes_join_shape tc' (Hshape: tc_shape_inv tc') : 
  forall tc (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc'),
  Foralltc (fun tc' => tc_getclk (tc_roottid tc') tc < tc_rootclk tc') 
    (tc_get_updated_nodes_join tc tc') /\
  Foralltc (fun tc' => let: Node ni chn := tc' in
    Forall (fun tc' => tc_getclk (info_tid ni) tc < tc_rootaclk tc') chn) 
    (tc_get_updated_nodes_join tc tc').
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  rewrite -> List.Forall_forall in IH.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & -> & _ & Halllt & Halllt').
  rewrite -> List.Forall_forall in Halllt, Halllt'.
  pose proof (sublist_In _ _ Hsub) as Hsub_in.
  pose proof (tc_shape_inv_chn _ _ Hshape) as Hshape_ch.
  pose proof (tc_respect_chn _ _ _ Hrespect) as Hrespect_ch.
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

Corollary tc_get_updated_nodes_join_sound tc' (Hshape: tc_shape_inv tc')
  tc (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') :
  forall t, tc_getnode t (tc_get_updated_nodes_join tc tc') ->
    tc_getclk t tc < tc_getclk t tc'.
Proof.
  pose proof (tc_get_updated_nodes_join_shape _ Hshape _ Hrespect Hroot_clk_le) as H.
  apply proj1, Foralltc_Forall_subtree in H.
  intros t Hres.
  rewrite <- tc_getnode_subtc_iff, -> in_map_iff in Hres.
  destruct Hres as (sub & <- & Hin).
  pose proof Hin as Einfo.
  apply in_map with (f:=tc_rootinfo) in Einfo.
  eapply prefixtc_flatten_info_incl in Einfo.
  2: apply tc_get_updated_nodes_join_is_prefix.
  rewrite -> in_map_iff in Einfo.
  destruct Einfo as (sub' & Einfo & Hin').
  pose proof (tc_rootinfo_tid_inj _ _ Einfo) as Et.
  pose proof (tc_rootinfo_clk_inj _ _ Einfo) as Eclk.
  pose proof (tid_nodup_find_self _ (tid_nodup _ Hshape)) as Hself.
  rewrite -> List.Forall_forall in H, Hself.
  specialize (H _ Hin).
  specialize (Hself _ Hin').
  rewrite -> Et in Hself.
  unfold tc_getclk at 2.
  unfold tc_getnode.
  rewrite -> Hself.
  congruence.
Qed.

Corollary tc_get_updated_nodes_join_complete tc' (Hshape': tc_shape_inv tc') : 
  forall tc (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc')
  t (Hlt : tc_getclk t tc < tc_getclk t tc'),
    (* this equality can be from the prefix property; no need to repeat *)
    (* base.fmap tc_rootinfo (tc_getnode t (tc_get_updated_nodes_join tc tc')) = 
    base.fmap tc_rootinfo (tc_getnode t tc'). *)
    (tc_getnode t (tc_get_updated_nodes_join tc tc')).
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  simpl in Hroot_clk_le. 
  tc_get_updated_nodes_join_unfold.
  unfold tc_getclk in Hlt at 2.
  cbn in Hlt |- *.
  destruct (eqdec u' t) as [ <- | Htneq ] eqn:Etdec.
  1: intuition.
  (* get sub inv *)
  assert (NoDup (map tc_roottid (flat_map tc_flatten chn'))) as Hnodup_chn'
    by (now apply tid_nodup, NoDup_cons_iff in Hshape').
  (* get the result of tc_get_updated_nodes_join_aux *)
  pose proof (tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn') as Htmp.
  do 2 (removehead Htmp; [ | assumption ]).
  destruct Htmp as (chn_u'' & Hsub & Hsubmap & Hgetjoinres & Halllt & Halllt').
  rewrite -> Hsubmap.
  rewrite -> List.Forall_forall in Hgetjoinres, Halllt.

  destruct (find (has_same_tid t) (flat_map tc_flatten chn')) as [ res | ] eqn:E.
  2: now destruct (tc_getnode t tc).
  simpl.
  apply find_some in E.
  destruct E as (Hin & Et).
  rewrite -> has_same_tid_true in Et.
  rewrite -> in_flat_map in Hin.
  destruct Hin as (ch & Hin_ch & Hin).

  (* tc_rootclk res --> getclk t ch *)
  pose proof (tid_nodup_find_self (tc_flatten ch)) as Hres_ch.
  removehead Hres_ch.
  2: apply tid_nodup in Hshape'; eapply tid_nodup_chn_ch; eauto.
  rewrite -> List.Forall_forall in Hres_ch.
  specialize (Hres_ch _ Hin).
  assert (tc_rootclk res = tc_getclk t ch) as Eclk_ch.
  1: subst t; unfold tc_getclk, tc_getnode; now rewrite -> Hres_ch.
  rewrite -> Eclk_ch in Hlt.
  pose proof (tc_shape_inv_chn _ _ Hshape') as Hshape_chn.
  pose proof (tc_respect_chn _ _ _ Hrespect) as Hrespect_chn.
  rewrite -> List.Forall_forall in IH, Hshape_chn, Hrespect_chn.
  (* now decide in or not? *)
  destruct (in_dec treeclock_eqdec ch chn_u'') as [ Hin_ch' | Hnotin ].
  + (* use IH *)
    pose proof Hin_ch' as Hlt_ch.
    rewrite -> Halllt in Hlt_ch.
    2: assumption.
    specialize (IH _ Hin_ch (Hshape_chn _ Hin_ch) _ (Hrespect_chn _ Hin_ch) Hlt_ch _ Hlt).
    destruct (tc_getnode t (tc_get_updated_nodes_join tc ch)) as [ res' | ] eqn:E.
    2: discriminate.
    apply find_some in E.
    destruct E as (Hres' & Et'').
    rewrite -> has_same_tid_true in Et''.
    destruct (find (has_same_tid t)
      (flat_map tc_flatten (map (tc_get_updated_nodes_join tc) chn_u''))) as [ res'' | ] eqn:Efind.
    * auto.
    * eapply find_none in Efind.
      2:{
        eapply in_flat_map_conv.
        2: apply Hres'.
        now apply in_map.
      }
      now rewrite -> has_same_tid_false in Efind.
  + (* make contradiction by tc_ge *)
    rewrite -> Hgetjoinres in Hnotin.
    2: assumption.
    eapply Foralltc_Forall_subtree, List.Forall_forall in Hnotin.
    2: apply Hin.
    subst t.
    destruct res as [(?, ?, ?) ?].
    simpl in *.
    lia.
Qed.

Corollary tc_get_updated_nodes_join_adequacy tc' (Hshape: tc_shape_inv tc')
  tc (Hrespect: tc_respect tc' tc)
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') t :
  tc_getclk t tc < tc_getclk t tc' <->
  tc_getnode t (tc_get_updated_nodes_join tc tc').
Proof.
  split; intros H.
  - now apply tc_get_updated_nodes_join_complete.
  - now apply tc_get_updated_nodes_join_sound.
Qed.

(* turn the properties of forest in snd to those on fst *)

Lemma tc_detach_nodes_snd2fst tcs tc :
  Forall (fun tc' => exists sub, In sub (tc_flatten tc) /\ 
    tc' = fst (tc_detach_nodes tcs sub))
  (snd (tc_detach_nodes tcs tc)).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  simpl.
  (* TODO much repetition. make these domain-specific tactic? *)
  destruct (List.split (map (tc_detach_nodes tcs) chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs) new_chn)
    as (res', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
  simpl.
  rewrite -> List.Forall_app, ! List.Forall_forall.
  split.
  - subst res.
    setoid_rewrite -> in_concat.
    setoid_rewrite -> in_map_iff.
    intros res_ch (? & (ch & <- & Hin_ch) & Hin).
    specialize (IH _ Hin_ch _ Hin).
    destruct IH as (sub & Hin_sub & ->).
    exists sub.
    split; [ right; eapply in_flat_map_conv in Hin_sub; eauto | reflexivity ].
  - subst res' new_chn.
    setoid_rewrite -> filter_In.
    setoid_rewrite -> in_map_iff.
    intros ? ((ch & <- & Hin_ch) & _).
    exists ch.
    split. 
    2: reflexivity.
    right. 
    eapply in_flat_map_conv in Hin_ch; eauto.
    destruct ch as [(?, ?, ?) ?].
    simpl.
    intuition.
Qed.

Lemma tc_detach_nodes_dom_incl tcs tc :
  Forall (fun tc' => find (has_same_tid (tc_roottid tc')) tcs)
  (snd (tc_detach_nodes tcs tc)).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite -> List.Forall_forall in IH.
  setoid_rewrite -> List.Forall_forall in IH.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs) chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs) new_chn)
    as (res', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
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
  (H : forall x, In x (map tc_roottid tcs1) <-> In x (map tc_roottid tcs2)) tc :
  tc_detach_nodes tcs1 tc = tc_detach_nodes tcs2 tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  rewrite -> map_ext_Forall with (g:=(tc_detach_nodes tcs2)); auto.
  destruct (List.split (map (tc_detach_nodes tcs2) chn)) as (new_chn, res) eqn:Esplit.
  rewrite -> partition_ext_Forall with (g:=(fun tc' => find (has_same_tid (tc_roottid tc')) tcs2)); auto.
  apply Forall_forall.
  intros tc' _.
  match goal with |- ?b1 = ?b2 => enough (is_true b1 <-> is_true b2) as Hq
    by (destruct b1, b2; simpl in Hq; try reflexivity; exfalso; intuition) end.
  now rewrite <- ! tc_getnode_in_iff.
Qed.

Lemma tc_detach_nodes_fst_is_prefix tcs tc :
  prefixtc (fst (tc_detach_nodes tcs tc)) tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs) chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs) new_chn)
    as (res', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
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
  Forall (fun tc' => exists sub, In sub (tc_flatten tc) /\
    prefixtc tc' sub) (snd (tc_detach_nodes tcs tc)).
Proof.
  pose proof (tc_detach_nodes_snd2fst tcs tc) as Hto.
  rewrite -> List.Forall_forall in Hto |- *.
  intros sub' Hin'.
  specialize (Hto sub' Hin').
  destruct Hto as (sub & Hin & ->).
  pose proof (tc_detach_nodes_fst_is_prefix tcs sub).
  eauto.
Qed.

(* FIXME: use this to rewrite *)
Corollary tc_detach_nodes_fst_rootinfo_same tcs tc : 
  tc_rootinfo (fst (tc_detach_nodes tcs tc)) = tc_rootinfo tc.
Proof. erewrite prefixtc_rootinfo_same; [ reflexivity | apply tc_detach_nodes_fst_is_prefix ]. Qed.

Lemma tc_detach_nodes_tcs_app_fst tcs1 tcs2 tc :
  fst (tc_detach_nodes tcs2 (fst (tc_detach_nodes tcs1 tc))) =
  fst (tc_detach_nodes (tcs1 ++ tcs2) tc).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs1) chn))
    as (new_chn1, res1) eqn:Esplit1, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs1) new_chn1)
    as (res1', new_chn1') eqn:Epar1, 
    (List.split (map (tc_detach_nodes (tcs1 ++ tcs2)) chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) (tcs1 ++ tcs2)) new_chn)
    as (res', new_chn') eqn:Epar.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs2) new_chn1'))
    as (new_chn2, res2) eqn:Esplit2, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs2) new_chn2)
    as (res2', new_chn2') eqn:Epar2.
  simpl.
  f_equal.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit1, Esplit2, Esplit.
  rewrite -> partition_filter in Epar1, Epar2, Epar.
  apply pair_equal_split in Esplit1, Esplit2, Esplit, Epar1, Epar2, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn'), 
    Esplit1 as (Enew_chn1 & Eres1), Epar1 as (Eres1' & Enew_chn1'), 
    Esplit2 as (Enew_chn2 & Eres2), Epar2 as (Eres2' & Enew_chn2').
  subst.
  rewrite <- (map_ext_Forall _ _ IH).

  (* local induction to avoid too much manipulation *)
  clear ni IH. 
  induction chn as [ | ch chn IH ]; simpl; auto.
  unfold tc_roottid in *.
  pose proof (fun tc => tc_detach_nodes_fst_is_prefix tcs1 tc) as Hpf1.
  pose proof (fun tc => tc_detach_nodes_fst_is_prefix tcs2 tc) as Hpf2.
  rewrite ! (prefixtc_rootinfo_same _ _ (Hpf2 _)).
  rewrite ! (prefixtc_rootinfo_same _ _ (Hpf1 _)).
  rewrite find_app.
  destruct (find (has_same_tid (info_tid (tc_rootinfo ch))) tcs1) as [ res1 | ] eqn:E1; simpl.
  - apply IH.
  - rewrite ! (prefixtc_rootinfo_same _ _ (Hpf2 _)).
    rewrite ! (prefixtc_rootinfo_same _ _ (Hpf1 _)).
    destruct (find (has_same_tid (info_tid (tc_rootinfo ch))) tcs2) as [ res2 | ] eqn:E2; simpl.
    + apply IH.
    + f_equal; apply IH.
Qed.

Lemma tc_detach_nodes_tcs_app_snd tcs1 tcs2 tc :
  Permutation.Permutation (snd (tc_detach_nodes (tcs1 ++ tcs2) tc))
  (snd (tc_detach_nodes tcs2 (fst (tc_detach_nodes tcs1 tc))) ++
    map fst (map (tc_detach_nodes tcs2) (snd (tc_detach_nodes tcs1 tc))) ++
    flat_map snd (map (tc_detach_nodes tcs2) (snd (tc_detach_nodes tcs1 tc)))).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs1) chn))
    as (new_chn1, res1) eqn:Esplit1, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs1) new_chn1)
    as (res1', new_chn1') eqn:Epar1, 
    (List.split (map (tc_detach_nodes (tcs1 ++ tcs2)) chn))
    as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) (tcs1 ++ tcs2)) new_chn)
    as (res', new_chn') eqn:Epar.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs2) new_chn1'))
    as (new_chn2, res2) eqn:Esplit2, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs2) new_chn2)
    as (res2', new_chn2') eqn:Epar2.
  simpl.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit1, Esplit2, Esplit.
  rewrite -> partition_filter in Epar1, Epar2, Epar.
  apply pair_equal_split in Esplit1, Esplit2, Esplit, Epar1, Epar2, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn'), 
    Esplit1 as (Enew_chn1 & Eres1), Epar1 as (Eres1' & Enew_chn1'), 
    Esplit2 as (Enew_chn2 & Eres2), Epar2 as (Eres2' & Enew_chn2').

  (* now, manipulate *)
  pose proof IH as Hperm.
  apply Permutation_Forall_flat_map in Hperm.
  rewrite -> flat_map_concat_map, -> Eres in Hperm at 1.
  rewrite -> ! Permutation_flat_map_innerapp_split in Hperm.
  rewrite -> flat_map_concat_map in Hperm at 1.
  rewrite <- map_map with (g:=fun x => snd (tc_detach_nodes tcs2 x)) in Hperm at 1.
  rewrite -> Enew_chn1, <- flat_map_concat_map in Hperm.
  (* split new_chn1, get res1' and res2 *)
  match type of Hperm with Permutation.Permutation ?al ?bl => 
    eapply Permutation.Permutation_trans with (l:=al) (l':=bl) in Hperm end.
  2: apply Permutation.Permutation_app; [ | reflexivity ].
  2: apply Permutation.Permutation_flat_map, Permutation_split_combine.
  rewrite -> Eres1', -> Enew_chn1' in Hperm.
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
  match type of Hperm with Permutation.Permutation _ ?al =>
    transitivity (al ++ (res2' ++ map fst (map (tc_detach_nodes tcs2) res1'))) end.
  2:{
    apply Permutation.Permutation_count_occ with (eq_dec:=treeclock_eqdec).
    intros. rewrite ! count_occ_app with (eq_dec:=treeclock_eqdec).
    lia.
  }
  apply Permutation.Permutation_app; auto.

  subst.
  clear -chn.
  rewrite -> ! map_filter_comm, -> ! map_map.
  erewrite -> map_ext; [ | intros; now rewrite tc_detach_nodes_tcs_app_fst ].
  f_equal.
  erewrite -> filter_ext with (l:=filter _ _); [ | intros; now rewrite tc_detach_nodes_tcs_app_fst ].
  rewrite <- map_app.
  apply Permutation.Permutation_map.
  repeat match goal with |- context[filter ?ff ?ll] => 
    match ff with context[fst] => 
    erewrite -> filter_ext with (f:=ff) (l:=ll); [ | intros x; unfold tc_roottid; 
      rewrite (prefixtc_rootinfo_same _ _ (tc_detach_nodes_fst_is_prefix _ _)); fold (tc_roottid x); reflexivity ]
    end
  end.
  induction chn as [ | ch chn IH ]; simpl; auto.
  rewrite find_app.
  destruct (find (has_same_tid (tc_roottid ch)) tcs1) as [ res1 | ] eqn:E1, 
    (find (has_same_tid (tc_roottid ch)) tcs2) as [ res2 | ] eqn:E2; 
    simpl; try rewrite E1; try rewrite E2; simpl; try rewrite IH.
  all: apply Permutation.Permutation_count_occ with (eq_dec:=treeclock_eqdec).
  all: intros; simpl; rewrite ! count_occ_app with (eq_dec:=treeclock_eqdec); simpl.
  all: destruct (treeclock_eqdec ch x); simpl; try lia.
Qed.

(* a niche case *)
Fact tc_detach_nodes_prepend_child ni ch chn tcs 
  (H : find (has_same_tid (tc_roottid ch)) tcs = None) :
  let: (pivot_ch, forest_ch) := tc_detach_nodes tcs ch in
  let: (pivot_main, forest_main) := tc_detach_nodes tcs (Node ni chn) in
  let: Node ni' chn' := pivot_main in
  tc_detach_nodes tcs (Node ni (ch :: chn)) = 
  (Node ni' (pivot_ch :: chn'), forest_ch ++ forest_main).
Proof.
  simpl.
  destruct (tc_detach_nodes tcs ch) as (pivot_ch, forest_ch) eqn:Ech, 
    (List.split (map (tc_detach_nodes tcs) chn)) as (new_chn, res) eqn:Esplit, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs) new_chn)
    as (res', new_chn') eqn:Epar.
  simpl.
  rewrite -> Epar.
  unfold tc_roottid in H |- * at 1.
  replace pivot_ch with (fst (tc_detach_nodes tcs ch)) by now rewrite Ech.
  rewrite ! (prefixtc_rootinfo_same _ _ (tc_detach_nodes_fst_is_prefix tcs ch)), Ech, H.
  simpl.
  now rewrite app_assoc.
Qed.

Fact tc_detach_nodes_intact tcs tc
  (Hdj : forall t, In t (map tc_roottid (flat_map tc_flatten (tc_rootchn tc))) -> 
    In t (map tc_roottid tcs) -> False) :
  tc_detach_nodes tcs tc = (tc, nil).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl in *.
  epose proof (Forall_impl_impl _ _ _ IH ?[Goalq]) as Htmp.
  [Goalq]:{
    apply Forall_forall.
    intros ch Hin_ch t Hin.
    apply Hdj, map_flat_map_In.
    exists ch.
    destruct ch; simpl in *; eqsolve.
  }
  erewrite -> map_ext_Forall; [ | apply Htmp ].
  (* TODO repeat the typical proof steps related with tc_detach_nodes *)
  destruct (List.split (map (fun ch : treeclock => (ch, nil)) chn))
    as (new_chn, forest) eqn:Esplit, 
    (partition (fun tc' => find (has_same_tid (tc_roottid tc')) tcs) new_chn)
    as (forest', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  simpl in Esplit.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
  rewrite -> map_id_eq in Enew_chn.
  subst new_chn.
  replace (concat forest) with (@nil treeclock) in *.
  2:{ 
    symmetry; apply concat_nil_Forall.
    subst forest. 
    now apply List.Forall_map, Forall_forall.
  }
  simpl.
  match type of Enew_chn' with filter ?f ?l = _ => 
    assert (forall ch, In ch l -> f ch = true) as HH end.
  { 
    intros ch Hin.
    apply negb_true_iff.
    (* FIXME: how to use proper SSR to solve this? *)
    match goal with |- isSome ?a = false => 
      enough (~ (is_true (isSome a))) by (destruct a; simpl in *; intuition) end.
    rewrite <- tc_getnode_in_iff.
    unfold not. (* ? *)
    apply Hdj, map_flat_map_In.
    exists ch. 
    split; auto. 
    apply in_map, tc_flatten_self_in.
  }
  simpl in HH.
  rewrite -> filter_all_true in Enew_chn'; auto.
  rewrite -> filter_all_false in Eres'.
  2: intros; now apply negb_true_iff, HH.
  congruence.
Qed.

(* permutation is much more clear than mutual In here *)

Lemma tc_detach_nodes_dom_partition tcs tc :
  Permutation.Permutation (map tc_rootinfo (tc_flatten tc))
    (map tc_rootinfo (tc_flatten (fst (tc_detach_nodes tcs tc)) ++ 
      (flat_map tc_flatten (snd (tc_detach_nodes tcs tc))))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  simpl.
  destruct (List.split (map (tc_detach_nodes tcs) chn))
    as (new_chn, forest) eqn:Esplit, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs) new_chn)
    as (forest', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  apply pair_equal_split in Esplit.
  destruct Esplit as (Enew_chn & Eres).
  simpl.
  constructor.
  rewrite -> flat_map_app, -> ! map_app.
  etransitivity.
  2:{
    rewrite -> Permutation.Permutation_app_comm, <- app_assoc, <- map_app, <- flat_map_app.
    apply Permutation.Permutation_app_head, Permutation.Permutation_map, Permutation.Permutation_flat_map.
    match type of Epar with partition ?f ?l = (?a, ?b) => 
      replace a with (fst (partition f l)) by (rewrite -> Epar; now simpl);
      replace b with (snd (partition f l)) by (rewrite -> Epar; now simpl)
    end.
    apply Permutation_partition.
  }
  (* seems a local induction is needed *)
  clear -chn IH Enew_chn Eres.
  revert new_chn forest IH Enew_chn Eres.
  induction chn as [ | ch chn IH2 ]; intros.
  all: simpl in Enew_chn, Eres |- *; subst.
  - reflexivity.
  - apply Forall_cons_iff in IH.
    destruct IH as (HH & IH).
    specialize (IH2 _ _ IH eq_refl eq_refl).
    simpl.
    (* TODO this seems to be quite straightforward, but hard to deal with in Coq! *)
    rewrite -> flat_map_app.
    rewrite -> ! map_app.
    match goal with |- Permutation.Permutation _ ((?a ++ ?b) ++ (?c ++ ?d)) => 
      transitivity ((c ++ a) ++ (b ++ d)) end.
    2:{
      match goal with |- Permutation.Permutation _ ((?a ++ ?b) ++ (?c ++ ?d)) => 
        remember a as la; remember b as lb; remember c as lc; remember d as ld end.
      rewrite -> ! app_assoc with (n:=ld).
      apply Permutation.Permutation_app_tail.
      rewrite <- 2 app_assoc.
      apply Permutation.Permutation_app_rot.
    }
    apply Permutation.Permutation_app.
    + now rewrite <- map_app.
    + assumption.
Qed.

(* TODO troublesome? *)
Corollary tc_detach_nodes_dom_partition_subset tcs tc :
  incl (map tc_rootinfo (tc_flatten (fst (tc_detach_nodes tcs tc))) ++
     map tc_rootinfo (flat_map tc_flatten (flat_map tc_rootchn
            (snd (tc_detach_nodes tcs tc)))))
    (map tc_rootinfo (tc_flatten tc)).
Proof.
  pose proof (tc_detach_nodes_dom_partition tcs tc) as Hperm.
  (* eapply Permutation.Permutation_map with (f:=info_tid) in Hperm.
  rewrite -> ! map_map in Hperm.
  fold tc_rootinfo in Hperm. *)
  intros ni Hin.
  eapply Permutation.Permutation_in.
  1: symmetry; apply Hperm.
  rewrite -> map_app. 
  rewrite -> in_app_iff in Hin |- *.
  destruct Hin as [ Hin | Hin ].
  1: now left.
  right.
  rewrite -> map_flat_map_In in Hin.
  setoid_rewrite -> in_flat_map in Hin.
  destruct Hin as (ch_sub & ([ni_sub chn_sub] & Hin_sub & Hin_ch) & Hin).
  simpl in Hin_ch.
  eapply map_flat_map_In_conv.
  1: apply Hin_sub.
  simpl.
  right.
  apply map_flat_map_In.
  eauto.
Qed.

Corollary tc_detach_nodes_tid_nodup tcs tc 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  NoDup (map tc_roottid (flat_map tc_flatten (snd (tc_detach_nodes tcs tc)))) /\
  (forall t, 
    In t (map tc_roottid (tc_flatten (fst (tc_detach_nodes tcs tc)))) ->
    In t (map tc_roottid (flat_map tc_flatten (snd (tc_detach_nodes tcs tc)))) -> False) /\
  NoDup (map tc_roottid (tc_flatten (fst (tc_detach_nodes tcs tc)))).
Proof.
  pose proof (tc_detach_nodes_dom_partition tcs tc) as Hperm.
  eapply Permutation.Permutation_map with (f:=info_tid) in Hperm.
  rewrite -> ! map_map in Hperm.
  fold tc_roottid in Hperm.
  pose proof (Permutation.Permutation_NoDup Hperm Hnodup) as Htmp.
  rewrite -> map_app, <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Htmp.
  repeat setoid_rewrite -> base.elem_of_list_In in Htmp.
  intuition.
Qed.

(* there will not be any tid in tcs that is also inside the pivot tree *)

Lemma tc_detach_nodes_dom_excl tcs tc :
  forall t (Htarg : find (has_same_tid t) tcs)
  (* res (Hres : tc_getnode t (fst (tc_detach_nodes tcs tc)) = Some res), *)
  res (Hin : In res (tc_flatten (fst (tc_detach_nodes tcs tc)))) (Et : tc_roottid res = t),
  res = (fst (tc_detach_nodes tcs tc)).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  rewrite -> List.Forall_forall in IH.
  simpl in Hin |- *.
  destruct (List.split (map (tc_detach_nodes tcs) chn))
    as (new_chn, forest) eqn:Esplit, 
    (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) tcs) new_chn)
    as (forest', new_chn') eqn:Epar.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
  simpl in Hin |- *.
  destruct Hin as [ | Hin ].
  1: congruence.
  (* now contradiction part *)
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
  now destruct (find (has_same_tid (tc_roottid (fst (tc_detach_nodes tcs ch)))) tcs).
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
  rewrite -> List.Forall_forall in Hto, Hshape_sub |- *.
  intros sub' Hin'.
  specialize (Hto sub' Hin').
  destruct Hto as (sub & Hin & ->).
  specialize (Hshape_sub _ Hin).
  now apply tc_shape_inv_tc_detach_nodes_fst.
Qed.

(* more abstracted version *)

Lemma forest_recombine_pre tcs l
  (Hnodup : NoDup (map tc_roottid tcs)) (Hnodup' : NoDup l) 
  (Hdomincl : incl (map tc_roottid tcs) l) :
  Permutation.Permutation (map Some tcs) 
    (filter isSome (map (fun t => find (has_same_tid t) tcs) l)).
Proof.
  apply Permutation.NoDup_Permutation.
  - apply FinFun.Injective_map_NoDup.
    1: congruence.
    now apply NoDup_map_inv with (f:=tc_roottid).
  - (* no much good way ... induction? *)
    clear Hdomincl.
    revert tcs Hnodup.
    induction l as [ | t l IH ]; intros.
    1: constructor.
    apply NoDup_cons_iff in Hnodup'.
    destruct Hnodup' as (Hnotin & Hnodup').
    simpl.
    destruct (find (has_same_tid t) tcs) as [ res | ] eqn:E; simpl.
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
      pose proof (in_map tc_roottid _ _ Hin) as Hin'.
      pose proof (tid_nodup_find_self _ Hnodup) as Hself.
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
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  (Hnodup' : NoDup (map tc_roottid tcs)) :
  Permutation.Permutation
    (map Some (snd (tc_detach_nodes tcs tc)))
    (filter isSome (map
      (fun t => find (has_same_tid t) (snd (tc_detach_nodes tcs tc))) 
        (map tc_roottid tcs))).
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
    setoid_rewrite <- tc_getnode_in_iff in Hdomincl.
    setoid_rewrite -> in_map_iff in Hdomincl.
    intros ? (sub & <- & Hin).
    firstorder.
Qed.

(* simulation *)

Lemma forest_chn_recombine tcs l 
  (Hperm : Permutation.Permutation (map Some tcs) 
    (filter isSome (map (fun t => find (has_same_tid t) tcs) l))) :
  Permutation.Permutation (flat_map tc_rootchn tcs)
    (flat_map (fun t => match find (has_same_tid t) tcs with
      | Some res => tc_rootchn res
      | None => nil
      end) l).
Proof.
  pose (f:=fun ot => match ot with Some tc => tc_rootchn tc | None => nil end).
  apply Permutation.Permutation_flat_map with (g:=f) in Hperm.
  match type of Hperm with Permutation.Permutation ?a _ => transitivity a end.
  1:{
    clear -thread_eqdec tcs.
    induction tcs as [ | tc tcs IH ].
    1: reflexivity.
    simpl.
    now apply Permutation.Permutation_app_head.
  }
  match type of Hperm with Permutation.Permutation _ ?a => transitivity a end.
  2:{
    clear -thread_eqdec l.
    induction l as [ | x l IH ].
    1: reflexivity.
    simpl.
    destruct (find (has_same_tid x) tcs) eqn:E; simpl.
    - now apply Permutation.Permutation_app_head.
    - assumption.
  }
  assumption.
Qed.

Corollary tc_detach_nodes_forest_recombine tcs tc 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  (Hnodup' : NoDup (map tc_roottid tcs)) :
  Permutation.Permutation
    (flat_map tc_rootchn (snd (tc_detach_nodes tcs tc)))
    (flat_map
      (fun t : thread =>
      match find (has_same_tid t) (snd (tc_detach_nodes tcs tc)) with
      | Some res => tc_rootchn res
      | None => nil
      end) (map tc_roottid tcs)).
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
    map tc_rootinfo chn1 = map tc_rootinfo prefix_chn.
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
    match List.find (has_same_tid t) forest with
    | Some res => tc_rootchn res
    | None => nil
    end) tc (tc_attach_nodes forest tc).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
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

Lemma simple_overlaytc_dom_info (P : thread -> list treeclock) tc : forall tc'
  (Hoverlay : simple_overlaytc P tc tc'),
  Permutation.Permutation (map tc_rootinfo (tc_flatten tc'))
  ((map tc_rootinfo (tc_flatten tc)) ++
    (map tc_rootinfo (flat_map tc_flatten (flat_map P (map tc_roottid (tc_flatten tc)))))).
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
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
  1: apply Permutation.Permutation_app_comm.
  etransitivity.
  2: apply Permutation.Permutation_app_comm.
  rewrite <- app_assoc.
  apply Permutation.Permutation_app_head.
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
    match goal with |- Permutation.Permutation _ ((?a ++ ?b) ++ (?c ++ ?d)) => 
      remember a as la; remember b as lb; remember c as lc; remember d as ld;
      transitivity ((lc ++ la) ++ (lb ++ ld)) end.
    2:{
      rewrite -> ! app_assoc with (n:=ld).
      apply Permutation.Permutation_app_tail.
      rewrite <- 2 app_assoc.
      apply Permutation.Permutation_app_rot.
    }
    apply HH in Hso.
    now apply Permutation.Permutation_app.
Qed.

Corollary tc_attach_nodes_dom_info subtree_tc' tc 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc)))
  (Hnodup' : NoDup (map tc_roottid (tc_flatten subtree_tc'))) :
  Permutation.Permutation (map tc_rootinfo (tc_flatten (tc_attach_nodes (snd (tc_detach_nodes (tc_flatten subtree_tc') tc)) subtree_tc')))
  ((map tc_rootinfo (tc_flatten subtree_tc')) ++
    (map tc_rootinfo (flat_map tc_flatten (flat_map tc_rootchn (snd (tc_detach_nodes (tc_flatten subtree_tc') tc)))))).
Proof.
  pose proof (tc_attach_nodes_result (snd (tc_detach_nodes (tc_flatten subtree_tc') tc)) subtree_tc') as Hso.
  apply simple_overlaytc_dom_info in Hso.
  etransitivity.
  1: apply Hso.
  apply Permutation.Permutation_app_head, Permutation.Permutation_map, Permutation.Permutation_flat_map.
  symmetry.
  now apply tc_detach_nodes_forest_recombine.
Qed.

Lemma simple_overlaytc_nodup (P : thread -> list treeclock) 
  (Hnodup_small : forall t, List.NoDup (map tc_roottid (flat_map tc_flatten (P t))))
  tc tc'
  (Hoverlay : simple_overlaytc P tc tc')
  (Hnodup_forest : NoDup (map tc_roottid (flat_map tc_flatten (flat_map P (map tc_roottid (tc_flatten tc))))))
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc)))
  (* a neat choice to write None or neg here ... *)
  (Hdomexcl : forall t, tc_getnode t tc -> 
    forall t', ~ find (has_same_tid t) (flat_map tc_flatten (P t'))) :
  List.NoDup (map tc_roottid (tc_flatten tc')).
Proof.
  eapply Permutation.Permutation_NoDup.
  1:{
    symmetry.
    unfold tc_roottid.
    rewrite <- map_map.
    apply Permutation.Permutation_map.
    eapply simple_overlaytc_dom_info.
    apply Hoverlay.
  }
  rewrite -> map_app.
  rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
  split; [ | split ].
  - now rewrite -> map_map.
  - repeat setoid_rewrite -> base.elem_of_list_In.
    rewrite -> ! map_map.
    fold tc_roottid.
    setoid_rewrite -> map_flat_map_In.
    setoid_rewrite -> in_flat_map.
    intros t Hin (ch & (u & Hin' & Hin_ch) & Hin_sub').
    rewrite -> tc_getnode_subtc_iff in Hin.
    pose proof (map_flat_map_In_conv _ _ _ _ _ Hin_ch Hin_sub').
    rewrite -> tc_getnode_in_iff in H.
    apply (Hdomexcl _ Hin _ H).
  - now rewrite -> map_map.
Qed.

Lemma tc_shape_inv_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat)
  (Hcomple : forall t, exists aclk, tc_shape_inv (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hshape : tc_shape_inv tc)
  (* needed for aclk upperbound *)
  (Hclk_lt : Foralltc (fun tc' => Q (tc_roottid tc') <= tc_rootclk tc') tc)
  (* needed for aclk sorted *)
  (Haclk_lt : Foralltc (fun tc' => let: Node ni chn := tc' in
    Forall (fun tc' => Q (info_tid ni) <= tc_rootaclk tc') chn) tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  Foralltc tc_chn_aclk_ub tc' /\ Foralltc tc_chn_aclk_decsorted tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
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
  pose proof (tc_shape_inv_chn _ _ Hshape) as Hshape_chn.
  rewrite -> tc_shape_inv_conj_iff, -> ! Foralltc_cons_iff in Hshape_sub, Hshape.
  rewrite -> Foralltc_cons_iff in Haclk_lt, Hclk_lt.
  destruct Hshape_sub as (_ & (Ha & Ha') & (Hb & Hb')), 
    Hshape as (_ & (Ha'' & _) & (Hb'' & _)), 
    Haclk_lt as (Eaclk_lt & Haclk_lt), Hclk_lt as (Eclk_lt & Hclk_lt).
  simpl in Ha, Hb, Eaclk_lt, Eclk_lt, Ha'', Hb''.

  rewrite -> List.Forall_forall in Hshape_chn, Hclk_lt, Haclk_lt.

  (* TODO repetition elimination *)
  split.
  all: rewrite -> Foralltc_cons_iff, -> List.Forall_app.
  - split; [ | split ].
    + simpl.
      apply List.Forall_app.
      split.
      * unfold tc_rootaclk.
        change (fun tc' => _) with (fun tc' => (fun ni => info_aclk ni <= clk) (tc_rootinfo tc')) in Ha'' |- *.
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
    + simpl.
      unfold tc_rootaclk.
      rewrite <- map_map, -> map_app, <- Hinfosame, <- map_app, -> map_map.
      fold tc_rootaclk.
      rewrite -> map_app.
      apply StronglySorted_app.
      * assumption.
      * assumption.
      * change (fun tc' => _) with (fun tc' => (fun a => a <= clk) (tc_rootaclk tc')) in Ha''.
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
  (Hdmono_sub : forall t, exists aclk, Foralltc (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hge : tc_ge tc_larger tc)
  (* needed for using dmono on (P t) *)
  (Hclk_le : Foralltc (fun tc' => Q (tc_roottid tc') <= tc_rootclk tc') tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  tc_ge tc_larger tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
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
  rewrite -> Foralltc_cons_iff in Hclk_le, Hdmono_sub, Hge |- *.
  destruct Hge as (Ege & Hge), Hclk_le as (Eclk_le & Hclk_le), 
    Hdmono_sub as (Hdmono_sub & _).
  rewrite -> List.Forall_forall in Hge, Hclk_le.
  simpl in Eclk_le, Hdmono_sub.
  removehead Hdmono_sub.
  2: lia.
  split; auto.
  apply List.Forall_app.
  split.
  2: now apply Foralltc_cons_iff in Hdmono_sub.
  rewrite -> List.Forall_forall.
  intros new_ch Hin_newch.
  pose proof (Hcorr_inr _ Hin_newch) as (ch & Hin_ch & Hso).
  specialize (IH _ Hin_ch (Hge _ Hin_ch) (Hclk_le _ Hin_ch) _ Hso).
  now apply IH.
Qed.

Corollary dmono_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hdmono_sub : forall t, exists aclk, Foralltc (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Hdmono : Foralltc (dmono_single tc_larger) tc)
  (* needed for using dmono on (P t) *)
  (Hclk_le : Foralltc (fun tc' => Q (tc_roottid tc') <= tc_rootclk tc') tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  Foralltc (dmono_single tc_larger) tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
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
    apply Foralltc_self in Hdmono.
    intuition.
  - apply List.Forall_app.
    split.
    + rewrite -> Foralltc_cons_iff in Hdmono, Hclk_le.
      destruct Hdmono as (_ & Hdmono_chn), Hclk_le as (_ & Hclk_le).
      rewrite -> List.Forall_forall in Hdmono_chn, Hclk_le |- *.
      firstorder.
    + specialize (Hdmono_sub u).
      destruct Hdmono_sub as (aclk' & Hdmono_sub).
      now apply Foralltc_cons_iff in Hdmono_sub.
Qed.

Lemma imono_simple_overlaytc_pre (P : thread -> list treeclock) (Q : thread -> nat) tc_larger
  (Hdmono_sub : forall t, exists aclk, Foralltc (dmono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  (Himono_sub : forall t, exists aclk, Foralltc (imono_single tc_larger) (Node (mkInfo t (Q t) aclk) (P t)))
  tc (Himono : Foralltc (imono_single tc_larger) tc)
  (Hclk_le : Foralltc (fun tc' => Q (tc_roottid tc') <= tc_rootclk tc') tc)
  : forall tc' (Hoverlay : simple_overlaytc P tc tc'),
  Foralltc (imono_single tc_larger) tc'.
Proof.
  induction tc as [(u, clk, aclk) chn IH] using treeclock_ind_2; intros.
  destruct tc' as [(u', clk', aclk') chn'].
  apply simple_overlaytc_inv in Hoverlay.
  simpl in Hoverlay.
  destruct Hoverlay as (new_chn & ? & Htmp & -> & -> & Hcorr & Hinfosame).
  injection Htmp as <-.
  subst clk' aclk'.
  rewrite -> List.Forall_forall in IH.
  pose proof (Forall2_forall_exists_r _ _ _ Hcorr) as Hcorr_inr.
  pose proof (Himono_sub u) as (aclk' & Himono_sub').
  rewrite -> Foralltc_cons_iff in Himono, Hclk_le, Himono_sub' |- *.
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
  (Hclk_le : Foralltc (fun tc' => Q (tc_roottid tc') <= tc_rootclk tc') tc)
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

(* now, put everything together *)
(* TODO revise the following two proofs *)

Lemma tc_attach_nodes_tc_shape_inv tc tc' 
  (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc') 
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc')
  (Hrespect : tc_respect tc' tc) :
  tc_shape_inv (tc_attach_nodes 
    (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc)) 
    (tc_get_updated_nodes_join tc tc')).
Proof.
  pose proof (tc_attach_nodes_result 
    (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))
    (tc_get_updated_nodes_join tc tc')) as Hso.
  remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
  destruct (tc_detach_nodes (tc_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
  simpl in Hso |- *.
  pose proof Hso as Hnodup.
  pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
  rewrite <- Eprefix in Hprefix.
  pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix Hshape') as Hshape_pf.
  assert (forest = snd (tc_detach_nodes (tc_flatten prefix_tc') tc)) as Eforest by now rewrite -> Edetach.

  (* first, get nodup *)
  eapply simple_overlaytc_nodup in Hnodup.
  2:{
    intros t.
    destruct (find (has_same_tid t) forest) as [ res | ] eqn:E.
    2: simpl; constructor.
    apply find_some in E.
    destruct E as (E & _).
    pose proof (tc_shape_inv_tc_detach_nodes_snd (tc_flatten prefix_tc') tc Hshape) as H.
    rewrite -> Edetach, -> List.Forall_forall in H.
    specialize (H _ E).
    destruct res.
    now apply tid_nodup, NoDup_cons_iff in H.
  }
  2:{
    pose proof (tc_detach_nodes_tid_nodup (tc_flatten prefix_tc') tc (tid_nodup _ Hshape)) as Hnodup_forest.
    pose proof (tc_detach_nodes_forest_recombine _ _ (tid_nodup _ Hshape) (tid_nodup _ Hshape_pf)) as Hperm.
    rewrite <- Eforest in Hperm.
    eapply Permutation.Permutation_NoDup.
    1: apply Permutation.Permutation_map, Permutation.Permutation_flat_map, Hperm.
    apply tid_nodup_root_chn_split.
    rewrite -> Eforest.
    now apply tc_detach_nodes_tid_nodup, tid_nodup.
  }
  2:{
    apply tid_nodup in Hshape'.
    pose proof (tid_nodup_prefix_preserve _ _ (tc_get_updated_nodes_join_is_prefix tc tc') Hshape').
    congruence.
  }
  2:{
    intros t H t' Hres.
    destruct (find (has_same_tid t') forest) as [ [ni chn] | ] eqn:E.
    2: auto.
    simpl in Hres.
    (* cannot find in children *)
    apply find_some in E.
    destruct E as (Hin & E).
    rewrite -> has_same_tid_true in E.
    subst forest.
    (* pose proof Hin as Hsnd. *)
    pose proof (tc_detach_nodes_snd2fst (tc_flatten prefix_tc') tc) as Hsnd2fst.
    rewrite -> List.Forall_forall in Hsnd2fst.
    apply Hsnd2fst in Hin.
    destruct Hin as (sub & Hin & Hsnd).
    rewrite <- tc_getnode_in_iff, -> in_map_iff in Hres.
    destruct Hres as (sub' & <- & Hin').
    pose proof (tc_detach_nodes_dom_excl _ sub _ H sub') as Htmp.
    rewrite <- Hsnd in Htmp.
    simpl in Htmp.
    specialize (Htmp (or_intror Hin') eq_refl).
    subst sub'.
    now apply self_not_in_tc_flatten_chn in Hin'.
  }

  (* next, get all the others *)
  pose proof Hso as Hother.
  eapply tc_shape_inv_simple_overlaytc_pre with (Q:=fun t => tc_getclk t tc) in Hother.
  2:{
    intros t.
    destruct (find (has_same_tid t) forest) as [ [(t', clk, aclk) chn] | ] eqn:E.
    2:{
      exists 0.
      constructor.
      all: simpl.
      2-3: rewrite -> Foralltc_cons_iff.
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
    pose proof (tc_detach_nodes_snd_is_subprefix (tc_flatten prefix_tc') tc) as Hsnd2pf.
    pose proof (tc_shape_inv_tc_detach_nodes_snd (tc_flatten prefix_tc') tc Hshape) as Hshape_forest.
    rewrite <- Eforest, -> List.Forall_forall in Hsnd2pf, Hshape_forest.
    specialize (Hsnd2pf _ Hin).
    specialize (Hshape_forest _ Hin).
    destruct Hsnd2pf as (sub & Hin_sub & E).
    pose proof (prefixtc_rootinfo_same _ _ E) as Einfo.
    pose proof (tid_nodup_find_self_sub _ (tid_nodup _ Hshape) _ Hin_sub) as Hres.
    apply option.fmap_Some in Hres.
    destruct Hres as (res & Hres & Einfo').
    unfold tc_roottid in Hres.
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
    eapply Foralltc_impl.
    2: apply (proj1 H).
    simpl.
    lia.
  }
  2:{
    pose proof (tc_get_updated_nodes_join_shape _ Hshape' _ Hrespect Hroot_clk_le).
    subst prefix_tc'.
    eapply Foralltc_impl.
    2: apply (proj2 H).
    intros [? ?].
    apply List.Forall_impl.
    lia.
  }

  now apply tc_shape_inv_conj_iff.
Qed.

Lemma tc_attach_nodes_respect tc tc' 
  (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc') 
  (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc')
  (Hrespect : tc_respect tc' tc) tc_larger 
    (Hrespect1 : tc_respect tc tc_larger)
    (Hrespect2 : tc_respect tc' tc_larger) :
  tc_respect (tc_attach_nodes 
    (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc)) 
    (tc_get_updated_nodes_join tc tc')) tc_larger.
Proof.
  pose proof (tc_attach_nodes_result 
    (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))
    (tc_get_updated_nodes_join tc tc')) as Hso.
  remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
  destruct (tc_detach_nodes (tc_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
  simpl in Hso |- *.
  pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
  assert (forest = snd (tc_detach_nodes (tc_flatten prefix_tc') tc)) as Eforest by now rewrite -> Edetach.
  rewrite <- Eprefix in Hprefix.
  revert Hso.
  apply tc_respect_simple_overlaytc_pre with (Q:=fun t => tc_getclk t tc).
  - intros t.
    destruct (find (has_same_tid t) forest) as [ [(t', clk, aclk) chn] | ] eqn:E.
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
    pose proof (tc_detach_nodes_snd_is_subprefix (tc_flatten prefix_tc') tc) as Hsnd2pf.
    pose proof (tc_shape_inv_tc_detach_nodes_snd (tc_flatten prefix_tc') tc Hshape) as Hshape_forest.
    rewrite <- Eforest, -> List.Forall_forall in Hsnd2pf, Hshape_forest.
    specialize (Hsnd2pf _ Hin).
    specialize (Hshape_forest _ Hin).
    destruct Hsnd2pf as (sub & Hin_sub & E).
    pose proof (prefixtc_rootinfo_same _ _ E) as Einfo.
    pose proof (tid_nodup_find_self_sub _ (tid_nodup _ Hshape) _ Hin_sub) as Hres.
    apply option.fmap_Some in Hres.
    destruct Hres as (res & Hres & Einfo').
    unfold tc_roottid in Hres.
    rewrite <- Einfo in Hres.
    simpl in Hres.
    assert (tc_getclk t tc = clk) as <-.
    {
      unfold tc_getclk, tc_rootclk.
      now rewrite -> Hres, <- Einfo', <- Einfo.
    }
    exists aclk.
    pose proof (tc_respect_sub _ _ Hrespect1) as Hrespect_sub.
    rewrite -> Foralltc_Forall_subtree, -> List.Forall_forall in Hrespect_sub.
    specialize (Hrespect_sub _ Hin_sub).
    eapply tc_respect_prefix_preserve; eauto.
  - eapply tc_respect_prefix_preserve; eauto.
  - pose proof (tc_get_updated_nodes_join_shape _ Hshape' _ Hrespect Hroot_clk_le).
    subst prefix_tc'.
    eapply Foralltc_impl.
    2: apply (proj1 H).
    simpl.
    lia.
Qed.

(* should also be "tcs_congr", but keep the word "forest" anyway *)
Lemma tc_attach_nodes_forest_congr forest1 forest2 tc
  (H : Foralltc (fun tc' => List.find (has_same_tid (tc_roottid tc')) forest1 = 
    List.find (has_same_tid (tc_roottid tc')) forest2) tc) :
  tc_attach_nodes forest1 tc = tc_attach_nodes forest2 tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  rewrite Foralltc_cons_iff in H.
  simpl in H |- *.
  destruct H as (Hroot & H).
  eapply Forall_impl_impl in H.
  2: apply IH.
  erewrite -> map_ext_Forall.
  2: apply H.
  now rewrite Hroot.
Qed.

(* FIXME: why so long? *)

Lemma tc_detach_attach_distr1_fst tc forest nd 
  (Hnotin : ~ In (tc_roottid nd) (map tc_roottid (tc_flatten tc))) :
  fst (tc_detach_nodes (nd :: nil) (tc_attach_nodes forest tc)) =
  tc_attach_nodes (map fst (map (tc_detach_nodes (nd :: nil)) forest)) tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  remember (match find (has_same_tid (info_tid ni)) forest with Some u => tc_rootchn u | None => nil end) as old_chn eqn:Eold_chn.
  remember (map (tc_attach_nodes forest) chn) as app_chn eqn:Eapp_chn.
  rewrite map_app, split_app.
  destruct (List.split (map (tc_detach_nodes (nd :: nil)) app_chn)) as (new_chn1, res1) eqn:Esplit1, 
    (List.split (map (tc_detach_nodes (nd :: nil)) old_chn)) as (new_chn2, res2) eqn:Esplit2, 
    (partition (fun tc' : treeclock => isSome (if has_same_tid (tc_roottid tc') nd then Some nd else None)) (new_chn1 ++ new_chn2))
    as (res', new_chn') eqn:Epar.
  (* bad isSome *)
  rewrite -> partition_ext_Forall with (g:=fun tc' => has_same_tid (tc_roottid tc') nd) in Epar.
  2: apply Forall_forall; intros x ?; now destruct (has_same_tid (tc_roottid x) nd).
  simpl.
  f_equal.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit1, Esplit2.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit1, Esplit2, Epar.
  destruct Epar as (Eres' & Enew_chn'), Esplit1 as (Enew_chn1 & Eres1), 
    Esplit2 as (Enew_chn2 & Eres2).
  simpl in Hnotin.
  apply Forall_impl_impl with (P:=fun tc => ~ In (tc_roottid nd) (map tc_roottid (tc_flatten tc))) in IH.
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
    unfold tc_roottid at 1.
    rewrite (prefixtc_rootinfo_same _ _ (tc_detach_nodes_fst_is_prefix _ _)).
    destruct ch; simpl; auto.
  - (* ? *)
    clear -forest.
    induction forest as [ | tc' forest IH ]; simpl; auto.
    erewrite -> tc_rootinfo_has_same_tid_congr with (x:=(fst (tc_detach_nodes (nd :: nil) tc'))).
    2: apply tc_detach_nodes_fst_rootinfo_same.
    destruct (has_same_tid (info_tid ni) tc') eqn:E.
    + destruct tc' as [ ni' chn' ].
      simpl.
      (* TODO ... *)
      destruct (List.split (map (tc_detach_nodes (nd :: nil)) chn'))
        as (new_chn, forest') eqn:Esplit, 
        (partition (fun tc' : treeclock => isSome (if has_same_tid (tc_roottid tc') nd then Some nd else None)) new_chn)
        as (res', new_chn') eqn:Epar.
      simpl.
      (* bad isSome *)
      rewrite -> partition_ext_Forall with (g:=fun tc' => has_same_tid (tc_roottid tc') nd) in Epar.
      2: apply Forall_forall; intros x ?; now destruct (has_same_tid (tc_roottid x) nd).
      rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
      rewrite -> partition_filter in Epar.
      apply pair_equal_split in Esplit, Epar.
      destruct Esplit as (Enew_chn & Eres), Epar as (Eres' & Enew_chn').
      now subst.
    + apply IH.
Qed.

Lemma tc_detach_attach_distr1_snd tc forest nd 
  (Hnotin : ~ In (tc_roottid nd) (map tc_roottid (tc_flatten tc))) :
  Permutation.Permutation
  (snd (tc_detach_nodes (nd :: nil) (tc_attach_nodes forest tc)))
  (flat_map snd (map (fun tc' => tc_detach_nodes (nd :: nil) 
    (match find (has_same_tid (tc_roottid tc')) forest with 
      | Some u => u | None => Node (tc_rootinfo tc') nil end)) (tc_flatten tc))).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
  simpl.
  remember (match find (has_same_tid (info_tid ni)) forest with Some u => tc_rootchn u | None => nil end) as old_chn eqn:Eold_chn.
  remember (map (tc_attach_nodes forest) chn) as app_chn eqn:Eapp_chn.
  rewrite map_app, split_app.
  destruct (List.split (map (tc_detach_nodes (nd :: nil)) app_chn)) as (new_chn1, res1) eqn:Esplit1, 
    (List.split (map (tc_detach_nodes (nd :: nil)) old_chn)) as (new_chn2, res2) eqn:Esplit2, 
    (partition (fun tc' : treeclock => isSome (if has_same_tid (tc_roottid tc') nd then Some nd else None)) (new_chn1 ++ new_chn2))
    as (res', new_chn') eqn:Epar.
  (* bad isSome *)
  rewrite -> partition_ext_Forall with (g:=fun tc' => has_same_tid (tc_roottid tc') nd) in Epar.
  2: apply Forall_forall; intros x ?; now destruct (has_same_tid (tc_roottid x) nd).
  simpl.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit1, Esplit2.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit1, Esplit2, Epar.
  destruct Epar as (Eres' & Enew_chn'), Esplit1 as (Enew_chn1 & Eres1), 
    Esplit2 as (Enew_chn2 & Eres2).
  simpl in Hnotin.
  apply Forall_impl_impl with (P:=fun tc => ~ In (tc_roottid nd) (map tc_roottid (tc_flatten tc))) in IH.
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
  1: apply Permutation.Permutation_app; [ apply Permutation.Permutation_app; 
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
  match goal with |- Permutation.Permutation (_ ++ ?al ++ _) _ => 
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
  etransitivity; [ | apply Permutation.Permutation_app_comm ].
  apply Permutation.Permutation_app_head.

  destruct (find (has_same_tid (info_tid ni)) forest) as [ [ ni' chn' ] | ] eqn:E.
  2: now simpl.
  clear -chn'.
  cbn delta [tc_rootchn] beta iota.
  (* TODO this is a simple equation for the result of tc_detach_nodes only? *)
  simpl.
  destruct (List.split (map (tc_detach_nodes (nd :: nil)) chn')) as (new_chn, res) eqn:Esplit,  
    (partition (fun tc' : treeclock => isSome (if has_same_tid (tc_roottid tc') nd then Some nd else None)) new_chn)
    as (res', new_chn') eqn:Epar.
  (* bad isSome *)
  rewrite -> partition_ext_Forall with (g:=fun tc' => has_same_tid (tc_roottid tc') nd) in Epar.
  2: apply Forall_forall; intros x ?; now destruct (has_same_tid (tc_roottid x) nd).
  simpl.
  rewrite -> split_map_fst_snd, -> ! map_map in Esplit.
  rewrite -> partition_filter in Epar.
  apply pair_equal_split in Esplit, Epar.
  destruct Epar as (Eres' & Enew_chn'), Esplit as (Enew_chn & Eres).
  now subst.
Qed.

Section TC_Join.

  Variables (tc tc' : treeclock).
  Hypotheses (Hshape : tc_shape_inv tc) (Hshape' : tc_shape_inv tc') 
    (Hrespect : tc_respect tc' tc).

  Lemma tc_join_dom_info
    (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') :
    Permutation.Permutation (map tc_rootinfo (tc_flatten (tc_join tc tc')))
      (map tc_rootinfo (tc_flatten (fst (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))) ++
      map tc_rootinfo (tc_flatten (let: Node (mkInfo t clk _) chn := tc_attach_nodes 
        (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc)) 
        (tc_get_updated_nodes_join tc tc') in Node (mkInfo t clk (tc_rootclk tc)) chn))).
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    simpl in Hroot_clk_le.
    unfold tc_join.
    cbn delta [tc_rootinfo] beta iota.
    destruct (clk_u' <=? tc_getclk u' tc) eqn:Eclk_lt.
    1: apply Nat.leb_le in Eclk_lt; lia.
    rewrite <- ! Etc'.
    remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
    destruct (tc_detach_nodes (tc_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
    destruct (tc_attach_nodes forest prefix_tc') as [ni chn_w] eqn:Eattach.
    assert (ni = mkInfo u' clk_u' aclk_u') as ->.
    {
      (* TODO extract the two rootinfoeq out? *)
      pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as E.
      apply prefixtc_rootinfo_same in E.
      rewrite <- Eprefix in E.
      destruct prefix_tc' as [ni' ?].
      simpl in Eattach.
      injection Eattach as ->.
      subst tc'.
      now simpl in E.
    }
    destruct pivot as [ni_z chn_z] eqn:Epivot.
    assert (ni_z = tc_rootinfo tc) as ->.
    {
      destruct tc as [ni' ?].
      simpl in Edetach |- *.
      destruct (List.split (map (tc_detach_nodes (tc_flatten prefix_tc')) chn)) as (new_chn, ?),
        (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) (tc_flatten prefix_tc')) new_chn).
      congruence.
    }
    simpl.
    constructor.
    rewrite -> Eattach.
    simpl.
    rewrite -> map_app.
    etransitivity.
    2: apply Permutation.Permutation_middle.
    constructor.
    now apply Permutation.Permutation_app_comm.
  Qed.

  (* TODO there may be some repetition below ... *)

  Lemma tc_join_dom_partial_info
    (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') :
    Permutation.Permutation (map tc_rootinfo_partial (tc_flatten (tc_join tc tc')))
      (map tc_rootinfo_partial (tc_flatten (fst (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))) ++
      map tc_rootinfo_partial (tc_flatten (tc_get_updated_nodes_join tc tc')) ++
      map tc_rootinfo_partial (flat_map tc_flatten (flat_map tc_rootchn
              (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))))).
  Proof.
    pose proof (tc_join_dom_info Hroot_clk_le) as Hperm.
    pose (f:=fun ni => let: mkInfo u clk _ := ni in (u, clk)).
    apply Permutation.Permutation_map with (f:=f) in Hperm.
    rewrite <- map_app, -> ! map_map in Hperm.
    rewrite -> ! map_ext with (f:=fun x => f (tc_rootinfo x)) (g:=tc_rootinfo_partial) in Hperm.
    2-3: now destruct a as [(?, ?, ?) ?].
    etransitivity.
    1: apply Hperm.
    rewrite -> map_app.
    apply Permutation.Permutation_app_head.

    pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
    pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix Hshape') as Hshape_pf.
    pose proof (tc_attach_nodes_dom_info _ _ (tid_nodup _ Hshape) (tid_nodup _ Hshape_pf)) as Hperm'.
    apply Permutation.Permutation_map with (f:=f) in Hperm'.
    rewrite <- map_app, -> ! map_map in Hperm'.
    rewrite -> ! map_ext with (f:=fun x => f (tc_rootinfo x)) (g:=tc_rootinfo_partial) in Hperm'.
    2-3: now destruct a as [(?, ?, ?) ?].
    rewrite -> map_app in Hperm, Hperm'.
    destruct (tc_attach_nodes
      (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))
      (tc_get_updated_nodes_join tc tc')) as [(?, ?, ?) ?].
    etransitivity.
    1: apply Hperm'; auto.
    reflexivity.
  Qed.

  Corollary tc_join_dom_tid 
    (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') :
    Permutation.Permutation (map tc_roottid (tc_flatten (tc_join tc tc')))
      (map tc_roottid (tc_flatten (fst (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))) ++
      map tc_roottid (tc_flatten (tc_attach_nodes 
        (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc)) 
        (tc_get_updated_nodes_join tc tc')))).
  Proof.
    pose proof (tc_join_dom_info Hroot_clk_le) as Hperm.
    apply Permutation.Permutation_map with (f:=info_tid) in Hperm.
    rewrite <- map_app, -> ! map_map in Hperm.
    fold tc_roottid in Hperm.
    etransitivity.
    1: apply Hperm.
    rewrite -> map_app.
    apply Permutation.Permutation_app_head.
    destruct (tc_attach_nodes
      (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))
      (tc_get_updated_nodes_join tc tc')) as [(?, ?, ?) ?].
    now simpl.
  Qed.

  Corollary tc_join_dom_tid'
    (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') :
    Permutation.Permutation (map tc_roottid (tc_flatten (tc_join tc tc')))
      (map tc_roottid (tc_flatten (fst (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))) ++
      map tc_roottid (tc_flatten (tc_get_updated_nodes_join tc tc')) ++
      map tc_roottid (flat_map tc_flatten (flat_map tc_rootchn
              (snd (tc_detach_nodes (tc_flatten (tc_get_updated_nodes_join tc tc')) tc))))).
  Proof.
    pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
    pose proof (tc_shape_inv_prefix_preserve _ _ Hprefix Hshape') as Hshape_pf.
    pose proof (tc_attach_nodes_dom_info _ _ (tid_nodup _ Hshape) (tid_nodup _ Hshape_pf)) as Hperm.
    apply Permutation.Permutation_map with (f:=info_tid) in Hperm.
    rewrite <- map_app, -> ! map_map in Hperm.
    fold tc_roottid in Hperm.
    rewrite -> map_app in Hperm.
    etransitivity.
    1: apply tc_join_dom_tid; auto.
    now apply Permutation.Permutation_app_head.
  Qed.

  Corollary tc_join_dom_incl_operand
    (Hroot_clk_le : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') :
    incl (map tc_roottid (tc_flatten tc)) (map tc_roottid (tc_flatten (tc_join tc tc'))).
  Proof.
    intros t Hin.
    eapply Permutation.Permutation_in.
    1: symmetry; apply tc_join_dom_tid'; auto.
    rewrite -> ! in_app_iff.
    (* use tc detach dom *)
    pose proof (tc_detach_nodes_dom_partition (tc_flatten (tc_get_updated_nodes_join tc tc')) tc) as Hperm.
    eapply Permutation.Permutation_map with (f:=info_tid) in Hperm.
    rewrite -> ! map_map in Hperm.
    fold tc_roottid in Hperm.
    eapply Permutation.Permutation_in in Hin.
    2: apply Hperm.
    clear Hperm.
    rewrite -> map_app, -> in_app_iff in Hin.
    destruct Hin as [ Hin | Hin ].
    1: intuition.
    right.
    rewrite -> map_flat_map_In in Hin.
    destruct Hin as ([ni_sub chn_sub] & Hin_sub & Hin).
    simpl in Hin.
    destruct Hin as [ <- | Hin ].
    - left.
      (* use dom incl *)
      pose proof (tc_detach_nodes_dom_incl (tc_flatten (tc_get_updated_nodes_join tc tc')) tc) as Hdomincl.
      rewrite -> List.Forall_forall in Hdomincl.
      apply Hdomincl in Hin_sub.
      simpl in Hin_sub.
      now rewrite -> tc_getnode_subtc_iff.
    - right.
      rewrite -> map_flat_map_In in Hin.
      destruct Hin as (ch_sub & Hin_ch & Hin).
      eapply map_flat_map_In_conv.
      2: apply Hin.
      rewrite -> in_flat_map.
      now exists (Node ni_sub chn_sub).
  Qed.

  (* this is fundamental! the root of tc will not be updated *)
  Hypothesis (Hroot_clk_le : tc_getclk (tc_roottid tc) tc' <= tc_rootclk tc).

  Lemma tc_join_tc_shape_inv :
    tc_shape_inv (tc_join tc tc').
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    unfold tc_join.
    cbn delta [tc_rootinfo] beta iota.
    destruct (clk_u' <=? tc_getclk u' tc) eqn:Eclk_lt.
    1: assumption.
    apply Nat.leb_gt in Eclk_lt.
    rewrite <- ! Etc'.
    remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
    destruct (tc_detach_nodes (tc_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
    destruct (tc_attach_nodes forest prefix_tc') as [ni chn_w] eqn:Eattach.
    assert (ni = mkInfo u' clk_u' aclk_u') as ->.
    {
      (* TODO extract the two rootinfoeq out? *)
      pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as E.
      apply prefixtc_rootinfo_same in E.
      rewrite <- Eprefix in E.
      destruct prefix_tc' as [ni' ?].
      simpl in Eattach.
      injection Eattach as ->.
      subst tc'.
      now simpl in E.
    }
    destruct pivot as [ni_z chn_z] eqn:Epivot.
    assert (ni_z = tc_rootinfo tc) as Eni_z.
    {
      destruct tc as [ni' ?].
      simpl in Edetach |- *.
      destruct (List.split (map (tc_detach_nodes (tc_flatten prefix_tc')) chn)) as (new_chn, ?),
        (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) (tc_flatten prefix_tc')) new_chn).
      congruence.
    }

    (* use prepend child *)
    apply tc_shape_inv_prepend_child.
    - pose proof (tc_shape_inv_tc_detach_nodes_fst (tc_flatten prefix_tc') tc Hshape) as H.
      now rewrite -> Edetach in H.
    - apply tc_shape_inv_root_aclk_useless with (aclk:=aclk_u').
      pose proof (tc_attach_nodes_tc_shape_inv _ _ Hshape Hshape' Eclk_lt Hrespect) as H.
      subst.
      rewrite -> Edetach in H.
      cbn delta [snd] beta iota in H.
      now rewrite -> Eattach in H.
    - (* a long proof! *)
      pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as Hprefix.
      rewrite <- Eprefix in Hprefix.
      rewrite <- Etc' in Hshape', Hrespect.
      pose proof (tid_nodup_prefix_preserve _ _ Hprefix (tid_nodup _ Hshape')) as Hnodup_prefix.
      pose proof (tc_attach_nodes_dom_info _ _ (tid_nodup _ Hshape) Hnodup_prefix) as Hperm_attach.
      rewrite -> Edetach in Hperm_attach.
      simpl in Hperm_attach.
      rewrite -> Eattach in Hperm_attach.
      intros t Hin Hin'.
      rewrite <- tc_getnode_subtc_iff in Hin, Hin'.
      (* local trans *)
      assert (In t (map tc_roottid (tc_flatten (Node (mkInfo u' clk_u' (info_clk ni_z)) chn_w))) <->
        In t (map tc_roottid (tc_flatten (Node (mkInfo u' clk_u' aclk_u') chn_w)))) as Htmp by now simpl.
      rewrite -> Htmp in Hin.
      clear Htmp.
      pose proof Hin as Hin_backup.
      pose proof Hin' as Hin'_backup.
      unfold tc_roottid in Hin, Hin'.
      rewrite <- map_map, -> in_map_iff in Hin, Hin'.
      destruct Hin as (ni_t & Eni_t & Hin), Hin' as (ni_t' & Eni_t' & Hin').
      eapply Permutation.Permutation_in in Hin.
      2: apply Hperm_attach.
      rewrite <- map_app in Hin.
      apply in_map with (f:=info_tid) in Hin.
      rewrite -> map_map in Hin.
      fold tc_roottid in Hin.
      rewrite -> Eni_t in Hin.
      rewrite -> map_app, -> in_app_iff in Hin.
      destruct Hin as [ Hin | Hin ].
      + (* fst of detach and prefix_tc' have no intersection *)
        rewrite -> tc_getnode_subtc_iff in Hin.
        pose proof (tc_detach_nodes_dom_excl _ tc _ Hin) as Hdomexcl.
        rewrite -> in_map_iff in Hin'_backup.
        destruct Hin'_backup as (sub & Et & Hin'_backup).
        rewrite -> Edetach in Hdomexcl.
        cbn delta [fst] beta iota in Hdomexcl.
        specialize (Hdomexcl _ Hin'_backup Et).
        subst sub.
        simpl in Et.
        subst ni_z.
        fold (tc_roottid tc) in Et.
        (* use Hroot_clk_le *)
        subst prefix_tc'.
        apply tc_get_updated_nodes_join_sound in Hin; try assumption.
        * rewrite <- Et in Hin.
          unfold tc_getclk in Hin at 1.
          rewrite -> tc_getnode_self in Hin.
          subst tc'. 
          lia.
        * now subst tc'.
      + (* fst, snd of detach have no intersection *)
        pose proof (tc_detach_nodes_tid_nodup (tc_flatten prefix_tc') tc (tid_nodup _ Hshape)) as Hnodup_forest.
        rewrite -> Edetach in Hnodup_forest.
        cbn delta [fst snd] beta iota in Hnodup_forest.
        apply proj2, proj1 in Hnodup_forest.
        eapply Hnodup_forest.
        1: apply Hin'_backup.
        apply map_flat_map_In in Hin.
        setoid_rewrite -> in_flat_map in Hin.
        destruct Hin as (sub' & (sub & Hin_sub & Hin_sub') & Hin).
        eapply map_flat_map_In_conv.
        1: apply Hin_sub.
        destruct sub as [ni_sub chn_sub].
        simpl.
        right.
        eapply map_flat_map_In_conv; eauto.
    - now simpl.
    - simpl.
      pose proof (tc_shape_inv_tc_detach_nodes_fst (tc_flatten prefix_tc') tc Hshape) as H.
      apply aclk_upperbound, Foralltc_self in H.
      rewrite -> Edetach in H.
      simpl in H.
      destruct ni_z as (?, clk_z, ?).
      rewrite -> List.Forall_forall in H.
      destruct chn_z as [ | ch ? ]; simpl.
      1: lia.
      now specialize (H _ (or_introl eq_refl)).
  Qed.

  Lemma tc_join_pointwise_max_pre
    (Hroot_clk_lt : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') t :
    tc_getclk t (tc_join tc tc') = Nat.max (tc_getclk t tc) (tc_getclk t tc').
  Proof.
    unfold tc_getclk at 1.
    destruct (tc_getnode t (tc_join tc tc')) as [ res | ] eqn:E.
    - apply find_some in E.
      rewrite -> has_same_tid_true in E.
      destruct E as (Hres & Et).
      pose proof tc_join_tc_shape_inv as Hnodup_join.
      apply tid_nodup in Hnodup_join.
      eapply Permutation.Permutation_NoDup in Hnodup_join.
      2:{
        etransitivity.
        1: now apply tc_join_dom_tid'.
        etransitivity.
        1: apply Permutation.Permutation_app_swap_app.
        apply Permutation.Permutation_app_swap.
      }
      pose proof Hres as Hin.
      apply in_map with (f:=tc_rootinfo_partial) in Hin.
      eapply Permutation.Permutation_in in Hin.
      2:{
        etransitivity.
        1: now apply tc_join_dom_partial_info.
        apply Permutation.Permutation_app_swap_app.
      }
      rewrite -> in_app_iff in Hin.
      (* TODO a lot of repetition below *)
      destruct Hin as [ Hin | Hin ].
      + pose proof Hin as Hin'.
        apply in_map with (f:=fst) in Hin'.
        rewrite -> map_map, -> map_ext with (g:=tc_roottid) in Hin'.
        2: now destruct a as [(?, ?, ?) ?].
        replace (fst (tc_rootinfo_partial res)) with t in Hin'.
        2: destruct res as [(?, ?, ?) ?]; simpl in *; congruence.
        rewrite -> tc_getnode_subtc_iff, <- tc_get_updated_nodes_join_adequacy in Hin'; auto.
        (* le is enough here *)
        apply Nat.lt_le_incl in Hin'.
        rewrite -> max_r.
        2: assumption.

        (* result comes from tc' *)
        rewrite -> in_map_iff in Hin.
        destruct Hin as (sub & Einfop & Hin).
        (* pose proof Hin as Hin_backup. *)
        apply in_map with (f:=tc_rootinfo) in Hin.

        eapply prefixtc_flatten_info_incl in Hin.
        2: apply tc_get_updated_nodes_join_is_prefix.
        rewrite -> in_map_iff in Hin.
        destruct Hin as (sub' & Einfo & Hin).
        pose proof (tid_nodup_find_self _ (tid_nodup _ Hshape')) as Hself.
        rewrite -> List.Forall_forall in Hself.
        apply Hself in Hin.
        unfold tc_getclk, tc_getnode.
        rewrite -> (tc_rootinfo_tid_inj _ _ Einfo) in Hin.
        destruct res as [(t', clk, ?) ?], sub as [(t'', clk', ?) ?].
        simpl in Einfop, Et, Hin |- *.
        injection Einfop as ->.
        subst.
        now rewrite -> Hin, -> (tc_rootinfo_clk_inj _ _ Einfo).
      + rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hnodup_join.
        repeat setoid_rewrite -> base.elem_of_list_In in Hnodup_join.
        destruct Hnodup_join as (_ & Hnodup_join & _).

        pose proof Hin as Hin'.
        apply in_map with (f:=fst) in Hin'.
        rewrite <- map_app, -> map_map, -> map_ext with (g:=tc_roottid) in Hin'.
        2: now destruct a as [(?, ?, ?) ?].
        replace (fst (tc_rootinfo_partial res)) with t in Hin'.
        2: destruct res as [(?, ?, ?) ?]; simpl in *; congruence.
        rewrite -> map_app in Hin'.

        specialize (Hnodup_join _ Hin').
        rewrite -> tc_getnode_subtc_iff, <- tc_get_updated_nodes_join_adequacy, -> Nat.nlt_ge in Hnodup_join; auto.
        rewrite -> max_l.
        2: assumption.

        (* result comes from tc *)
        rewrite <- map_app, -> in_map_iff in Hin.
        destruct Hin as (sub & Einfop & Hin).
        (* pose proof Hin as Hin_backup. *)
        apply in_map with (f:=tc_rootinfo) in Hin.
        rewrite -> map_app in Hin.

        pose proof (tc_detach_nodes_dom_partition_subset _ _ _ Hin) as Hin_tc.
        rewrite -> in_map_iff in Hin_tc.
        destruct Hin_tc as (sub' & Einfo & Hin_tc).
        pose proof (tid_nodup_find_self _ (tid_nodup _ Hshape)) as Hself.
        rewrite -> List.Forall_forall in Hself.
        apply Hself in Hin_tc.
        unfold tc_getclk, tc_getnode.
        rewrite -> (tc_rootinfo_tid_inj _ _ Einfo) in Hin_tc.
        destruct res as [(t', clk, ?) ?], sub as [(t'', clk', ?) ?].
        simpl in Einfop, Et, Hin_tc |- *.
        injection Einfop as ->.
        subst.
        now rewrite -> Hin_tc, -> (tc_rootinfo_clk_inj _ _ Einfo).
    - (* not in the join result, then both must be 0 *)
      match type of E with ?a = _ => assert (~ a) as Hnotin by now rewrite -> E end.
      rewrite <- tc_getnode_subtc_iff in Hnotin.
      destruct (in_dec eqdec t (map tc_roottid (tc_flatten (tc_get_updated_nodes_join tc tc')))) as [ Hin' | Hnotin' ].
      + exfalso.
        apply Hnotin.
        eapply Permutation.Permutation_in.
        1: symmetry; apply tc_join_dom_tid'; auto.
        rewrite -> ! in_app_iff.
        intuition.
      + rewrite -> tc_getnode_subtc_iff, <- tc_get_updated_nodes_join_adequacy in Hnotin'; auto.
        destruct (in_dec eqdec t (map tc_roottid (tc_flatten tc))) as [ Hin'' | Hnotin'' ].
        * now apply tc_join_dom_incl_operand in Hin''.
        * rewrite -> tc_getnode_subtc_iff in Hnotin''.
          assert (tc_getclk t tc = 0) as Eclk.
          {
            unfold tc_getclk.
            destruct (tc_getnode t tc).
            - now unfold isSome, is_true in Hnotin''.
            - reflexivity.
          }
          rewrite -> Eclk in Hnotin' |- *.
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
      apply dmono, Foralltc_self in Hrespect.
      simpl in Hrespect.
      subst tc'.
      intuition.
    - apply Nat.leb_gt in Eclk_lt.
      rewrite <- Etc' in *.
      replace clk_u' with (tc_rootclk tc') in Eclk_lt by now rewrite -> Etc'.
      replace u' with (tc_roottid tc') in Eclk_lt by now rewrite -> Etc'.
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
    (Hroot_clk_lt' : tc_getclk (tc_roottid tc) tc'' < tc_rootclk tc) :
    tc_respect (tc_join tc tc') tc''.
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    unfold tc_join.
    cbn delta [tc_rootinfo] beta iota.
    destruct (clk_u' <=? tc_getclk u' tc) eqn:Eclk_lt.
    1: assumption.
    apply Nat.leb_gt in Eclk_lt.
    rewrite <- ! Etc'.
    remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
    destruct (tc_detach_nodes (tc_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
    destruct (tc_attach_nodes forest prefix_tc') as [ni chn_w] eqn:Eattach.
    assert (ni = mkInfo u' clk_u' aclk_u') as ->.
    {
      (* TODO extract the two rootinfoeq out? *)
      pose proof (tc_get_updated_nodes_join_is_prefix tc tc') as E.
      apply prefixtc_rootinfo_same in E.
      rewrite <- Eprefix in E.
      destruct prefix_tc' as [ni' ?].
      simpl in Eattach.
      injection Eattach as ->.
      subst tc'.
      now simpl in E.
    }
    destruct pivot as [ni_z chn_z] eqn:Epivot.
    assert (ni_z = tc_rootinfo tc) as Eni_z.
    {
      destruct tc as [ni' ?].
      simpl in Edetach |- *.
      destruct (List.split (map (tc_detach_nodes (tc_flatten prefix_tc')) chn)) as (new_chn, ?),
        (partition (fun tc' : treeclock => find (has_same_tid (tc_roottid tc')) (tc_flatten prefix_tc')) new_chn).
      congruence.
    }
    (* prepare *)
    pose proof (tc_detach_nodes_fst_is_prefix (tc_flatten prefix_tc') tc) as Hprefix_pivot.
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
        subst ni_z.
        destruct tc as [(?, ?, ?) ?].
        simpl in Hroot_clk_lt' |- *.
        lia.
      + constructor.
        * (* the difference of aclk is troublesome ... *)
          apply dmono in Hrespect_attach.
          rewrite -> Foralltc_cons_iff in Hrespect_attach |- *.
          split; [ | intuition ].
          apply proj1 in Hrespect_attach.
          simpl in Hrespect_attach |- *.
          unfold tc_ge in Hrespect_attach |- *.
          now rewrite -> Foralltc_cons_iff in Hrespect_attach |- *.
        * eapply List.Forall_impl.
          2: apply tc_respect_chn in Hrespect_pivot; apply Hrespect_pivot.
          simpl.
          intros.
          now apply dmono.
    - constructor.
      + unfold imono_single.
        subst ni_z.
        destruct tc as [(z, clk_z, aclk_z) chn_z'].
        simpl.
        constructor.
        * (* impossible by assumption *)
          simpl in Hroot_clk_lt'.
          lia.
        * now apply imono, Foralltc_cons_iff, proj1 in Hrespect_pivot.
      + constructor.
        * (* the difference of aclk is troublesome ... *)
          apply imono in Hrespect_attach.
          rewrite -> Foralltc_cons_iff in Hrespect_attach |- *.
          split; intuition.
        * eapply List.Forall_impl.
          2: apply tc_respect_chn in Hrespect_pivot; apply Hrespect_pivot.
          simpl.
          intros.
          now apply imono.
  Qed.

End TC_Join.

Definition tc_join_partial tc subtree_tc' :=
  let: (pivot, forest) := tc_detach_nodes (tc_flatten subtree_tc') tc in
  let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
  let: Node info_z chn_z := pivot in 
  Node info_z ((Node (mkInfo w clk_w (info_clk info_z)) chn_w) :: chn_z).

(* TODO tc_join tc tc' = tc_join tc (prefix); this may not be useful enough, though *)



End TreeClock.
