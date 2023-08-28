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

(* FIXME: redefine it in the same way below? *)
Definition tc_rootinfo_partial tc :=
  let: Node (mkInfo u clk _) _ := tc in (u, clk).

Definition info_partial ni := (info_tid ni, info_clk ni).

Definition tc_rootchn tc :=
  let: Node _ chn := tc in chn.

Definition tc_roottid tc := info_tid (tc_rootinfo tc).

Definition tc_rootclk tc := info_clk (tc_rootinfo tc).

Definition tc_rootaclk tc := info_aclk (tc_rootinfo tc).

Global Arguments tc_roottid !_ /.
Global Arguments tc_rootclk !_ /.
Global Arguments tc_rootaclk !_ /.

Fact tc_rootinfo_partial_info_partial tc : info_partial (tc_rootinfo tc) = tc_rootinfo_partial tc.
Proof. now destruct tc as [(?, ?, ?) ?]. Qed.

Fact tc_rootinfo_tid_inj : forall x y, tc_rootinfo x = tc_rootinfo y -> tc_roottid x = tc_roottid y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

Fact tc_rootinfo_clk_inj : forall x y, tc_rootinfo x = tc_rootinfo y -> tc_rootclk x = tc_rootclk y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

Fact tc_partialinfo_tid_inj : forall x y, tc_rootinfo_partial x = tc_rootinfo_partial y -> tc_roottid x = tc_roottid y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

Fact tc_partialinfo_clk_inj : forall x y, tc_rootinfo_partial x = tc_rootinfo_partial y -> tc_rootclk x = tc_rootclk y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

Fact tc_rootinfo_aclk_inj : forall x y, tc_rootinfo x = tc_rootinfo y -> tc_rootaclk x = tc_rootaclk y.
Proof. intros [(?, ?, ?) ?] [(?, ?, ?) ?]. simpl. congruence. Qed.

Fact map_map_rootinfo2partialinfo tcs :
  map tc_rootinfo_partial tcs = map info_partial (map tc_rootinfo tcs).
Proof.
  rewrite -> map_ext with (f:=tc_rootinfo_partial) (g:=fun tc => info_partial (tc_rootinfo tc)) in |- *.
  2: intros; now rewrite tc_rootinfo_partial_info_partial.
  rewrite <- map_map with (f:=tc_rootinfo) (g:=info_partial).
  reflexivity.
Qed.

Fact Permutation_rootinfo2partialinfo tcs1 tcs2 
  (H : Permutation.Permutation (map tc_rootinfo tcs1) (map tc_rootinfo tcs2)) :
  Permutation.Permutation (map tc_rootinfo_partial tcs1) (map tc_rootinfo_partial tcs2).
Proof.
  rewrite -> ! map_map_rootinfo2partialinfo.
  now apply Permutation.Permutation_map.
Qed.

Fact Permutation_partialinfo2roottid tcs1 tcs2 
  (H : Permutation.Permutation (map tc_rootinfo_partial tcs1) (map tc_rootinfo_partial tcs2)) :
  Permutation.Permutation (map tc_roottid tcs1) (map tc_roottid tcs2).
Proof.
  rewrite -> ! map_ext with (f:=tc_roottid) (g:=fun tc => fst (tc_rootinfo_partial tc)) in |- *.
  2-3: now intros [(?, ?, ?) ?].
  rewrite <- 2 map_map with (f:=tc_rootinfo_partial) (g:=fst).
  now apply Permutation.Permutation_map.
Qed.

Fact Permutation_rootinfo2roottid tcs1 tcs2 
  (H : Permutation.Permutation (map tc_rootinfo tcs1) (map tc_rootinfo tcs2)) :
  Permutation.Permutation (map tc_roottid tcs1) (map tc_roottid tcs2).
Proof. now apply Permutation_partialinfo2roottid, Permutation_rootinfo2partialinfo. Qed.
(*
(* FIXME:??? *)
Fact NoDup_rootinfo_partialinfo tcs : 
  NoDup (map tc_rootinfo tcs) <-> NoDup (map tc_rootinfo_partial tcs).
Proof.
  erewrite -> map_ext with (f:=tc_rootinfo_partial).
  2: intros; symmetry; now apply tc_rootinfo_partial_info_partial.
  rewrite <- map_map with (g:=info_partial).
  split; intros H.
  - 


  - now apply NoDup_map_inv in H.
*)
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

Fact tc_flatten_direct_result tc : tc_flatten tc = tc :: (flat_map tc_flatten (tc_rootchn tc)).
Proof. now destruct tc as [? ?]. Qed.

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

Corollary subtc_flatten_incl tc tc' (H : subtc tc tc') : incl (tc_flatten tc) (tc_flatten tc').
Proof. hnf. intros sub' H'. revert H' H. apply subtc_trans. Qed.

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

Fact tc_locate_pos_app pos1 : forall tc pos2 sub (H : tc_locate tc pos1 = Some sub),
  tc_locate tc (pos1 ++ pos2) = tc_locate sub pos2.
Proof.
  induction pos1 as [ | x pos1 IH ]; intros; simpl in *.
  - injection H as <-.
    reflexivity.
  - destruct tc as [ni chn].
    simpl in *.
    destruct (nth_error chn x) eqn:E; try discriminate.
    now apply IH.
Qed.

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

Definition tc_size tc := length (tc_flatten tc).

Global Arguments tc_size ! _ /.

Fact tc_size_chn_lt_full tc : length (tc_rootchn tc) < tc_size tc.
Proof.
  destruct tc; simpl.
  erewrite -> Permutation.Permutation_length with (l:=(flat_map tc_flatten chn)).
  2: apply tc_flatten_root_chn_split.
  rewrite app_length.
  lia.
Qed.

Fact tc_size_ch_lt_full ch tc (H : In ch (tc_rootchn tc)) : 
  tc_size ch < tc_size tc.
Proof.
  destruct tc; simpl in H |- *.
  pose proof (in_split _ _ H) as (pre & suf & ->).
  rewrite -> flat_map_app.
  simpl.
  erewrite -> Permutation.Permutation_length.
  2: apply Permutation.Permutation_app_swap_app.
  rewrite ! app_length.
  unfold tc_size. 
  lia.
Qed.

Fact tc_size_subtc_le_full tc : forall sub (H : subtc sub tc), 
  tc_size sub <= tc_size tc.
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros; simpl in H |- *.
  destruct H as [ <- | (ch & Hin_ch & H)%in_flat_map ]; simpl.
  1: apply le_n.
  transitivity (tc_size ch).
  2: pose proof (tc_size_ch_lt_full ch (Node ni chn) Hin_ch) as Htmp; simpl in Htmp; lia.
  rewrite Forall_forall in IH.
  now specialize (IH _ Hin_ch _ H).
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

Corollary tid_nodup_find_self_sub [A : Type] (f : treeclock -> A) tc (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc))) 
  sub (Hin_sub : In sub (tc_flatten tc)) :
  base.fmap f (tc_getnode (tc_roottid sub) tc) = Some (f sub).
Proof.
  pose proof (tid_nodup_find_self (tc_flatten tc) Hnodup) as H.
  rewrite -> List.Forall_forall in H.
  specialize (H _ Hin_sub).
  unfold tc_getnode.
  now rewrite -> H.
Qed.

Corollary tc_getclk_perm_congr_pre tcs1 tcs2 (Hnodup1 : List.NoDup (map tc_roottid tcs1))
  (Hperm : Permutation.Permutation (map tc_rootinfo_partial tcs1) (map tc_rootinfo_partial tcs2)) :
  forall t, base.fmap tc_rootclk (find (has_same_tid t) tcs1) = base.fmap tc_rootclk (find (has_same_tid t) tcs2).
Proof.
  (* TODO revise this or not? *)
  pose proof Hnodup1 as Hnodup1'.
  rewrite -> map_ext with (g:=fun x => fst (tc_rootinfo_partial x)) in Hnodup1'.
  2: now intros [(?, ?, ?) ?].
  rewrite <- map_map in Hnodup1'.
  apply NoDup_map_inv in Hnodup1'.
  pose proof Hnodup1' as Hnodup2'.
  eapply Permutation.Permutation_NoDup in Hnodup2'.
  2: apply Hperm.
  pose proof Hperm as Hperm'%Permutation_partialinfo2roottid.
  pose proof Hnodup1 as Hnodup2.
  eapply Permutation.Permutation_NoDup in Hnodup2.
  2: apply Hperm'.

  intros t.
  pose proof (Permutation_in_mutual _ _ Hperm' t) as Hin.
  rewrite -> ! tc_getnode_in_iff in Hin.
  (* unfold tc_getclk. *)
  destruct (find (has_same_tid t) tcs1) as [ res1 | ] eqn:Eres1.
  - destruct (find (has_same_tid t) tcs2) as [ res2 | ] eqn:Eres2.
    2: simpl in Hin; unfold is_true in Hin; eqsolve.
    (* use NoDup_map_inj *)
    apply find_some in Eres1, Eres2.
    rewrite -> has_same_tid_true in Eres1, Eres2.
    destruct Eres1 as (Hsub1%(in_map tc_rootinfo_partial) & E1), 
      Eres2 as (Hsub2%(in_map tc_rootinfo_partial) & E2).
    eapply Permutation.Permutation_in in Hsub1.
    2: apply Hperm.
    rewrite -> map_ext with (g:=(fun x : treeclock => fst (tc_rootinfo_partial x))) (f:=tc_roottid) in Hnodup2.
    2: now intros [(?, ?, ?) ?].
    rewrite <- map_map in Hnodup2.
    eapply NoDup_map_inj in Hnodup2.
    3: apply Hsub1.
    3: apply Hsub2.
    all: destruct res1 as [(?, ?, ?) ?], res2 as [(?, ?, ?) ?]; simpl in *; congruence.
  - destruct (find (has_same_tid t) tcs2) as [ res2 | ] eqn:Eres2.
    + simpl in Hin; unfold is_true in Hin; eqsolve.
    + reflexivity.
Qed.

Fact tc_getclk_viewchange t tc : tc_getclk t tc = 
  match base.fmap tc_rootclk (tc_getnode t tc) with Some res => res | None => 0 end.
Proof. unfold tc_getclk. now destruct (tc_getnode t tc). Qed.

(* return a tree instead of a stack? *)
(* compute prefix(tc') that should be updated in tc; assume that 
    at least the root of tc' must be updated in tc
*)
(* considering the simulation with imperative code, maybe this process 
    should not be too declarative. therefore takes a recursion on list
    as a sub-procedure
*)

Fixpoint tc_get_updated_nodes_join tc tc' : treeclock :=
  (* making this clk parameterized, instead of being some thread will be good for verification *)
  let fix tc_get_updated_nodes_join_aux tc clk chn_u' : list treeclock :=
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

(* TODO this is awkward. the inner aux must be an external function to work with
    since implementing it as a mutual recursion does not pass the arg decrease check *)

Fixpoint tc_get_updated_nodes_join_aux tc clk chn_u' : list treeclock :=
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

Lemma tc_get_updated_nodes_join_eta tc tc' : 
  tc_get_updated_nodes_join tc tc' = 
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (tc_getclk (info_tid info_u') tc) chn_u').
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

(* if the subtree_tc' is not a complete one then this is a "partial" result *)

Definition tc_join_partial tc subtree_tc' :=
  let: (pivot, forest) := tc_detach_nodes (tc_flatten subtree_tc') tc in
  let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
  let: Node info_z chn_z := pivot in 
  Node info_z ((Node (mkInfo w clk_w (info_clk info_z)) chn_w) :: chn_z).

Definition tc_join tc tc' := Eval unfold tc_join_partial in
  let: mkInfo z' clk_z' aclk_z' := tc_rootinfo tc' in
  if clk_z' <=? (tc_getclk z' tc)
  then tc
  else tc_join_partial tc (tc_get_updated_nodes_join tc tc').
    (*
    let: subtree_tc' := tc_get_updated_nodes_join tc tc' in
    let: (pivot, forest) := tc_detach_nodes (tc_flatten subtree_tc') tc in
    let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
    let: Node info_z chn_z := pivot in 
    Node info_z ((Node (mkInfo w clk_w (info_clk info_z)) chn_w) :: chn_z).
    *)

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

Corollary tid_nodup_subtc [sub tc] (H : subtc sub tc) 
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc))) :
  List.NoDup (map tc_roottid (tc_flatten sub)).
Proof. rewrite -> tid_nodup_Foralltc_id in Hnodup; eapply Foralltc_subtc in H; [ | apply Hnodup ]; auto. Qed. 

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
  (* (Hnointersect : forall t, tc_getnode t tc_new -> tc_getnode t (Node ni chn) -> False) *)
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten (Node ni (tc_new :: chn)))))
  (Haclk_bounded : tc_rootaclk tc_new <= info_clk ni)
  (Haclk_ge : tc_rootaclk tc_new >= match chn with ch :: _ => tc_rootaclk ch | nil => 0 end) :
  tc_shape_inv (Node ni (tc_new :: chn)).
Proof.
  constructor.
  - assumption.
    (*
    repeat setoid_rewrite <- tc_getnode_subtc_iff in Hnointersect.
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
    *)
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

Fact tc_get_updated_nodes_join_aux_app tc clk chn1 chn2 
  (H : Forall (fun tc' => clk < tc_rootaclk tc' \/ (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc') chn1) :
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
  (Hcong : Forall (fun sub => tc_getclk (tc_roottid sub) tc = tc_getclk (tc_roottid sub) tc') chn) :
  map tc_rootinfo (tc_get_updated_nodes_join_aux tc clk chn) = 
  map tc_rootinfo (tc_get_updated_nodes_join_aux tc' clk chn).
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
    tc_rootclk tc' <= (tc_getclk (tc_roottid tc') tc)) 
  (Hsorted: StronglySorted ge (map tc_rootaclk chn_u')) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc clk chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => In tc' chn_u'' <-> 
      ((tc_getclk (tc_roottid tc') tc) < tc_rootclk tc' /\
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

Corollary tc_get_updated_nodes_join_is_prefix tc tc' :
  prefixtc (tc_get_updated_nodes_join tc tc') tc'.
Proof.
  induction tc' as [(u', clk_u', aclk_u') chn' IH] using treeclock_ind_2; intros.
  tc_get_updated_nodes_join_unfold.
  simpl.
  pose proof (tc_get_updated_nodes_join_aux_result_submap tc (tc_getclk u' tc) chn')
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

(* subsumption? *)
Lemma tc_get_updated_nodes_join_aux_result_regular tc u' clk_u' aclk_u' chn_u' 
  (Hshape_tc' : tc_shape_inv (Node (mkInfo u' clk_u' aclk_u') chn_u')) 
  (Hrespect : tc_respect (Node (mkInfo u' clk_u' aclk_u') chn_u') tc) :
  exists chn_u'', list.sublist chn_u'' chn_u' /\
    (tc_get_updated_nodes_join_aux tc (tc_getclk u' tc) chn_u') = map (tc_get_updated_nodes_join tc) chn_u'' /\
    (Forall (fun tc' => ~ In tc' chn_u'' <-> tc_ge tc tc') chn_u') /\
    (Forall (fun tc' => In tc' chn_u'' <-> (tc_getclk (tc_roottid tc') tc) < tc_rootclk tc') chn_u') /\
    (Forall (fun tc' => (tc_getclk u' tc) < tc_rootaclk tc') chn_u'').
Proof.
  pose proof (tc_get_updated_nodes_join_aux_result tc (tc_getclk u' tc) chn_u') as H.
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
  (* FIXME: perm solver *)
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

Corollary tc_detach_nodes_dom_partition' tcs tc :
  Permutation.Permutation (map tc_rootinfo (tc_flatten tc))
    (map tc_rootinfo (tc_flatten (fst (tc_detach_nodes tcs tc))) ++ 
      map tc_rootinfo (snd (tc_detach_nodes tcs tc)) ++ 
      map tc_rootinfo (flat_map tc_flatten (flat_map tc_rootchn (snd (tc_detach_nodes tcs tc))))).
Proof.
  etransitivity; [ apply tc_detach_nodes_dom_partition with (tcs:=tcs) | ].
  rewrite -> map_app.
  apply Permutation.Permutation_app_head. 
  rewrite <- map_app.
  now apply Permutation.Permutation_map, tc_flatten_root_chn_split.
Qed.

Corollary tc_detach_nodes_tid_nodup tcs tc 
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  NoDup (map tc_roottid (flat_map tc_flatten (snd (tc_detach_nodes tcs tc)))) /\
  (forall t, 
    In t (map tc_roottid (tc_flatten (fst (tc_detach_nodes tcs tc)))) ->
    In t (map tc_roottid (flat_map tc_flatten (snd (tc_detach_nodes tcs tc)))) -> False) /\
  NoDup (map tc_roottid (tc_flatten (fst (tc_detach_nodes tcs tc)))).
Proof.
  pose proof (tc_detach_nodes_dom_partition tcs tc) as Hperm%Permutation_rootinfo2roottid.
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

(* FIXME: use this alternative version to replace/optimize the original version? *)
Corollary tc_detach_nodes_dom_excl' tcs tc t (Htarg : find (has_same_tid t) tcs) :
  ~ In t (map tc_roottid (flat_map tc_flatten (tc_rootchn (fst (tc_detach_nodes tcs tc))))).
Proof.
  destruct (fst (tc_detach_nodes tcs tc)) as [ni chn] eqn:E.
  simpl.
  intros (ch & Hin_ch & (res & Eid & H)%in_map_iff)%map_flat_map_In.
  apply tc_detach_nodes_dom_excl with (res:=res) (tc:=tc) in Htarg; try assumption.
  2: rewrite E; apply subtc_trans with (tc':=ch); [ assumption | apply subtc_chn; now simpl ].
  (* contradiction *)
  apply self_not_in_tc_flatten_chn with (ni:=ni) (chn:=chn), in_flat_map.
  rewrite Htarg, E in H.
  eauto.
Qed.

Corollary tc_detach_nodes_dom_excl'' tcs tc t (Htarg : find (has_same_tid t) tcs) :
  ~ In t (map tc_roottid (flat_map tc_flatten (flat_map tc_rootchn (snd (tc_detach_nodes tcs tc))))).
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
  (Hnotin : find (has_same_tid (tc_roottid tc)) tcs = None) :
  forall ni,
    In ni (map tc_rootinfo (filter (fun sub => find (has_same_tid (tc_roottid sub)) tcs) (tc_flatten tc))) <-> 
    In ni (map tc_rootinfo (snd (tc_detach_nodes tcs tc))).
Proof.
  intros.
  pose proof (tc_detach_nodes_dom_partition' tcs tc) as Hperm.
  rewrite <- ! map_app in Hperm.
  (* ... have to use map_filter_comm *)
  pose proof (map_filter_comm tc_rootinfo (fun ni => find (has_same_tid (info_tid ni)) tcs) (tc_flatten tc)) as Htmp.
  simpl in Htmp.
  unfold tc_roottid.
  rewrite <- Htmp, -> filter_In.
  clear Htmp.
  erewrite -> Permutation_in_mutual at 1; [ | apply Hperm ].
  rewrite -> ! map_app, -> ! in_app_iff.
  split; intros H.
  - destruct H as (H & Htarg).
    (* TODO why this Hlocal? *)
    assert (forall ni0 tcs0, ~ In (info_tid ni0) (map tc_roottid tcs0) -> ~ In ni0 (map tc_rootinfo tcs0)) as Hlocal.
    {
      intros.
      intros (sub & <- & Hq)%in_map_iff.
      apply in_map with (f:=tc_roottid) in Hq.
      unfold tc_roottid in Hq at 1.
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
      unfold tc_roottid in Hnotin.
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

Corollary tc_detach_nodes_dom_partition'' tcs tc (Hnotin : find (has_same_tid (tc_roottid tc)) tcs = None) 
  (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc))) :
  Permutation.Permutation
    (map tc_rootinfo (tc_flatten (fst (tc_detach_nodes tcs tc))) ++
     map tc_rootinfo (flat_map tc_flatten (flat_map tc_rootchn
            (snd (tc_detach_nodes tcs tc)))))
    (map tc_rootinfo (filter (fun sub => 
      negb (find (has_same_tid (tc_roottid sub)) tcs)) (tc_flatten tc))) /\
  Permutation.Permutation
    (map tc_rootinfo (snd (tc_detach_nodes tcs tc)))
    (map tc_rootinfo (filter (fun sub => find (has_same_tid (tc_roottid sub)) tcs) (tc_flatten tc))).
Proof.
  apply base.and_wlog_l.
  - intros Hperm'.
    eapply Permutation.Permutation_app_inv_l.
    etransitivity.
    2: rewrite <- map_app; apply Permutation.Permutation_map, Permutation_split_combine.
    etransitivity.
    2: symmetry; apply tc_detach_nodes_dom_partition' with (tcs:=tcs).
    etransitivity.
    2: apply Permutation.Permutation_app_swap_app.
    now apply Permutation.Permutation_app_tail.
  - unfold tc_roottid in Hnodup.
    rewrite <- map_map with (f:=tc_rootinfo) in Hnodup.
    apply NoDup_map_inv in Hnodup.
    apply Permutation.NoDup_Permutation.
    + eapply Permutation.Permutation_NoDup in Hnodup.
      2: apply tc_detach_nodes_dom_partition' with (tcs:=tcs).
      rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hnodup.
      destruct Hnodup as (_ & _ & Hnodup).
      now rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup in Hnodup.
    + (* ... have to use map_filter_comm *)
      pose proof (map_filter_comm tc_rootinfo (fun ni => find (has_same_tid (info_tid ni)) tcs) (tc_flatten tc)) as Htmp.
      simpl in Htmp.
      unfold tc_roottid.
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
(*
Fact simple_overlaytc_rootinfo_same (P : thread -> list treeclock) tc tc'
  (Hoverlay : simple_overlaytc P tc tc') : tc_rootinfo tc' = tc_rootinfo tc.
Proof. destruct tc, tc', (simple_overlaytc_inv _ _ _ _ _ Hoverlay) as (? & ? & ?). simpl. intuition. Qed.
*)
Fact tc_attach_nodes_rootinfo_same forest tc : 
  tc_rootinfo (tc_attach_nodes forest tc) = tc_rootinfo tc.
Proof. now destruct tc. Qed.

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
  (* these two conditions are required the trees of the forest appear at most once in the result *)
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

(* TODO this is not needed for our current purpose. for now, just keep it *)
(*
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
*)

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

Lemma tc_attach_detached_nodes_tid_nodup tc tc'
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) (Hnodup' : NoDup (map tc_roottid (tc_flatten tc'))) :
  NoDup (map tc_roottid (tc_flatten (tc_attach_nodes (snd (tc_detach_nodes (tc_flatten tc') tc)) tc'))).
Proof.
  (* TODO still needs some preparation when using tc_attach_nodes_dom_info *)
  pose proof (tc_attach_nodes_dom_info _ _ Hnodup Hnodup') as Hperm.
  rewrite <- map_app in Hperm.
  apply Permutation_rootinfo2roottid in Hperm.
  eapply Permutation.Permutation_NoDup. 
  1: symmetry; apply Hperm. 
  rewrite -> map_app.
  rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
  repeat setoid_rewrite -> base.elem_of_list_In.
  split; [ assumption | split ].
  2: apply tid_nodup_root_chn_split, tc_detach_nodes_tid_nodup; assumption.
  (* use domain exclusion *)
  (* FIXME: extract this out? *)
  intros t H (ch & (sub & Hpick & Hin_ch)%in_flat_map & Hin_sub)%map_flat_map_In.
  pose proof (tc_detach_nodes_snd2fst (tc_flatten tc') tc) as Htmp.
  rewrite -> List.Forall_forall in Htmp.
  specialize (Htmp _ Hpick).
  destruct Htmp as (sub' & Hin_sub' & ->).
  eapply tc_detach_nodes_dom_excl'; [ apply tc_getnode_in_iff, H | ].
  eapply map_flat_map_In_conv; eauto.
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
    pose proof (tid_nodup_find_self_sub tc_rootinfo _ (tid_nodup _ Hshape) _ Hin_sub) as Hres.
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

  apply tc_shape_inv_conj_iff.
  split; [ | assumption ].
  subst forest.
  apply tc_attach_detached_nodes_tid_nodup. 
  all: now apply tid_nodup.
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
    (* FIXME: revise? *)
    pose proof (tc_detach_nodes_snd_is_subprefix (tc_flatten prefix_tc') tc) as Hsnd2pf.
    pose proof (tc_shape_inv_tc_detach_nodes_snd (tc_flatten prefix_tc') tc Hshape) as Hshape_forest.
    rewrite <- Eforest, -> List.Forall_forall in Hsnd2pf, Hshape_forest.
    specialize (Hsnd2pf _ Hin).
    specialize (Hshape_forest _ Hin).
    destruct Hsnd2pf as (sub & Hin_sub & E).
    pose proof (prefixtc_rootinfo_same _ _ E) as Einfo.
    pose proof (tid_nodup_find_self_sub tc_rootinfo _ (tid_nodup _ Hshape) _ Hin_sub) as Hres.
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

Corollary tc_attach_nodes_forest_cleanhd forest1 sub tc
  (Hnotin : ~ In (tc_roottid sub) (map tc_roottid (tc_flatten tc))) :
  tc_attach_nodes forest1 tc = tc_attach_nodes (sub :: forest1) tc.
Proof.
  apply tc_attach_nodes_forest_congr, Foralltc_Forall_subtree, Forall_forall.
  intros sub' Hin.
  simpl.
  destruct (has_same_tid (tc_roottid sub') sub) eqn:E; try reflexivity.
  rewrite -> has_same_tid_true in E.
  apply in_map with (f:=tc_roottid) in Hin.
  congruence.
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
      | Some u => u | None => Node (mkInfo (tc_roottid tc') 0%nat 0%nat) nil end)) (tc_flatten tc))).
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

(* TODO can we prove this from the beginning? this seems to be the only thing we want. *)
(* FIXME: something must be repeating here. what is it? *)
Corollary tc_detach_attach_distr1_snd' tc forest nd 
  (Hnotin : ~ In (tc_roottid nd) (map tc_roottid (tc_flatten tc))) 
  (Hdomincl : Forall (fun tc' => In (tc_roottid tc') (map tc_roottid (tc_flatten tc))) forest)
  (Hnodup_forest : NoDup (map tc_roottid forest))
  (Hnodup : NoDup (map tc_roottid (tc_flatten tc))) :
  Permutation.Permutation
    (snd (tc_detach_nodes (nd :: nil) (tc_attach_nodes forest tc)))
    (flat_map snd (map (tc_detach_nodes (nd :: nil)) forest)).
Proof.
  rewrite tc_detach_attach_distr1_snd; try assumption.
  match goal with |- _ (flat_map snd (map ?ff _)) _ =>
    rewrite -> map_ext_Forall with (l:=forest) (f:=(tc_detach_nodes (nd :: nil))) (g:=ff) end.
  2:{
    pose proof (tid_nodup_find_self _ Hnodup_forest) as Htmp.
    rewrite -> Forall_forall in Htmp |- *.
    intros x Hin.
    specialize (Htmp _ Hin).
    now rewrite Htmp.
  }
  etransitivity.
  1: apply Permutation.Permutation_flat_map, Permutation.Permutation_map, 
    Permutation_split_combine with (f:=fun tc' => find (has_same_tid (tc_roottid tc')) forest).
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
  pose proof (map_map tc_roottid (fun t => tc_detach_nodes (nd :: nil)
    match find (has_same_tid t) forest with Some u => u | None => Node (mkInfo t 0%nat 0%nat) nil end)) as Htmp.
  simpl in Htmp.
  rewrite <- ! Htmp.
  clear Htmp.
  apply Permutation.Permutation_flat_map, Permutation.Permutation_map.
  (* ... have to use map_filter_comm *)
  pose proof (map_filter_comm tc_roottid (fun t => (find (has_same_tid t) forest)) (tc_flatten tc)) as Htmp.
  simpl in Htmp.
  rewrite <- ! Htmp.
  clear Htmp.
  (* ... *)
  apply Permutation.NoDup_Permutation; try assumption.
  1: now apply NoDup_filter.
  intros t.
  rewrite filter_In.
  rewrite -> Forall_forall in Hdomincl.
  split.
  - match goal with |- context[find ?a ?b] => destruct (find a b) as [ res | ] eqn:Eres end.
    2: intros (? & ?); discriminate.
    intros (Hin & _).
    apply tc_getnode_in_iff.
    now rewrite Eres.
  - intros Hin.
    split.
    + rewrite -> in_map_iff in Hin.
      destruct Hin as (sub & <- & Hin).
      now apply Hdomincl.
    + now rewrite -> tc_getnode_in_iff in Hin.
Qed.

(* purely computational *)

Fact tc_join_trivial tc tc' (H : tc_rootclk tc' <= tc_getclk (tc_roottid tc') tc) :
  tc_join tc tc' = tc.
Proof.
  unfold tc_join.
  destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
  simpl in H |- *.
  apply Nat.leb_le in H.
  now rewrite H.
Qed.

Fact tc_join_roottid_same_trivial tc tc' (H : tc_roottid tc = tc_roottid tc') 
  (Hroot_clk_le : tc_getclk (tc_roottid tc) tc' <= tc_rootclk tc) :
  tc_join tc tc' = tc.
Proof.
  apply tc_join_trivial.
  destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
  simpl in H, Hroot_clk_le |- *; subst z.
  unfold tc_getclk, tc_getnode in Hroot_clk_le |- *. 
  simpl in Hroot_clk_le |- *.
  now destruct (eqdec z' z').
Qed.

Fact tc_join_go tc tc' 
  (H : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') :
  tc_join tc tc' = tc_join_partial tc (tc_get_updated_nodes_join tc tc').
Proof.
  unfold tc_join, tc_join_partial.
  destruct tc' as [(z', clk_z', ?) ?], tc as [(z, clk_z, ?) ?]. 
  simpl in H.
  apply Nat.leb_gt in H.
  cbn delta [tc_rootinfo] zeta iota beta.
  now rewrite H.
Qed.

Fact tc_join_partial_rootinfo_same tc subtree_tc' :
  tc_rootinfo (tc_join_partial tc subtree_tc') = tc_rootinfo tc.
Proof.
  unfold tc_join_partial.
  destruct (tc_detach_nodes _ _) as (pivot, forest) eqn:Edetach.
  destruct subtree_tc' as [(?, ?, ?) ?] eqn:E, pivot as [(?, ?, ?) ?] eqn:Epivot.
  simpl in *. 
  rewrite <- tc_detach_nodes_fst_rootinfo_same with (tcs:=tc_flatten (subtree_tc')).
  subst.
  simpl.
  now rewrite -> Edetach.
Qed.

Section TC_Join_Partial.

  Variables (tc tc' : treeclock).

  (* a direct result *)
  Lemma tc_join_partial_dom_info :
    Permutation.Permutation (map tc_rootinfo (tc_flatten (tc_join_partial tc tc')))
      (map tc_rootinfo (tc_flatten (fst (tc_detach_nodes (tc_flatten tc') tc))) ++
        map tc_rootinfo (tc_flatten 
          (let: Node (mkInfo t clk _) chn := tc_attach_nodes 
            (snd (tc_detach_nodes (tc_flatten tc') tc)) tc' 
          in Node (mkInfo t clk (tc_rootclk tc)) chn))).
  Proof.
    destruct tc' as [(u', clk_u', aclk_u') chn'] eqn:Etc'.
    unfold tc_join_partial.
    rewrite <- ! Etc'.
    destruct (tc_detach_nodes (tc_flatten tc') tc) as (pivot, forest) eqn:Edetach.
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
    2: apply Permutation.Permutation_middle.
    constructor.
    now apply Permutation.Permutation_app_comm.
  Qed.

  Corollary tc_join_partial_dom_tid :
    Permutation.Permutation (map tc_roottid (tc_flatten (tc_join_partial tc tc')))
      (map tc_roottid (tc_flatten (fst (tc_detach_nodes (tc_flatten tc') tc))) ++
        map tc_roottid (tc_flatten (tc_attach_nodes 
          (snd (tc_detach_nodes (tc_flatten tc') tc)) tc'))).
  Proof.
    pose proof tc_join_partial_dom_info as Hperm.
    rewrite <- map_app in Hperm.
    apply Permutation_rootinfo2roottid in Hperm.
    etransitivity; [ apply Hperm | ].
    rewrite -> map_app.
    apply Permutation.Permutation_app_head.
    destruct (tc_attach_nodes _ _) as [(?, ?, ?) ?].
    now simpl.
  Qed.

  Hypotheses (Hnodup : List.NoDup (map tc_roottid (tc_flatten tc))) (Hnodup' : List.NoDup (map tc_roottid (tc_flatten tc'))).
  Collection collection_nodup := Hnodup Hnodup'.

  (* TODO there may be some repetition below ... *)

  (* a refined result *)
  Lemma tc_join_partial_dom_partial_info :
    Permutation.Permutation (map tc_rootinfo_partial (tc_flatten (tc_join_partial tc tc')))
      (map tc_rootinfo_partial (tc_flatten (fst (tc_detach_nodes (tc_flatten tc') tc))) ++
        map tc_rootinfo_partial (tc_flatten tc') ++
        map tc_rootinfo_partial (flat_map tc_flatten (flat_map tc_rootchn
                (snd (tc_detach_nodes (tc_flatten tc') tc))))).
  Proof.
    pose proof tc_join_partial_dom_info as Hperm.
    pose proof (tc_attach_nodes_dom_info _ _ Hnodup Hnodup') as Hperm'.
    rewrite <- map_app in Hperm, Hperm'.
    apply Permutation_rootinfo2partialinfo in Hperm, Hperm'.
    etransitivity; [ apply Hperm | ].
    rewrite -> map_app.
    apply Permutation.Permutation_app_head.
    rewrite -> map_app in Hperm'.
    destruct (tc_attach_nodes (snd (tc_detach_nodes (tc_flatten tc') tc)) tc') as [(?, ?, ?) ?].
    etransitivity; [ apply Hperm' | ].
    reflexivity.
  Qed.

  Corollary tc_join_partial_dom_tid' :
    Permutation.Permutation (map tc_roottid (tc_flatten (tc_join_partial tc tc')))
      (map tc_roottid (tc_flatten (fst (tc_detach_nodes (tc_flatten tc') tc))) ++
        map tc_roottid (tc_flatten tc') ++
        map tc_roottid (flat_map tc_flatten (flat_map tc_rootchn
                (snd (tc_detach_nodes (tc_flatten tc') tc))))).
  Proof.
    pose proof (tc_attach_nodes_dom_info _ _ Hnodup Hnodup') as Hperm.
    rewrite <- map_app in Hperm.
    apply Permutation_rootinfo2roottid in Hperm.
    rewrite -> map_app in Hperm.
    etransitivity; [ apply tc_join_partial_dom_tid; auto | ].
    now apply Permutation.Permutation_app_head.
  Qed.

  (* Hypothesis (Hnotin : find (has_same_tid (tc_roottid tc)) (tc_flatten tc') = None). *)
  Hypothesis (Hnotin : ~ In (tc_roottid tc) (map tc_roottid (tc_flatten tc'))).

  Corollary tc_join_partial_dom_partial_info' :
    Permutation.Permutation (map tc_rootinfo_partial (tc_flatten (tc_join_partial tc tc')))
      (map tc_rootinfo_partial (filter (fun sub => 
              negb (find (has_same_tid (tc_roottid sub)) (tc_flatten tc'))) (tc_flatten tc)) ++
        map tc_rootinfo_partial (tc_flatten tc')).
  Proof.
    etransitivity; [ apply tc_join_partial_dom_partial_info | ].
    etransitivity; [ apply Permutation.Permutation_app_swap_app | ].
    etransitivity; [ | apply Permutation.Permutation_app_comm ].
    apply Permutation.Permutation_app_head.
    rewrite <- map_app.
    apply Permutation_rootinfo2partialinfo.
    rewrite -> map_app.
    apply tc_detach_nodes_dom_partition''; try assumption.
    rewrite -> tc_getnode_in_iff in Hnotin.
    now destruct (find _ _); unfold is_true in Hnotin.
  Qed.

  Corollary tc_join_partial_tid_nodup :
    List.NoDup (map tc_roottid (tc_flatten (tc_join_partial tc tc'))).
  Proof.
    pose proof tc_join_partial_dom_partial_info' as Hperm.
    rewrite <- map_app in Hperm.
    eapply Permutation.Permutation_NoDup; [ symmetry; apply Permutation_partialinfo2roottid, Hperm | ].
    rewrite -> map_app.
    rewrite <- base.NoDup_ListNoDup, -> list.NoDup_app, -> ! base.NoDup_ListNoDup.
    repeat setoid_rewrite -> base.elem_of_list_In.
    (* ... have to use map_filter_comm *)
    pose proof (map_filter_comm tc_roottid (fun t => negb (find (has_same_tid t) (tc_flatten tc'))) (tc_flatten tc)) as Htmp.
    simpl in Htmp.
    rewrite <- ! Htmp.
    clear Htmp.
    split; [ now apply NoDup_filter | split; try assumption ].
    intros t (Hin & E)%filter_In Hin'%tc_getnode_in_iff.
    now rewrite -> Hin' in E.
  Qed.

  Lemma tc_join_partial_getclk t :
    tc_getclk t (tc_join_partial tc tc') = match tc_getnode t tc' with Some res => tc_rootclk res | None => tc_getclk t tc end.
  Proof.
    pose proof tc_join_partial_dom_partial_info' as Hperm.
    rewrite -> Permutation.Permutation_app_comm, <- map_app in Hperm.
    pose proof (tc_getclk_perm_congr_pre _ _ tc_join_partial_tid_nodup Hperm t) as Htmp.
    rewrite -> find_app in Htmp.
    fold (tc_getnode t (tc_join_partial tc tc')) in Htmp.
    rewrite -> tc_getclk_viewchange, -> Htmp.
    fold (tc_getnode t tc').
    destruct (tc_getnode t tc') as [ res | ] eqn:Eres; simpl.
    1: reflexivity.
    unfold tc_getclk.
    destruct (find _ _) as [ res' | ] eqn:Eres' in |- *; simpl.
    - apply find_some in Eres'.
      rewrite -> has_same_tid_true, -> filter_In, -> negb_true_iff in Eres'.
      destruct Eres' as ((Hres' & _) & ->).
      unfold tc_getnode.
      pose proof (tid_nodup_find_self _ Hnodup) as Htmp2%Foralltc_Forall_subtree.
      eapply Foralltc_subtc in Htmp2.
      2: apply Hres'.
      now rewrite -> Htmp2.
    - destruct (tc_getnode t tc) as [ res'' | ] eqn:Eres''.
      2: reflexivity.
      apply find_some in Eres''.
      rewrite -> has_same_tid_true in Eres''.
      destruct Eres'' as (Eres'' & ->).
      apply find_none with (x:=res'') in Eres'.
      2:{
        rewrite -> filter_In, -> negb_true_iff.
        split; try assumption.
        unfold tc_getnode in Eres.
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
    pose proof (tc_join_go tc tc') as Ejoin. (* get partial *)
    rewrite -> Etc' in Ejoin at 1 2.
    simpl in Ejoin.
    specialize (Ejoin Eclk_lt).
    rewrite <- ! Etc'.
    remember (tc_get_updated_nodes_join tc tc') as prefix_tc' eqn:Eprefix.
    destruct (tc_detach_nodes (tc_flatten prefix_tc') tc) as (pivot, forest) eqn:Edetach.
    destruct (tc_attach_nodes forest prefix_tc') as [ni chn_w] eqn:Eattach.
    pose proof (tc_attach_nodes_rootinfo_same forest prefix_tc') as Eni.
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Eni_z.
    rewrite -> Eattach, -> Eprefix, -> (prefixtc_rootinfo_same _ _ (tc_get_updated_nodes_join_is_prefix _ _)), 
      -> Etc' in Eni.
    rewrite -> Edetach in Eni_z.
    destruct pivot as [ni_z chn_z] eqn:Epivot.
    simpl in Eni, Eni_z.
    subst ni ni_z.

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
    - (* manipulate *)
      pose proof (tc_join_partial_tid_nodup tc (tc_get_updated_nodes_join tc tc') (tid_nodup _ Hshape)) as Htmp.
      pose proof (tid_nodup_prefix_preserve _ _ (tc_get_updated_nodes_join_is_prefix tc tc')) as Htmp2.
      rewrite -> Etc' in Htmp2 at 1.
      specialize (Htmp2 (tid_nodup _ Hshape')).
      pose proof (tc_get_updated_nodes_join_adequacy _ Hshape' _ Hrespect) as Htmp3.
      simpl tc_rootclk in Htmp3.
      simpl tc_roottid in Htmp3.
      specialize (Htmp3 Eclk_lt (tc_roottid tc)).
      apply Nat.nlt_ge in Hroot_clk_le.
      unfold tc_getclk in Htmp3 at 1.
      rewrite -> tc_getnode_self in Htmp3.
      rewrite -> Htmp3, <- tc_getnode_subtc_iff, <- Etc' in Hroot_clk_le.
      specialize (Htmp Htmp2 Hroot_clk_le).
      unfold tc_join_partial in Htmp.
      now rewrite <- Eprefix, -> Edetach, -> Eattach in Htmp.
    - now simpl.
    - simpl.
      pose proof (tc_shape_inv_tc_detach_nodes_fst (tc_flatten prefix_tc') tc Hshape) as H.
      apply aclk_upperbound, Foralltc_self in H.
      rewrite -> Edetach in H.
      destruct tc as [(?, clk_z, ?) ?].
      simpl in H |- *.
      rewrite -> List.Forall_forall in H.
      destruct chn_z as [ | ch ? ]; simpl.
      1: lia.
      now specialize (H _ (or_introl eq_refl)).
  Qed.

  Lemma tc_join_pointwise_max_pre
    (Hroot_clk_lt : tc_getclk (tc_roottid tc') tc < tc_rootclk tc') t :
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
    specialize (Htmp3' (tc_roottid tc)).
    apply Nat.nlt_ge in Hroot_clk_le.
    unfold tc_getclk in Htmp3' at 1.
    rewrite -> tc_getnode_self in Htmp3'.
    rewrite -> Htmp3', <- tc_getnode_subtc_iff in Hroot_clk_le.
    specialize (Htmp Htmp2 Hroot_clk_le).

    rewrite -> Htmp.
    destruct (tc_getnode t (tc_get_updated_nodes_join tc tc')) as [ res | ] eqn:Eres.
    - match type of Eres with ?a = _ => assert (a) as Eres' by now rewrite Eres end.
      rewrite <- Htmp3 in Eres'.
      pose proof Eres as (Eres2 & <-)%tc_getnode_has_tid.
      apply in_map with (f:=tc_rootinfo), (prefixtc_flatten_info_incl _ _ Hprefix), in_map_iff in Eres2.
      destruct Eres2 as (res2 & Einfo & Hres2).
      (* TODO extract this unifying process? *)
      pose proof (tid_nodup_find_self _ (tid_nodup _ Hshape')) as HH%Foralltc_Forall_subtree.
      eapply Foralltc_subtc in HH.
      2: apply Hres2.
      rewrite -> (tc_rootinfo_tid_inj _ _ Einfo) in HH.
      replace (tc_rootclk res) with (tc_getclk (tc_roottid res) tc').
      2: unfold tc_getclk, tc_getnode, tc_rootclk; now rewrite -> HH, -> Einfo.
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
    pose proof (tc_attach_nodes_rootinfo_same forest prefix_tc') as Eni.
    epose proof (tc_detach_nodes_fst_rootinfo_same _ _) as Eni_z.
    rewrite -> Eattach, -> Eprefix, -> (prefixtc_rootinfo_same _ _ (tc_get_updated_nodes_join_is_prefix _ _)), 
      -> Etc' in Eni.
    rewrite -> Edetach in Eni_z.
    destruct pivot as [ni_z chn_z] eqn:Epivot.
    simpl in Eni, Eni_z.
    subst ni ni_z.
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

(* TODO not sure whether this will be useful ... maybe it is too weak *)

Fact tc_get_updated_nodes_join_trace tc' : forall tc sub_prefix
  (H : subtc sub_prefix (tc_get_updated_nodes_join tc tc')), 
  exists sub, subtc sub tc' /\ sub_prefix = tc_get_updated_nodes_join tc sub.
Proof.
  induction tc' as [(u', clk', aclk') chn' IH] using treeclock_ind_2; intros.
  tc_get_updated_nodes_join_unfold in_ H.
  cbn delta [tc_flatten In info_tid] beta iota in H.
  destruct H as [ <- | (ch & Hin_ch & H)%in_flat_map ].
  - eexists. 
    split; [ apply tc_flatten_self_in | ].
    reflexivity.
  - pose proof (tc_get_updated_nodes_join_aux_result_submap tc (tc_getclk u' tc) chn') 
      as (chn'' & Hsl & E).
    rewrite -> E in Hin_ch.
    apply in_map_iff in Hin_ch.
    destruct Hin_ch as (ch'' & <- & Hin_ch).
    pose proof (sublist_In _ _ Hsl _ Hin_ch) as Hin_ch'.
    eapply Forall_forall in IH.
    2: apply Hin_ch'.
    destruct (IH _ _ H) as (sub & Hsub & ->).
    exists sub.
    split; [ | reflexivity ].
    now eapply subtc_trans; [ | apply subtc_chn; simpl; apply Hin_ch' ].
Qed.

(* TODO tc_join tc tc' = tc_join tc (prefix); this may not be useful enough, though *)

Section Preorder_Prefix_Theory.

(* it is very difficult to use only one version of this ... *)

Fixpoint tc_vertical_splitr (full : bool) tc (l : list nat) : treeclock :=
  match l with
  | nil => Node (tc_rootinfo tc) (if full then tc_rootchn tc else nil)
  | x :: l' =>
    match nth_error (tc_rootchn tc) x with
    | Some ch => Node (tc_rootinfo tc) (tc_vertical_splitr full ch l' :: skipn (S x) (tc_rootchn tc))
    (* | None => Node (tc_rootinfo tc) (skipn (S x) (tc_rootchn tc)) *)
    | None => Node (tc_rootinfo tc) nil
    end
  end.

(* compute both the positions and thread ids at the same time *)

Fixpoint tc_traversal_waitlist tc (l : list nat) : (list (list nat)) * (list treeclock) :=
  match l with
  | nil => (nil, nil)
  | x :: l' =>
    match nth_error (tc_rootchn tc) x with
    | Some ch => 
      let: (res1, res2) := (tc_traversal_waitlist ch l') in
      ((map (fun i => i :: nil) (seq 0 x)) ++ (map (fun l0 => x :: l0) res1), (firstn x (tc_rootchn tc)) ++ res2)
    | None => 
      ((map (fun i => i :: nil) (seq 0 (length (tc_rootchn tc)))), (tc_rootchn tc))
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

Lemma tc_traversal_waitlist_continue_trivial tc l y (Hle : y <= length (tc_rootchn tc))
  (H : tc_traversal_waitlist tc l = (map (fun i => i :: nil) (seq 0 y), firstn y (tc_rootchn tc)))
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
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
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
  prefixtc (tc_vertical_splitr full tc l) tc.
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
    stk = (map tc_roottid (snd (tc_traversal_waitlist tc l) ++ (sub :: nil))) ->
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
    stk = (map tc_roottid (snd (tc_traversal_waitlist tc l) ++ (sub :: nil))) /\
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
  (Hsub : tc_locate tc l = Some sub) (Echn : tc_rootchn sub <> nil) :
  tc_traversal_snapshot tc 
    (map tc_roottid (snd (tc_traversal_waitlist tc l) ++ tc_rootchn sub)) 
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
  (Hsub : tc_locate tc l = Some sub) (Echn : tc_rootchn sub = nil) :
  tc_traversal_snapshot tc 
    (map tc_roottid (snd (tc_traversal_waitlist tc l))) 
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
    (map tc_roottid (snd (tc_traversal_waitlist tc l) ++ tc_rootchn sub)) 
    (tc_vertical_splitr false tc l).
Proof.
  destruct (list_ifnil_destruct (tc_rootchn sub)) as [ H | H ].
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
  tc_traversal_snapshot tc (map tc_roottid (tc_rootchn tc)) (Node (tc_rootinfo tc) nil).
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
    base.fmap tc_rootinfo (tc_locate (tc_attach_nodes forest tc) l) = Some (tc_rootinfo sub).
Proof.
  induction tc as [ni chn IH] using treeclock_ind_2; intros.
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
