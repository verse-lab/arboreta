Require Import VST.floyd.proofauto.

(* allp is not easy to work with ... so turn to fold sepcon *)

(*
Lemma data_at_array_to_forall (lclk : list (reptype t_struct_clock)) plclk dim
  (Hdim : 0 < dim) (Hlen : Zlength lclk = dim) :
  data_at Tsh (tarray t_struct_clock dim) lclk plclk |--
  ALL i : Z, !! (0 <= i < dim) -->
    data_at Tsh t_struct_clock (Znth i lclk) 
    (offset_val (sizeof t_struct_clock * i) plclk).
Proof.
*)

Fact fold_right_fold_right_sepcon_eq l : 
  fold_right sepcon emp l = fold_right_sepcon l.
Proof. induction l as [ | m l IH ]; auto. Qed.

(* NOTE: may use fold_left_sepconx instead, if necessary? *)

Fact fold_sepcon_left_right_eq l :
  fold_left sepcon l emp = fold_right sepcon emp l.
Proof.
  apply fold_symmetric.
  - intros; now rewrite sepcon_assoc.
  - intros; apply sepcon_comm.
Qed.

Fact Zfunc_list_proj {A : Type} `{Inhabitant A} (f : Z -> A) dim (Hdim : 0 <= dim) :
  exists l : list A, 
    Zlength l = dim /\ forall i : Z, 0 <= i < dim -> Znth i l = f i.
Proof.
  remember (Z.to_nat dim) as n eqn:E.
  revert dim Hdim E. 
  induction n as [ | n IH ]; intros.
  - replace dim with 0 by lia. exists nil. list_solve.
  - assert (n = Z.to_nat (dim - 1)) as H1 by lia.
    assert (0 <= dim - 1) as H2 by lia.
    specialize (IH _ H2 H1). destruct IH as (l & Hl & HH).
    exists (l ++ [f (dim - 1)]).
    split. 1: list_solve.
    intros i Hi. destruct (Z.eq_dec i (dim - 1)) as [ -> | Hneq ].
    + now rewrite sublist.Znth_app1.
    + rewrite Znth_app1; try list_solve. apply HH. lia.
Qed.

(* FIXME: not really useful *)

Fact sepcon_map_data_at_innerext {cs : compspecs} (sh : Share.t) (t : type) (p : val) 
  (f g : Z -> reptype t) (st : list Z) 
  (Hext : forall i, In i st -> f i = g i) :
  fold_right_sepcon (map (fun i => data_at sh t (f i)
    (offset_val (sizeof t * i) p)) st) =
  fold_right_sepcon (map (fun i => data_at sh t (g i)
    (offset_val (sizeof t * i) p)) st).
Proof.
  erewrite -> map_ext_Forall. 1: reflexivity.
  rewrite -> Forall_forall. 
  intros i Hin. apply Hext in Hin. now rewrite Hin.
Qed.

Lemma sepcon_map_data_at_merge_app {A : Type} (fdec : forall a a' : A, {a = a'} + {a <> a'})
  (f g : A -> mpred) (st1 st2 : list A) 
  (Hdj : forall a, In a st1 -> In a st2 -> False) :
  (fold_right_sepcon (map f st1) * fold_right_sepcon (map g st2))%logic = 
  fold_right_sepcon (map (fun a => if in_dec fdec a st1 then f a else g a) (st1 ++ st2)).
Proof.
  erewrite -> map_ext_Forall with (l:=st1).
  erewrite -> map_ext_Forall with (l:=st2).
  1: rewrite <- fold_right_sepcon_app, <- map_app; reflexivity.
  all: apply Forall_forall; intros i Hin; specialize (Hdj i); 
    destruct (in_dec fdec i st1), (in_dec fdec i st2); auto; tauto.
Qed.

(*
Lemma sepcon_map_data_at_merge_app {cs : compspecs} (sh : Share.t) (t : type) (p : val) 
  (f g : Z -> reptype t) (st1 st2 : list Z) 
  (Hdj : forall i, In i st1 -> In i st2 -> False) :
  (fold_right_sepcon (map (fun i => data_at sh t (f i)
    (offset_val (sizeof t * i) p)) st1) *
  fold_right_sepcon (map (fun i => data_at sh t (g i)
    (offset_val (sizeof t * i) p)) st2))%logic = 
  fold_right_sepcon (map (fun i => data_at sh t 
    (* eta? *)
    ((fun i' => if in_dec Z.eq_dec i st1 then f i' else g i') i)
    (offset_val (sizeof t * i) p)) (st1 ++ st2)).
Proof.
  erewrite -> sepcon_map_data_at_innerext with (st:=st1).
  erewrite -> sepcon_map_data_at_innerext with (st:=st2).
  1: rewrite <- fold_right_sepcon_app, <- map_app; reflexivity.
  all: simpl; intros i Hin; specialize (Hdj i); 
    destruct (in_dec Z.eq_dec i st1), (in_dec Z.eq_dec i st2); auto; tauto.
Qed.
*)

Lemma sepcon_map_data_at_merge_sepcon {cs : compspecs} {A : Type}
  (f g : A -> mpred) (st : list A) :
  (fold_right_sepcon (map f st) * fold_right_sepcon (map g st))%logic = 
  fold_right_sepcon (map (fun i => (f i * g i)%logic) st).
Proof. 
  induction st; simpl; autorewrite with norm; auto.
  rewrite <- IHst. 
  (* go classic *)
  apply pred_ext; entailer!.
Qed.

Lemma data_at_array_unfold {cs : compspecs} (sh : Share.t) (t : type) (l : list (reptype t))
  (p : val) dim (Hdim : 0 < dim) (Hlen : Zlength l = dim) :
  data_at sh (tarray t dim) l p |--
  !! (field_compatible (tarray t dim) [] p) &&
  fold_right_sepcon (map (fun i => data_at sh t (Znth i l) 
    (offset_val (sizeof t * i) p)) (upto (Z.to_nat dim))).
Proof.
  entailer!. clear H H0.
  induction l as [ | v l IH ] using rev_ind; intros.
  - rewrite Zlength_nil in Hdim. lia.
  - destruct l eqn:E.
    + simpl in *. 
      assert_PROP (isptr p) by entailer.
      (* go classic *)
      erewrite -> data_at_singleton_array_eq. 2: reflexivity.
      rewrite Znth_0_cons.
      replace (sizeof t * 0) with 0 by lia.
      rewrite isptr_offset_val_zero; auto.
      entailer.
    + rewrite <- E in *.
      assert (0 < Zlength l) as Hlen by (subst; list_solve).
      clear E. apply IH in Hlen.
      erewrite -> split2_data_at_Tarray_app.
      2: reflexivity.
      2: list_solve.
      sep_apply Hlen.
      replace (Zlength (l ++ [v])) with (Zlength l + 1) in * by list_solve.
      replace ((Zlength l + 1) - Zlength l) with 1 by lia.
      rewrite -> app_length, -> upto_app. simpl.
      (* use Permutation to change *)
      match goal with |- _ |-- fold_right_sepcon ?l =>
        erewrite -> fold_right_sepcon_permutation with (al:=l) end.
      2: apply Permutation_map, Permutation_app_comm.
      simpl. 
      rewrite sepcon_comm at 1.
      rewrite <- ! Zlength_correct.
      rewrite -> sublist.Znth_app1; try lia.
      (* go classic, again *)
      erewrite -> data_at_singleton_array_eq. 2: reflexivity.
      (* well ... *)
      assert_PROP (is_pointer_or_null (field_address0
        (tarray t (Zlength l + 1)) (SUB Zlength l) p)) by entailer!.
      rewrite field_address0_clarify; auto.
      simpl. rewrite -> Z.add_0_l, -> Z.add_0_r.
      apply cancel_left.
      erewrite -> sepcon_map_data_at_innerext. 1: apply derives_refl.
      intros i Hin. simpl. 
      rewrite -> In_upto, <- Zlength_correct in Hin.
      now rewrite -> Znth_app1; try lia.
Qed.

(* TODO this can be done in another way: forall such l, prove that this holds on l
  but we have Znth_eq_ext, so this will not bother too much ... maybe modify the proof later *)

Lemma data_at_array_fold {cs : compspecs} (sh : Share.t) (t : type) (p : val) dim (Hdim : 0 < dim)
  (f : Z -> reptype t) (Hcomp : field_compatible (tarray t dim) [] p) :
  fold_right_sepcon (map (fun i => data_at sh t (f i)
    (offset_val (sizeof t * i) p)) (upto (Z.to_nat dim))) |--
  EX l : list (reptype t), 
    !! (Zlength l = dim) && !! (forall i, 0 <= i < dim -> Znth i l = f i) &&
    data_at sh (tarray t dim) l p.
Proof.
  remember (Z.to_nat dim) as n eqn:E.
  replace dim with (Z.of_nat n) in Hdim by lia.
  revert dim E Hcomp. 
  induction n as [ | n IH ]; intros.
  - lia.
  - destruct n eqn:EE.
    + assert (dim = 1) as -> by lia.
      simpl. Exists (f 0 :: nil).
      assert_PROP (isptr p) by entailer.
      (* go classic *)
      erewrite <- data_at_singleton_array_eq. 2: reflexivity.
      replace (sizeof t * 0) with 0 by lia.
      rewrite isptr_offset_val_zero; auto.
      entailer!. intros. replace i with 0 by lia. now rewrite Znth_0_cons.
    + rewrite <- EE in *.
      assert (0 < Z.of_nat n) as Htmp by lia. clear EE.
      assert (n = Z.to_nat (dim - 1)) as Htmp2 by lia.
      assert_PROP (field_compatible (tarray t (dim - 1)) [] p) as Htmp3 by entailer.
      specialize (IH Htmp (dim - 1) Htmp2 Htmp3).
      replace (S n) with (n + 1)%nat by lia.
      rewrite -> upto_app. simpl. rewrite Z.add_0_r. 
      replace (Z.of_nat n) with (dim - 1) by lia.
      (* use Permutation to change *)
      match goal with |- fold_right_sepcon ?l |-- _ =>
        erewrite -> fold_right_sepcon_permutation with (al:=l) end.
      2: apply Permutation_map, Permutation_app_comm.
      simpl. sep_apply IH. Intros l.
      Exists (l ++ (f (dim - 1) :: nil)).
      erewrite -> split2_data_at_Tarray_app; auto.
      2: list_solve.
      rewrite Zlength_app.
      rewrite H. replace (dim - (dim - 1)) with 1 by lia.
      (* go classic, again *)
      erewrite -> data_at_singleton_array_eq. 2: reflexivity.
      rewrite arr_field_address0; auto; try lia.
      entailer!. split.
      * list_solve.
      * intros. destruct (Z.eq_dec i (dim - 1)) as [ -> | Hn ].
        1: rewrite sublist.Znth_app1; auto; try lia.
        assert (i < dim - 1) by lia.
        rewrite app_Znth1; try lia. now apply H0.
Qed.
