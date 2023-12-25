Require Import VST.floyd.proofauto.
From Coq Require Import List Bool Lia PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.

From arboreta.utils Require Import util.

Fact nth_error_some_inrange_Z {A : Type} (i : nat) (al : list A) a : 
  nth_error al i = Some a -> Z.of_nat i < Zlength al.
Proof. 
  intros H. apply nth_error_some_inrange in H. 
  rewrite <- ZtoNat_Zlength in H. lia.
Qed.

Fact nth_error_Znth_result {A : Type} `{Inhabitant A} n (l : list A) res : 
  nth_error l n = Some res -> Znth (Z.of_nat n) l = res.
Proof.
  intros HH. apply List.nth_error_nth with (d:=default) in HH.
  now rewrite <- nth_Znth'.
Qed.

Fact Znth_nth_error_result {A : Type} `{Inhabitant A} n (l : list A) res 
  (Hlt : (n < length l)%nat) :
  Znth (Z.of_nat n) l = res -> nth_error l n = Some res.
Proof.
  intros HH. apply nth_error_nth' with (d:=default) in Hlt.
  rewrite -> Hlt, <- HH. f_equal. now apply nth_Znth'.
Qed.

Fact repable_signed_Z_eqb_Int_eq (x y : Z) 
  (Hx : repable_signed x) (Hy : repable_signed y) :
  Z.eqb x y = Int.eq (Int.repr x) (Int.repr y).
Proof.
  pose proof (int_cmp_repr Ceq _ _ Hx Hy) as H.
  pose proof (int_cmp_repr Cne _ _ Hx Hy) as H0.
  simpl in H, H0.
  destruct (Int.eq (Int.repr x) (Int.repr y)) eqn:E; intuition.
Qed.

Fact upto_seq n : upto n = map Z.of_nat (seq 0%nat n).
Proof. 
  induction n; simpl; auto. f_equal. 
  rewrite <- seq_shift, -> IHn, -> ! map_map.
  apply map_ext. intros. now rewrite -> Nat2Z.inj_succ.
Qed.

Fact seq_upto n : seq 0%nat n = map Z.to_nat (upto n).
Proof.
  rewrite -> upto_seq, -> map_map. rewrite <- map_id at 1.
  apply map_ext. intros. now rewrite Nat2Z.id.
Qed.
