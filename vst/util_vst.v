Require Import VST.floyd.proofauto.
From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.

Section Short_Integer_Type.

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
  pose proof (Zpower_nat_gt_0 2%Z 15) as H.
  pose proof (Zpower_nat_gt_0 2%Z 16) as H0. 
  nia.
Qed.

Fact short_max_signed_gt_0 : 0 < short_max_signed.
Proof. 
  unfold short_max_signed, two_power_nat. 
  rewrite -> shift_nat_correct, -> Zaux.Zpower_nat_S.
  pose proof (Zpower_nat_gt_0 2%Z 14) as H. lia.
Qed.

End Short_Integer_Type.

(* a little fact ... TODO why this is not in stdlib? *)
Fact nth_error_some_inrange {A : Type} (i : nat) (al : list A) a : 
  nth_error al i = Some a -> (i < length al)%nat.
Proof.
  revert i a. induction al as [ | a' al IH ]; intros; simpl in *.
  - destruct i; now simpl in H.
  - destruct i; try lia. simpl in H. apply IH in H. lia.
Qed.

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
  - now apply Z.eqb_eq.
  - now apply Z.eqb_neq.
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
