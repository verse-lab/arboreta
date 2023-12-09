From Coq Require Import List RelationClasses Permutation Morphisms Sorting PeanoNat.

(* PROBLEM: any other useful rewriting rule? *)
(* Some generic rewriting rules for "Permutation". *)

Add Parametric Morphism [A] : (@app A) with
  signature (@Permutation A) ==> (@Permutation A) ==> (@Permutation A) as perm_app_mor.
Proof. intros. apply Permutation_app; assumption. Qed.

Add Parametric Morphism [A] : (@cons A) with
  signature (@eq A) ==> (@Permutation A) ==> (@Permutation A) as perm_cons_mor.
Proof. intros. constructor. assumption. Qed.

Lemma Permutation_app_head_iff [A : Type] (l tl tl' : list A) :
  Permutation tl tl' <-> Permutation (l ++ tl) (l ++ tl').
Proof.
  split; intros H.
  - apply Permutation_app_head. assumption.
  - apply Permutation_app_inv_l in H. assumption.
Qed.

Lemma Permutation_app_tail_iff [A : Type] (l l' tl : list A) :
  Permutation l l' <-> Permutation (l ++ tl) (l' ++ tl).
Proof.
  split; intros H.
  - apply Permutation_app_tail. assumption.
  - apply Permutation_app_inv_r in H. assumption.
Qed.
