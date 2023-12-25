From Coq Require Import List Bool Lia PeanoNat Sorting RelationClasses Permutation.
From arboreta Require Import util rosetree.

From stdpp Require list.

(*
  This file demonstrates one possible way to project a tree onto a list, 
    which can be used in separation logic proofs. Users are encouraged to 
    defined their own projections based on this file. 

  The projection is pure but maybe not very generic, so it is defined outside
    "rosetree.v", while the file is in the same directory as "rosetree.v". 
*)

Class NodeInfoProjector (A PN : Type) :=
  nodeinfo_proj : tree A -> PN.

Class NodeInfoProjRelation (A B PN : Type) :=
  infoarray_proj_onto : forall (a : PN) (x : B) (l : list PN), Prop.

Class TreeStructProjector (A B PS : Type) :=
  tr_struct_proj : forall (par : option B) (prev : option B) (next : option B) (tr : tree A), PS.

Class TreeStructProjRelation (A B PS : Type) :=
  nodearray_proj_onto : forall (a : PS) (x : B) (l : list PS), Prop.

Global Arguments nodeinfo_proj {_ _ _} !_ /.

Section Tree_Projection.

Local Ltac intuition_solver ::= auto.

Context {A B : Type} `{B_getter : IdGetter A B}. (* usually, B can be nat or Z *)

Local Notation tree := (@rosetree.tree A).

Context {PN : Type}. (* the type of payload for node info *)

Context {PS : Type}. (* the type of payload for tree structure *)

(*
  Here, we distinguish between two types of payloads: the one for storing node 
    information, and the one for representing the spatial structure of tree.
    For example, "PN" can be the int type, while "PS" represents a struct. 
    They can be used together for modelling the following array-based tree in C:

  int val[N];
  struct node { int par, fch, nxt; };
  struct node tree[N];
*)

Context `{PNProj : NodeInfoProjector A PN} `{PSProj : TreeStructProjector A B PS}
  `{PNArrProj : NodeInfoProjRelation A B PN} `{PSArrProj : TreeStructProjRelation A B PS}.

(* users may change the following usage of "nth_error" into another function 
  (e.g., "Znth" in VST, or simply "nth") *)

Definition infoarray_proj (l : list PN) (tr : tree) : Prop :=
  Foralltr (fun tr' => infoarray_proj_onto (nodeinfo_proj tr') (tr_rootid tr) l) tr.

Definition nodearray_proj_chnaux (par : option B) (l : list PS) :
  forall (prev : option B) (chn : list tree), Prop := 
  fix aux prev chn {struct chn} : Prop := 
  match chn with
  | nil => True
  | ch :: chn' => nodearray_proj_onto (tr_struct_proj par prev (base.fmap tr_rootid (hd_error chn')) ch)
      (tr_rootid ch) l /\
    aux (Some (tr_rootid ch)) chn'
  end.

Definition nodearray_proj_chn (l : list PS) (tr : tree) : Prop :=
  nodearray_proj_chnaux (Some (tr_rootid tr)) l None (tr_rootchn tr).

Global Arguments nodearray_proj_chn _ _/.

Definition nodearray_proj_single (par prev next : option B) (l : list PS) (tr : tree) : Prop :=
  nodearray_proj_onto (tr_struct_proj par prev next tr) (tr_rootid tr) l.

Definition nodearray_proj_root (l : list PS) (tr : tree) : Prop :=
  Eval unfold nodearray_proj_single in nodearray_proj_single None None None l tr.

Definition nodearray_proj_pre (l : list PS) (tr : tree) : Prop :=
  Foralltr (nodearray_proj_chn l) tr.

(* for the whole tree *)
Definition nodearray_proj (l : list PS) (tr : tree) : Prop :=
  nodearray_proj_root l tr /\ nodearray_proj_pre l tr.

Definition nodearray_proj' (par prev next : option B) (l : list PS) (tr : tree) : Prop :=
  nodearray_proj_single par prev next l tr /\ nodearray_proj_pre l tr.

End Tree_Projection.
