From Coq Require Import List Bool Lia ssrbool PeanoNat.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
(* From Coq Require Import List Bool Lia. *)
(* From stdpp Require Import list. *)
(* ? *)

(* Section VectorClock.

Definition vectorclock := nat -> option nat.

End VectorClock. *)

Section TreeClock.

Context {thread : Type} (thread_eqdec : forall (t1 t2 : thread), {t1 = t2} + {t1 <> t2}).

Record nodeinfo : Type := mkInfo {
  info_tid : thread;
  info_clk : nat;
  info_aclk : option nat
}.

Inductive treeclock : Type :=
  (* Node (t : thread) (clk : nat) (aclk : option nat) (chn : list treeclock). *)
  Node (ni : nodeinfo) (chn : list treeclock).

Definition tc_init t := Node (mkInfo t 0 None) nil.

(* return a ThrMap ? *)

Fixpoint tc_flatten tc :=
  let: Node ni chn := tc in ni :: (List.flat_map tc_flatten chn).

(* Search (_ -> option _) inside List. *)

(* Fixpoint tc_find [A : Type] tc t (cont : thread -> nat -> option nat -> A) : option A :=
  match tc with
  Node t' clk aclk chn => 
    if Thr_eqdec t t'
    then Some (cont t clk aclk)
    else 
  end. *)

Definition tc_getnode tc t :=
  List.find (fun ni => thread_eqdec t (info_tid ni)) (tc_flatten tc).

Definition tc_rootinfo tc :=
  let: Node ni _ := tc in ni.

Definition tc_rootchn tc :=
  let: Node _ chn := tc in chn.

(* the same as paper, use 0 as default clk *)

Definition tc_getclk tc t :=
  match tc_getnode tc t with
  | Some res => info_clk res
  | _ => 0
  end.

Definition tc_getaclk tc t :=
  match tc_getnode tc t with
  | Some res => info_aclk res
  | _ => None
  end.

Definition tc_getaclk_default tc t :=
  match tc_getaclk tc t with
  | Some res => res
  | _ => 0
  end.

Definition option_nat_leb o1 o2 :=
  match o1, o2 with
  | Some n1, Some n2 => n1 <=? n2
  | _, _ => false
  end.

(* return a tree instead of a stack? *)
(* TODO here, aclk can be none, which tends to be troublesome. can this be eliminated? *)

Fixpoint tc_get_updated_nodes_join tc tc' : treeclock :=
  let fix tc_get_updated_nodes_join_aux tc u' chn_u' : list treeclock :=
  match chn_u' with
  | nil => nil
  | tc' :: chn_u'' => 
    let: Node info_v' chn_v' := tc' in
    let: mkInfo v' clk_v' aclk_v' := info_v' in
    if (tc_getclk tc v') <? clk_v'
    then (tc_get_updated_nodes_join tc tc') :: (tc_get_updated_nodes_join_aux tc u' chn_u'')
    else 
      (if option_nat_leb aclk_v' (tc_getaclk tc u')
        then nil
        else (tc_get_updated_nodes_join_aux tc u' chn_u''))
  end in
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (info_tid info_u') chn_u')
.

(* as is expected, the following cannot pass the decrease test. *)
(*
Fixpoint tc_get_updated_nodes_join_aux tc u' chn_u' : list treeclock :=
  match chn_u' with
  | nil => nil
  | tc' :: chn_u'' => 
    let: Node info_v' chn_v' := tc' in
    let: mkInfo v' clk_v' aclk_v' := info_v' in
    if (tc_getclk tc v') <? clk_v'
    then (tc_get_updated_nodes_join tc tc') :: (tc_get_updated_nodes_join_aux tc u' chn_u'')
    else 
      (if option_nat_leb aclk_v' (tc_getaclk tc u')
        then nil
        else (tc_get_updated_nodes_join_aux tc u' chn_u''))
  end
with tc_get_updated_nodes_join tc tc' : treeclock :=
  let: Node info_u' chn_u' := tc' in
  Node info_u' (tc_get_updated_nodes_join_aux tc (info_tid info_u') chn_u')
.
*)

(* Fixpoint tc_get_updated_nodes_join tc u' chn : treeclock :=
  match chn with
   *)

(* given a tree and a list of targets, return a pivot tree and a list of splitted trees *)

Fixpoint tc_detach_nodes targets tc : treeclock * list treeclock :=
  let: Node ni chn := tc in
  let: (new_chn, res) := List.split (map (tc_detach_nodes targets) chn) in
  let: (res', new_chn') := List.partition 
    (fun tc' => in_dec thread_eqdec (info_tid (tc_rootinfo tc')) targets)
    new_chn in
  (Node ni new_chn', (List.concat res) ++ res').

(* return a reconstructed tree to be added into the pivot *)

Fixpoint tc_attach_nodes forest tc' : treeclock :=
  let: Node info_u' chn' := tc' in
  (* try finding a tree in the forest with the same root thread *)
  let: u_pre := List.find (fun tc => thread_eqdec (info_tid (tc_rootinfo tc)) (info_tid info_u')) forest in
  let: chn_u := (match u_pre with Some u => tc_rootchn u | None => nil end) in
  (* TODO app or rev_app? *)
  (* for u', inherit clk and aclk anyway; prepend all children of u' *)
  Node info_u' ((map (tc_attach_nodes forest) chn') ++ chn_u).

Definition tc_join tc tc' :=
  let: mkInfo z' clk_z' aclk_z' := tc_rootinfo tc' in
  if clk_z' <=? (tc_getclk tc z')
  then tc
  else 
    let: subtree_tc' := tc_get_updated_nodes_join tc tc' in
    let: targets := map info_tid (tc_flatten subtree_tc') in
    let: (pivot, forest) := tc_detach_nodes targets tc in
    let: Node (mkInfo w clk_w _) chn_w := tc_attach_nodes forest subtree_tc' in
    let: Node info_z chn_z := pivot in 
    Node info_z ((Node (mkInfo w clk_w (Some (info_clk info_z))) chn_w) :: chn_z).










(* Definition vector_clock := nat -> nat. *)

End TreeClock.


