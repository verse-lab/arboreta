From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
From arboreta.clocks Require Export treeclock degenerated_treeclock.
Import ssreflect.SsrSyntax.

From Coq Require Import Extraction.
Extraction Language OCaml.

Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant is_left => "(fun x -> x)".
Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ].
Extract Constant PeanoNat.Nat.leb => "( <= )".
Extract Constant PeanoNat.Nat.add => "( + )".

(* FIXME: simply Import stdpp will result in mysterious extracted code. 
    Currently do not know why and there is no related report in Iris/stdpp/issues ...
    will investigate it later. For now, ignore this
*)
Extraction "extraction/lib/tcimpl.ml" tc_flatten tc_rootinfo tc_init tc_incr
  tc_eraseaclk tc_join tc_join_degen.
