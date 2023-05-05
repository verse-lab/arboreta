From Coq Require Import List Bool Lia ssrbool PeanoNat Sorting RelationClasses.
From Coq Require ssreflect.
From distributedclocks.clocks Require Export treeclock.
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

(* FIXME: simply Import stdpp will result in mysterious extracted code. 
    Currently do not know why and there is no related report in Iris/stdpp/issues ...
    will investigate it later. For now, ignore this
*)
Extraction "extraction/lib/tcimpl.ml" tc_join tc_flatten tc_rootinfo.
