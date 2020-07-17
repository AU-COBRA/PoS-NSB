From mathcomp Require Import
     all_ssreflect.

From AUChain Require Import
     Parameters
     Blocks
     BlockTree.

From RecordUpdate Require Import RecordSet. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * LocalState
      This file defines the LocalState a party should maintain.  
      
**)
Record LocalState  :=
  mkLocalState
    { tT : treeType
      ; pk : Party
      ; tree : tT }.

Instance LocalStateSettable : Settable LocalState :=
  settable! mkLocalState <tT ; pk; tree>. 
