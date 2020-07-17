From mathcomp Require Import
     all_ssreflect.

From AUChain Require Import
     Parameters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Blocks
    This file contain the basic record representing a block. 
**)
Record Block :=
  MkBlock
    { sl : Slot
    ; pred : Hash
    ; bid : Party }.

(* Type synononym for blocks *)
Definition Chain := seq Block.
Definition Chains := seq Chain.
Definition BlockPool := seq Block.

(* Decidable equality for Blocks *)
Definition eq_block (b b' : Block) :=
  match b, b' with
  | MkBlock sl pt bid, MkBlock sl' pt' bid' =>
    [&& sl == sl', pt == pt' & bid == bid']
  end.

Lemma eq_blockP : Equality.axiom eq_block.
Proof.
  case => sl pt bid; case => sl' pt' bid' .
  rewrite /eq_block.
  do ! (case: _ /eqP; [move => -> |by constructor; case]).
  by constructor.
Qed.

(* Canonial structures for block *)
Canonical Block_eqMixin := Eval hnf in EqMixin eq_blockP.
Canonical Block_eqType := Eval hnf in EqType Block Block_eqMixin.

(** Parameters for block *)
Parameter GenesisBlock : Block.
Parameter HashB : Block -> Hash.
