From mathcomp Require Import
     all_ssreflect.

From AUChain
     Require Import
     BlockTree
     Blocks
     Messages
     Parameters
     LocalState
     StateMonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Protocol
      Execution plan for each party pr. round:
      This consists of two parts:

      1) Recieve and process messages:
         - Recieve messages for this party and extend the blocktree with the
           received blocks.
  
      2) Execute consensus algorithm:
         - Check if leader.
         - If leader then bake block and add return messages that has to be submitted.
 **)

Section Protocol.

  Definition extend_tree_l (l: LocalState) (b : Block) : LocalState  :=
    mkLocalState (pk l) (extendTree (tree l) b). 

  Definition process_msg (m: Message) (l: LocalState) : LocalState :=
    let: BlockMsg b := m in extend_tree_l l b. 

  Definition process_msgs (msgs: Messages) : State LocalState unit :=
    modify (fun l => foldr process_msg l msgs).

  (* Notice that if a party actually bakes a block it will be added
     directly to the blocktree of this party. *)
  Definition honest_bake (sl : Slot) (txs : Transactions) : State LocalState Messages :=
    local_state <- get;
    if Winner (pk local_state) sl
    then let: bestChain := bestChain (sl-1) (tree local_state) in
         let: hashPrev := HashB (head GenesisBlock bestChain) in
         let: newBlock := MkBlock sl txs hashPrev (pk local_state) in
         modify (fun l => extend_tree_l l newBlock);;
         pure [:: BlockMsg newBlock]
    else pure [::].

  Definition honest_rcv (msgs : Messages) (sl : Slot) : State LocalState unit :=
    process_msgs msgs.

End Protocol.
