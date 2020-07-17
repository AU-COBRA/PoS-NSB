From mathcomp Require Import
     all_ssreflect.

From AUChain Require Import
     Messages
     Parameters.

From RecordUpdate Require Import RecordSet. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * MessageTuple 
    This file contains the wrapper around messages used
    by the network functionality.  
**)

Record MessageTuple :=
  mkMessageTuple
    { msg : Message
    ; rcv : Party
    ; cd : Delay }.

Instance MessageTupleSettable : Settable MessageTuple :=
  settable! mkMessageTuple <msg; rcv; cd>. 

Definition MessagePool := seq MessageTuple.

Module MessageTupleEq.

Definition eq_msg_tuple a b :=
  [&& msg a == msg b
   , rcv a == rcv b
   & cd a  == cd b ].

Lemma eq_msg_tupleP : Equality.axiom eq_msg_tuple.
Proof.
  case => ???; case => ???. rewrite /eq_msg_tuple /=.
  do ! (case: _ /eqP; [move => -> |by constructor; case]).
  by constructor.
Qed.

Canonical MessageTuple_eqMixin := Eval hnf in EqMixin eq_msg_tupleP.
Canonical MessageTuple_eqType := Eval hnf in EqType MessageTuple MessageTuple_eqMixin.

End MessageTupleEq.
Export MessageTupleEq.
