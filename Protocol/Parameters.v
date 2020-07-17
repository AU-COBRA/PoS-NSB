From mathcomp Require Import
     all_ssreflect.

(** * Paramters
    This file contains basic paramters for the protocol, as well as a few synononyms. 
**)

Parameter Hash : eqType.
Parameter Party : finType.

(* Type synononyms *)
Definition Slot := nat.
Definition SlotZero := 0.
Definition Delay := nat.
Definition Parties := seq Party.

(* List of initial parites *)
Parameter InitParties : Parties.

(* Lottery parameter *)
Parameter Winner: Party -> Slot -> bool.
