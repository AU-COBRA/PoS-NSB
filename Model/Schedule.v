From mathcomp Require Import
     all_ssreflect
     finmap.

Require Import Relations.

From AUChain Require Import
     Network
     Protocol
     GlobalState
     Blocks
     Messages
     MessageTuple
     Parameters
     BlockTree
     LocalState
     StateMonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Schedule 
      This file contains the semantics for an execution of the protocol.
**)

Definition upd_local (p: Party) (l: LocalState) (N: GlobalState) : GlobalState :=
  N[[state_map := setf (state_map N) p l ]].

(** Handy functions for using the network functionality to broadcast
    several messages. **)
Definition flood_msgs (msgs : Messages) (N : GlobalState) : GlobalState :=
  foldr flood_msg N msgs.

Definition flood_msgs_adv (msgs : seq (Message * DelayMap)) (N : GlobalState) : GlobalState :=
  foldr (fun ' (m , ϕ) => flood_msg_adv m ϕ) N msgs.

(** Our development is parameterised by a map deciding the honesty of
    parties. **)
Parameter CorruptionStatus : Party -> Honesty.

(** The adversary is modelled as two functions: 
    1) Decides how the adversary acts when baking.
    2) Decides how the adversary acts when recieving 
       messages. *)
Parameter AdversarialBake:
  Slot ->
  History ->
  MessagePool ->
  State AdversarialState (seq (Message * DelayMap)).

Parameter AdversarialRcv:
  Messages ->
  Slot ->
  History ->
  MessagePool ->
  State AdversarialState (seq (Message * DelayMap)).

(** We translate the map of honesty a boolean value. **)
Definition is_corrupt p : bool := CorruptionStatus p == Corrupt.
Definition is_honest p : bool := CorruptionStatus p == Honest.

(** If the party is honest an honest step is taken with the correct
    messages. Otherwise will the [AdversarialStep] function be called with
    the correct inputs and the world updated accordingly to this.  **)
Definition party_bake_step_world (p : Party) (N : GlobalState) : GlobalState :=
  if (state_map N).[? p] is Some l
  then if ~~(is_corrupt p)
       then let '(n_msgs, new_ls) := honest_bake (t_now N) l
            in flood_msgs n_msgs (upd_local p new_ls N)
       else let '(n_msgs, adv_state') := AdversarialBake (t_now N) (history N) (msg_buff N) (adv_state N)
            in (flood_msgs_adv n_msgs N)[[adv_state := adv_state']]
  else N.

(** If the party is honest he calls the honest recieve functions.
    Otherwise the [AdversarialRcv] function.  **)
Definition party_rcv_step_world (p : Party) (N : GlobalState) : GlobalState :=
  if (state_map N).[? p] is Some l
  then let '(msgs, N') := fetch_msgs p N in
       if ~~(is_corrupt p)
       then let '(_, new_ls) := honest_rcv msgs (t_now N') l
            in (upd_local p new_ls N')
       else let '(n_msgs, adv_state') := AdversarialRcv msgs (t_now N') (history N') (msg_buff N') (adv_state N')
            in (flood_msgs_adv n_msgs N')[[adv_state := adv_state']]
  else N.

Definition inc_round (N : GlobalState) : GlobalState :=
  N[[t_now := S (t_now N)]].

(** ** Definition: Related states **)

Reserved Notation "A ⤳ B" (at level 80, no associativity).

Notation "N '@' p" := (progress N = p) (at level 20).

Inductive SingleStep: GlobalState -> GlobalState -> Prop :=
(* Delivering messages to all parties *)
| Deliver : forall N, N @ Ready -> N ⤳
                 (foldr party_rcv_step_world N (exec_order N))[[progress := Delivered]]
(* Executing all party concurrenctly *)
| Bake : forall N, N @ Delivered -> N ⤳
              (foldr party_bake_step_world N (exec_order N))[[progress := Baked]]
(* When messages are delivered and  *)
| NextRound : forall N, N @ Baked -> N ⤳ (inc_round (round_tick N))[[progress := Ready]]
(* Permuting parties leads to related states *)
| PermParties : forall N ps, perm_eq (exec_order N) ps -> N ⤳ N[[exec_order := ps]]
(* Permuting message buffer leads to related states  *)
| PermMsgs : forall N mb, perm_eq (msg_buff N) mb -> N ⤳ N[[msg_buff := mb]]
where "N ⤳ N'" := (SingleStep N N').

(** BigStep semantics are just the reflexive transitive closure of the
    SingleStep relation **)
Definition BigStep (N N' : GlobalState) := clos_refl_trans_n1 GlobalState SingleStep N N'.

Notation "N '⇓' N'" := (BigStep N N') (at level 20).
Notation "N '⇓[' s ']' N'" := (N ⇓ N' /\ (s + t_now N) = (t_now N')) (at level 20).
Notation "N '⇓^+' N'" := (N ⇓ N' /\ t_now N < t_now N') (at level 20).
