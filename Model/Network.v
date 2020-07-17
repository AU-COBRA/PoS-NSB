From mathcomp Require Import all_ssreflect.

From AUChain Require Import
     GlobalState
     Messages
     MessageTuple
     Parameters.

From mathcomp Require Import finmap.

From RecordUpdate Require Import RecordSet. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Network 
      This file contains the basic operation for the synchronous network. 
**)

(* Notation for record update *)

Notation "x [[ proj  :=  v ]]" := (set proj (fun _ => v) x)
                                    (at level 12, left associativity). 

Notation "x [ proj  ::=  f ]" := (set proj f x)
                                     (at level 12, f at next level, left associativity).

(** Honest send of messages *)
Definition flood_msg (m : Message) (N : GlobalState) : GlobalState :=
  let: newMessages := [seq mkMessageTuple m r 1 | r <- exec_order N] in
  N[[msg_buff := newMessages ++ (msg_buff N)]][[history := m :: (history N)]].

(** Adversarial send of messages An adversary can for each of the
    messages choose to have them delivered in round t+1 or t+2.  *)
Definition Delay : Type := seq_sub [:: 1 ; 2].

Definition nat_of_delay (d : Delay) : nat.
  case d=> n; case: (n == 1)=> _; [exact 1| exact 2].
Defined.

Coercion nat_of_delay : Delay >-> nat.
Definition DelayMap := Party -> Delay.

Lemma delay12 (d : Delay): (d : nat) = 1 \/ (d : nat) = 2.
Proof. case d=> //= n. rewrite mem_seq2. case (_ == _) => //= _; by [constructor |constructor 2]. Qed.

Definition flood_msg_adv (m : Message) (ϕ : DelayMap) (N : GlobalState)  : GlobalState :=
  let: newMessages := [seq mkMessageTuple m r (ϕ(r)) | r <- exec_order N] in
  N[[msg_buff := newMessages ++ (msg_buff N)]][[history := m :: (history N)]].

(** Fetching of messages for a party *)
Definition collect_zero_pairs (r : Party) (N : GlobalState) : MessagePool :=
  [seq mt <- (msg_buff N) | (cd mt == 0) && (rcv mt == r)].

Definition rmv_zero_msgs (r : Party ) (N : GlobalState) : GlobalState :=
  N[[msg_buff := [seq mt <- (msg_buff N) | ~~ ((cd mt == 0) && (rcv mt == r))] ]].

Definition fetch_msgs (r : Party) (N : GlobalState): (seq Message * GlobalState) :=
  ([seq msg mt | mt <- collect_zero_pairs r N], rmv_zero_msgs r N).

(** Round tick *)
Definition round_tick (N : GlobalState) : GlobalState :=
  N[[msg_buff := [seq m[[cd := (cd m) - 1]] | m <- msg_buff N] ]].
