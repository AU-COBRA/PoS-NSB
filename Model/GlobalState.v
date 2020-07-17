From mathcomp Require Import
     all_ssreflect
     finmap.

From AUChain Require Import
     Parameters
     Blocks
     Messages
     MessageTuple
     BlockTree
     LocalState.

From RecordUpdate Require Import RecordSet. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Globalstate 
      This file contains the definition of a global state
      together, as well as definitions for some types used in the
      definition of [GlobalState].  
**)

(** The StateMap which is supposed to keep track of parties.
    The parties are existentially quantified over their treeType. *)

Definition StateMap := finMap [choiceType of Party] LocalState.

Definition state_map0 : StateMap := fmap0.
Open Scope fmap.

Inductive Honesty : Set :=
| Honest
| Corrupt.

Definition bool_of_honesty (h : Honesty) :=
  match h with
  | Honest => true
  | Corrupt => false
  end.

Coercion bool_of_honesty: Honesty >-> bool.

Definition honest_eq h h' :=
  match h, h' with
  | Honest, Honest => true
  | Corrupt, Corrupt => true
  | _, _ => false
  end.

Lemma honest_eqP : Equality.axiom honest_eq.
Proof. by move=> [] []; apply/(iffP idP). Qed. 

Canonical Honest_eqMixin := Eval hnf in EqMixin honest_eqP.
Canonical Honesty_eqType := Eval hnf in EqType Honesty Honest_eqMixin.

Inductive Progress : Set :=
| Ready
| Delivered
| Baked.

Definition progress_eq p p' :=
  match p, p' with
  | Ready, Ready => true
  | Delivered, Delivered => true
  | Baked, Baked => true
  | _, _ => false
  end.

Lemma progress_eqP : Equality.axiom progress_eq.
Proof. by move=> [] []; apply/(iffP idP). Qed. 

Canonical Progress_eqMixin := Eval hnf in EqMixin progress_eqP.
Canonical Progress_eqType := Eval hnf in EqType Progress Progress_eqMixin.

Parameter AdversarialState : Type.
Parameter AdvState0 : AdversarialState.

Definition History := seq Message. 

(** ** The GlobalState  *)
Record GlobalState :=
  mkGlobalState {
    (* The current slot of the world  *)
    t_now : Slot;
    (* All messages that yet has to be delivered *)
    msg_buff : MessagePool;
    (* A map of each party's local state *)
    state_map : StateMap;
    (* A global blockpool containing all blocks seen in thte world *)
    history : History;
    (* An adversary can update his state *)
    adv_state : AdversarialState ;
    (* Execution order for the next round*)
    exec_order : Parties ;
    (* A world state describing how far the world has progressed in this round *)
    progress : Progress
}.

Instance GlobalStateSettable : Settable GlobalState :=
  settable! mkGlobalState <t_now; msg_buff; state_map; history; adv_state; exec_order; progress>. 

Definition tree_gb (tT : treeType) : tT := tree0.

Definition history0 : Messages := [::].

Definition msg_id0 := 0.

Parameter TreeTypeMap : Party -> treeType. 

(** Creates a new party with identifier pk. Is not set to new as this is
    only to be used for the initial creations of parties where everybody
    are new, but none should act as such. *)

Definition init_local (pk : Party): LocalState :=
  mkLocalState pk (tree_gb (TreeTypeMap pk)).

Definition N0 : GlobalState :=
  let state_map := foldr (fun pk acc => acc.[pk <- init_local pk]) state_map0 InitParties in
  mkGlobalState 1 [::] state_map history0 AdvState0 InitParties Ready.
