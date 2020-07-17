From mathcomp Require Import
     all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * StateMonad
      This file contains the standard definition of a state-monad. 

**)

Definition State (s a : Type) : Type := s -> (a * s).

Definition get  {s : Type} : State s s := fun i => (i, i).
Definition gets {s a : Type} (f : s -> a) : State s a := fun s => (f s, s).
Definition put  {s : Type} x : State s unit := fun _ => (tt, x).
Definition modify {s : Type} (f : s -> s) : State s unit := fun i => (tt, f i).
Definition pure {s a : Type} : a -> State s a := fun x st => (x, st). 

Definition bind {s a b : Type} (m1 : State s a) (f :(a -> State s b)) : State s b :=
  fun st => match m1 st with
         | (x, st') => f x st'
         end.

Arguments bind _ _/. 
Arguments pure _/. 

Notation "m >>= f" := (bind m f) (at level 43, left associativity).

Notation "X <- A ; B" := (A >>= (fun X => B)) (at level 81, right associativity, only parsing). 

Notation "A ;; B" := (A >>= (fun _ => B)) (at level 81, right associativity, only parsing).
 
  







