From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Setoid. 
Require Import Morphisms.

(* Mem  *)
Instance eq_mem_equivalence T : Equivalence (@eq_mem T).
Proof. constructor; by [| move=> ?? + ?; move-> | move=> ??? ++ ?; move=> ->-> ]. Qed.

(* Transtitive *)
Lemma eq_mem_trans: forall (T : eqType) (a b c : seq T), 
    a =i b -> b =i c -> a =i c.
Proof. by move=> > ->. Qed. 

(* Symmetric *)
Lemma eq_mem_sym: forall (T : eqType) (a b : seq T),
    a =i b -> b =i a.
Proof. by move=> > ->. Qed. 

(* Reflexive *)
Lemma eq_mem_refl: forall (T : eqType) (a : seq T),
    a =i a. 
Proof. done. Qed. 

Definition mem_eq (T : eqType) (a b : seq T) := a =i b. 

Instance eq_mem_equivalence' T : Equivalence (@mem_eq T).
Proof. constructor; by [| move=> ?? + ?; move-> | move=> ??? ++ ?; move=> ->-> ]. Qed.

Instance cat_proper_mem_eq T : Proper ((@mem_eq T) ==> (@mem_eq T) ==> (@mem_eq T)) cat. 
Proof.
  move=> >//=. rewrite/mem_eq /(_ ==> _)%signature. 
  move=> H > H' c. rewrite 2!mem_cat. move: (H c) (H' c).
  by do 2!case: (_ \in _). 
Qed. 

Goal forall (T : eqType) (a a' b b' : seq T), a =i a' -> b =i b' -> a ++ b =i a' ++ b'. 
Proof. by move=> >; rewrite -3!/(mem_eq _ _) => -> ->. Qed. 


  
