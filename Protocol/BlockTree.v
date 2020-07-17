From mathcomp Require Import
     all_ssreflect.

From AUChain Require Import
     Parameters
     Blocks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
 * Block Tree.
   This file contains the definition of a treeType, which is the type of a blocktree. 
   First, the [valid_chain] predicate is defined and afterwards is the treeType defined. 
**)

(* Convenient notaiton for length of a list *)
Notation "'|' s '|'" := (size s) (at level 20).

Definition correct_block (b : Block) :=
  Winner (bid b) (sl b). 

Arguments correct_block !b /. 

Definition correct_blocks (c : Chain) : bool := all correct_block c. 

Definition linked (b b' : Block) := pred b == HashB b'.

Arguments linked !b _ /. 

Fixpoint properly_linked (c : Chain) : bool :=
  match c with
  | [::] => false
  | b :: bs => match bs with
             | [::] => b == GenesisBlock
             | b' :: bs' => (linked b b') && (properly_linked bs)
             end
  end.

Arguments properly_linked !_ : simpl nomatch. 

Definition lt_slots b b' := sl b > sl b'. 

Arguments lt_slots !b _ /. 

Definition decreasing_slots c := sorted lt_slots c. 

Arguments decreasing_slots _ /. 

Definition valid_chain c := [&& correct_blocks c, properly_linked c & decreasing_slots c]. 

Arguments valid_chain c : simpl nomatch. 

Notation "c '✓'" := (valid_chain c) (at level 20).

(** Interface of the BlockTree **)
Module BlockTree.
  Section BlockTreeDef.

  Record mixin_of T :=
    Mixin { extendTree : T -> Block -> T
        (* ; buildTree : BlockPool -> T *)
          ; bestChain : Slot -> T -> Chain
          ; allBlocks: T -> BlockPool
          ; tree0 : T

          (** All blocks contains correct blocks **)
          (* ; _ : forall bp, (allBlocks (buildTree bp)) =i bp *)
          ; _ : allBlocks tree0 =i [:: GenesisBlock] 
          ; _ : forall t b, allBlocks (extendTree t b) =i allBlocks t ++ [:: b]

          (* (** Building nothing gives the empty tree **) *)
          (* ; _ : buildTree [::] = tree0 *)

          (* (** Composition of build and extend **) *)
          (* ; _ : forall b bp, extendTree (buildTree bp) b = buildTree (b :: bp) *)

          (** Selecting best chain **)
          ; _ : forall t s, valid_chain (bestChain s t)
          ; _ : forall c s t, valid_chain c -> {subset c <= [seq b <- allBlocks t | sl b <= s]} -> |c| <= |bestChain s t|
          ; _ : forall s t, {subset (bestChain s t) <= [seq b <- allBlocks t | sl b <= s]}
      }.

  Notation class_of := mixin_of.
  Record type := Pack { sort : Type; class : class_of sort }.

  End BlockTreeDef.

  Module Exports.

    Coercion sort : type >-> Sortclass.
    Notation treeType := type.
    Notation BlockTreeMixin := Mixin.
    Notation TreeType T m := (@Pack T m).

    Section BlockTreeAcc.

      Implicit Type (T : treeType).

      Definition extendTree {T} := extendTree (class T).
      Definition bestChain {T} := bestChain (class T).
      Definition allBlocks {T} := allBlocks (class T).
      Definition tree0 {T} := tree0 (class T).

      Lemma all_tree0 T : @allBlocks T tree0  =i [:: GenesisBlock].
      Proof. by case: T => ? []. Qed.

      Lemma all_extend T : forall t b, @allBlocks T (extendTree t b) =i allBlocks t ++ [:: b].
      Proof. by case: T => ? []. Qed.

      Lemma best_chain_valid T : forall t s, valid_chain (@bestChain T s t). 
      Proof. by case: T => ? []. Qed.

      Lemma best_chain_best T : forall c s t, valid_chain c -> {subset c <= [seq b <- allBlocks t | sl b <= s]} -> |c| <= |@bestChain T s t|. 
      Proof. by case: T => ? []. Qed.

      Lemma best_chain_in_all T : forall s t, {subset (bestChain s t) <= [seq b <- @allBlocks T t | sl b <= s]}.
      Proof. by case: T => ? []. Qed.

    End BlockTreeAcc.
  End Exports.
End BlockTree.

Export BlockTree.Exports.
