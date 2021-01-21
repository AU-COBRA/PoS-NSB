Require Import Relations.
From mathcomp Require Import
     all_ssreflect.

From AUChain Require Import
     Blocks
     Parameters
     BlockTree
     MemEq
     SsrFacts
.

From mathcomp Require Import
     finmap.

Open Scope fmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *TreeChain 
    Basic facts about valid chains and trees. 
*)
Axiom GenesisSlot : sl GenesisBlock = 0. 
Axiom GenesisWin : Winner (bid GenesisBlock) (sl GenesisBlock). 

Lemma lt_slots_irr : irreflexive lt_slots. 
Proof. by move=> [] > /=; rewrite ltnn. Qed. 

Lemma lt_slots_trans : transitive lt_slots. 
Proof. by move=> [] ???? [] ???? [] ???? + H; apply/(ltn_trans H). Qed. 

Lemma valid_chain_block_gb b : reflect (b = GenesisBlock) (valid_chain [:: b]). 
Proof.
  apply/(iffP idP). 
  - by rewrite /valid_chain => //= /andP [] ? /andP [] /eqP -> _. 
  - by move->; rewrite /valid_chain /= /correct_block eq_refl GenesisWin. 
Qed.

Lemma valid_chain_cons c :  valid_chain c -> exists b c', b :: c' = c. 
Proof. by case: c=> //= b c _; exists b; exists c. Qed. 

Lemma valid_chain_ext b b' c :
  valid_chain (b :: b' :: c) =
  [&& correct_block b, linked b b', lt_slots b b' & valid_chain (b' :: c)].
Proof.
  rewrite /valid_chain /=.
  by do 2!case: (correct_block _);
    case: (linked _ _);
    case: (properly_linked);
    case: (correct_blocks _);
    case: (lt_slots _ _);
    case: (path _ _ _). 
Qed. 

Lemma valid_chain_short_l c1 b c2 :
  valid_chain (c1 ++ b :: c2) ->
  valid_chain (b :: c2).
Proof.
  elim: c1 => //= b' [] /= . 
  - by rewrite valid_chain_ext => _ /andP [] _ /andP [] _ /andP [] _.
  - move=> b'' c1 IH.
    by rewrite valid_chain_ext => /andP [] _ /andP [] _ /andP [] _ /IH. 
Qed.   

Lemma uniq_valid_chain c :
  valid_chain c -> uniq c. 
Proof.
  rewrite /valid_chain /= => /andP [] _ /andP [] _  /sorted_uniq -> //.
  - by apply/lt_slots_trans.
  - by apply/lt_slots_irr.
Qed. 
    
Lemma sorted_blocks_slots bs :
  sorted lt_slots bs = sorted gtn [seq sl b | b <- bs].
Proof. by case: bs=> //= + bs; elim: bs => //= b' bs -> b. Qed. 

Lemma best_chain_time {tT : treeType} (t : tT) s :
  {in bestChain s t, forall b, sl b <= s}. 
Proof. by move=> b/best_chain_in_all; rewrite mem_filter=> /andP []. Qed. 

Definition build_tree {tT : treeType} (bp : BlockPool ) : tT := foldr (fun b => extendTree^~ b) tree0  bp.

Lemma all_build {tT: treeType} : forall bp, (allBlocks (@build_tree tT bp)) =i GenesisBlock :: bp.
Proof.
  elim => [b |b bp IH b'] /=; first by rewrite /= all_tree0.
  rewrite inE. apply/esym. rewrite all_extend mem_cat IH inE orbC mem_seq1 inE.
  by do 2! case: (_ ==_); case: (_ \in _). 
Qed. 

Lemma build_tree0 T : @build_tree T [::] = tree0.
Proof. done. Qed. 

Lemma extend_build_composition T : forall b bp, extendTree (@build_tree T bp) b = @build_tree T (b :: bp).
Proof. done. Qed.

Lemma valid_chain_starts_gb c :
  valid_chain c -> exists bc, bc ++ [:: GenesisBlock] = c. 
Proof.
  move=> /andP [] _ /andP [] + _.
  elim: c=> //= b [_ /eqP ->| ?? IH /andP [] _ /IH [] c H].
  - by (exists [::]; rewrite cat0s).
  - by (exists (b :: c); rewrite -cat1s -catA H cat1s). 
Qed. 

Lemma best_chain_starts_gb {tT : treeType} (t : tT) sl :
  exists bc, bc ++ [:: GenesisBlock] = bestChain sl t . 
 Proof. by move: (best_chain_valid t sl) => /valid_chain_starts_gb. Qed. 


Lemma gb_in_all {tT: treeType} (t : tT) : GenesisBlock \in allBlocks t.
Proof. 
  move/(_ GenesisBlock): (@best_chain_in_all tT 0 t).
  apply: instant1; last by rewrite mem_filter => /andP [].  
  move: (@best_chain_starts_gb tT t 0)=> [] ? <-.
  by rewrite mem_cat orbC inE eq_refl.
Qed. 

Lemma allBlocks_build_cat {tT : treeType} bs1 bs2 :
  allBlocks (@build_tree tT (bs1 ++ bs2))
  =i (allBlocks (@build_tree tT bs1)) ++ (allBlocks (@build_tree tT bs2)). 
Proof.
  elim: bs1 => //= [| > IH /= b'].
  - move=> ?. rewrite mem_cat all_tree0 mem_seq1. case: (_ ==_)/eqP=> // ->.
    by rewrite gb_in_all /=.
  - rewrite all_extend. 
    apply/esym.
    rewrite mem_cat all_extend mem_cat orbA orbC -!orbA orbF orbA [(_ \in _) || _]orbC -mem_cat. 
    by rewrite -IH mem_cat mem_seq1. 
Qed. 
