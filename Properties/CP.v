From mathcomp Require Import
     all_ssreflect
     finmap.

From AUChain Require Import
     Network
     Protocol
     GlobalState
     Blocks
     Messages
     MessageTuple
     Parameters
     BlockTree
     Schedule
     LocalState
     MemEq
     SsrFacts
     TreeChain
     CG
     CQ
.

From Equations Require Import Equations.
Set Equations Transparent.

Open Scope fmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Common Prefix
      This file contains the proof of common prefix property. 
 **)

(** First, some preliminary definitions that is needed to define common prefix. **)

(** ** Super slots. 
    Slots where there are a unique honest winner. It
    is important that these are unique as this is what makes their
    position in the chains be disjoint. **)
Definition super_slot sl : bool :=
  count (fun p => Winner p sl && is_honest p) InitParties == 1. 

Definition super_slots_range a b :=
  p_slots_range super_slot a b.

Arguments super_slots_range _ _ /.

Definition super_block b : bool :=
  is_honest (bid b) && super_slot (sl b). 

Arguments super_block _ /.

Definition super_blocks_world N :=
  undup [seq b <- block_history N | super_block b]. 

Arguments super_blocks_world _ /.

Definition super_blocks_world_range n m N :=
  [seq b <- super_blocks_world N | n <= sl b < m]. 

Arguments super_blocks_world_range _ _ _ /.

Lemma empty_range a b : b <= a -> nat_range a b = [::]. 
Proof.
  move=> ?. apply/size0nil.
  by rewrite size_iota; apply/eqP. 
Qed. 

Lemma filter_range_split_blocks c x y z  :
  x <= y <= z -> 
  perm_eq [ seq b <- c |x <= sl b < z]
          ([ seq b <- c | x <= sl b < y] ++ [seq b <- c | y <= sl b < z]). 
Proof.
  move/andP => [] H1 H2.
  elim: c=> //= b bs IH.
  case l1: (_ <= _) => //=; case l2: (_<_)=> //=. 
  - rewrite andbC /=. case l3: (_ < _)=> //=; case l4: (_<=_)=> //=.
    + by move: (ltn_leq_trans l3 l4); rewrite ltnn.
    + by rewrite perm_cons. 
    + by rewrite perm_sym -cat1s perm_catCA cat1s perm_sym perm_cons. 
    + by move: l4; rewrite leqNgt l3. 
  - case l3: (_ < _)=> //=; case l4: (_<=_)=> //=.
    + by move: (ltn_leq_trans l3 H2); rewrite l2.
    + by move: (ltn_leq_trans l3 H2); rewrite l2.
  - by case l4: (_<=_)=> //=; move: (leq_trans H1 l4); rewrite l1.
  - by rewrite andbC. 
Qed. 

Lemma all_parties_state N : N0 ⇓ N -> all (exists_state^~N) (exec_order N).
Proof.
  move=> N0N. 
  rewrite (@eq_all_r _ _ InitParties); last first.
  { apply/perm_mem. rewrite perm_sym. 
      by apply/perm_exec_order0. }
  by apply/allP=> p; rewrite has_state_initP. 
Qed. 

Lemma block_history_adv_broadcast_subset N ms :
  {subset block_history N <= block_history (flood_msgs_adv ms N)}. 
Proof. by elim: ms=> //= [] [] > //= IH; apply/(subset_trans IH)/subset_cons. Qed. 

Lemma one_super_block N :
  N0 ⇓ N -> forging_free N -> N @ Baked -> 
  | super_blocks_world_range (t_now N) ((t_now N).+1) N | = super_slot (t_now N). 
Proof.
  elim=> // y z [] // {y z} N.
  (* Baking *)
  { move=> prog_N N0N _ ff _ /=. set N' := foldr _ _ _.
    rewrite -filter_undup size_filter count_filter.
    rewrite !baking_preserves_time. set P := predI _ _.
    pose P' := (fun b  =>
                  [&& (sl b == t_now N)
                   , is_honest (bid b)
                     & (count
                          (fun p => Winner p (t_now N) && is_honest p)
                          (exec_order N) == 1)]). 
    have: P =1 P'. 
    { move=> b. rewrite /P' /= /super_slot.
      move/permP: (perm_exec_order0 N0N) ->.
      rewrite ltnS -eqn_leq eq_sym. 
        by case: (_==_)/eqP => [->|] //. }
    move/eq_count -> => {P}. 
    rewrite /N' /super_slot=> {N'} .
    move/permP: (perm_exec_order0 N0N) ->. rewrite /P'.
    move: ff. set N2 := _[[_ := _]]. move=> ff. 
    move/ProgressB: (baking_steps_refl N2) (all_parties_state N0N) (uniq_exec_order N0N).  
    elim: exec_order=> //= [| p ps]. 
    (** BC *)
    - rewrite (@eq_count _ _  pred0); [by rewrite count_pred0|].
        by move=> b; rewrite andbA andbC. 
    - set N' := foldr _ _ _. move=> IH. 
      move/BakeStep=> bake /andP [] e_p state_ps /andP [] pnotps ups.
      move: (IH bake state_ps ups) => {} IH.
      case n: (_&&_)=> //=; last first.
      (** First guy is not honest winner. *)
      { rewrite add0n -IH /party_bake_step_world.
        case state_p: (_.[?_])=> [l|] //=. case honest_p: (~~_)=> //=.
        - rewrite /honest_bake /=. move: state_p honest_p n=> /(bakes_preserves_pk N0N) ->. 
            by rewrite honest_not_corrupt andbC baking_preserves_time=> -> /= ->.
        - case: ff => _ /(_ _ bake) /=. 
          rewrite baking_preserves_time -/N'.
          case: AdversarialBake=> //= nbs _. 
          elim: nbs => //= [] [] b ?? IH' /=.
          case honest_b: is_honest => //= subset; case bin: (_ \in _) => //=.
          + by apply/IH'/(subset_trans _ subset)/subset_cons.
          + move: subset bin=> /(_ (get_block b)).
            rewrite mem_head -/(block_history _) mem_filter=> /trueI /andP [] _ H.
              by rewrite block_history_adv_broadcast_subset. 
          + by apply/IH'/(subset_trans _ subset). 
          + rewrite honest_b andbC /= add0n.
              by apply/IH'/(subset_trans _ subset). }
      (** First guy is honest winner. *)
      { case eq : (count _ ps)=> [|n' ]; last first. 
        { rewrite add1n //=.
          rewrite (@eq_count _ _  pred0); [by rewrite count_pred0|].
            by move=> b; rewrite andbA andbC. }
        { rewrite addn0 //= eq_refl.
          rewrite /party_bake_step_world.
          move: e_p. rewrite (@exists_state_bakes p ps) -/N'=> /exists_stateP [] l.
          rewrite /has_state=> state_p.
          move/andP: n=> [] win_p honest_p.
          rewrite state_p -honest_not_corrupt honest_p /honest_bake /=.
          move: state_p=> /(bakes_preserves_pk N0N) ->.
          rewrite baking_preserves_time win_p //=. set nb := MkBlock _ _ _.
          have: count (fun b : Block => [&& sl b == t_now N, is_honest (bid b) & true]) (undup [seq get_block m | m <- history N']) = 0. 
          { move/eqP: eq bake. rewrite all_count0. 
            rewrite /N'=> {N' IH state_ps pnotps ups}.
            have ffN : forging_free N.
            { apply/(forging_free_prev _ ff).
              by do 2! econstructor. }
            elim: ps=> //=. 
            - move=>_ _. move: (no_premature_honest_blocks_D N0N ffN prog_N)=> /=.
              rewrite -/(block_history _).
              elim: block_history=> //= > IH.
              case honest: is_honest=> //=; case ins: (_\in _)=> //=.
              + by move/andP=> [] _ /IH. 
              + by move=>/andP [] + /IH ->; case: (_==_)/eqP=> [->|] //=; rewrite ltnn. 
              + by move/IH ->; rewrite honest andbC. 
            - move=> p' ps IH /andP []. set N' := foldr _ _ _.  
              rewrite negb_and=> //= H /IH {} IH /BakeStep bake.
              move: (IH bake)=> {} IH. 
              rewrite /party_bake_step_world.
              case state_p': (_.[?_])=> [l'|] //=.
              rewrite -honest_not_corrupt. move: H; rewrite orbC.
              case: is_honest=> //=.
              + rewrite /honest_bake /=. rewrite baking_preserves_time.
                move: state_p'=> /(bakes_preserves_pk N0N) ->. 
                  by case Winner=> //=. 
              + case: ff => _ /(_ _ bake) /=. rewrite -/N'.
                case: AdversarialBake=> //= nms _ + _.
                elim: nms=> //= [] [] n ?? {} IH //= . 
                case honest_b: is_honest => //= subset; case bin: (_ \in _) => //=.
              + by apply/IH/(subset_trans _ subset)/subset_cons.
              + move: subset bin=> /(_ (get_block n)).
                rewrite mem_head -/(block_history _) mem_filter=> /trueI /andP [] _ H.
                  by rewrite block_history_adv_broadcast_subset. 
              + by apply/IH/(subset_trans _ subset). 
              + rewrite honest_b andbC /= add0n.
                  by apply/IH/(subset_trans _ subset). }
          case nbin: (_\in _)=> //=. 
          - move: nbin. elim: [seq _ | _ <- _] => //= > IH'.
            rewrite inE=> /orP [/eqP <-|]. case H: (_ \in _) => //=.
            + by rewrite eq_refl honest_p /= add1n. 
            + move/IH'=> {} IH'. case: (_ \in _)=> //=. 
              case: (_==_)=> //=. by case: is_honest=> //=. 
          - by move->; rewrite addn0 eq_refl honest_p. }
      }}
  (* Permutations *)
  { move=> ps perm N0N IH ff ?. apply/IH => //.
    apply/(forging_free_prev _ ff). by do 2! econstructor. }
  { move=> ps perm N0N IH ff ?. apply/IH=> //.
    apply/(forging_free_prev _ ff). by do 2! econstructor. }    
Qed. 


Lemma super_slots_blocks n m N :
  N0 ⇓ N ->
  forging_free N -> 
  0 < n ->
  m <= t_now N -> 
 |super_slots_range n m| = |super_blocks_world_range n m N|.
Proof.
  move: n m=> + + N0N. 
  elim: N0N=> // [n m ff gtn leqm|].
  (** BC *)
  { apply/eqP. rewrite size_eq0. apply/eqP.
    rewrite /p_slots_range /nat_range.
      by move: gtn leqm; case: n=> //= n; case: m => //= [] [] //=. }
  (** IH *)
  move=> y z [] // {y z} N. 
  - move=> prog_N N0N IH n m ffN gtn. rewrite delivery_preserves_time=> leqm.
    move: IH -> => //; last first.
    { apply/(forging_free_prev _ ffN).
      by do 2! econstructor. }
    apply/esym=> /=.
    rewrite 2!filter_undup. apply/eqP.
    rewrite -uniq_size_uniq; try by apply/undup_uniq. 
    rewrite 2!mem_undup. move=> b.
    rewrite 2!mem_filter. case: (_ <= _ < _) => //=.
    rewrite 2!mem_filter -andbA andbC. apply/esym.
    rewrite -andbA andbC. case: super_slot=> //=.
    rewrite andbC. apply/esym. rewrite andbC. 
    rewrite -2!(@mem_filter _ (fun b => is_honest (bid b))). 
    by apply/delivery_preserves_honest_block_hist. 
  - move=> prog_N N0N IH n m ffN gtn. 
    rewrite baking_preserves_time=> leqm.
    set N' := _[[_ := _]].
    rewrite IH //; last first.
    { apply/(forging_free_prev _ ffN).
      by do 2! econstructor. }
    rewrite /= 2!filter_undup.
    apply/eqP. 
    rewrite -uniq_size_uniq; try by apply/undup_uniq. 
    rewrite 2!mem_undup. 
    move=> b. rewrite 2!mem_filter. 
    case tb: (_ <= _ < _) => //=.
    rewrite 2!mem_filter -andbA andbC. apply/esym.
    rewrite -andbA andbC. case: super_slot=> //=.
    rewrite andbC. apply/esym. rewrite andbC. 
    rewrite -2!(@mem_filter _ (fun b => is_honest (bid b))).
    have NN': N ⇓ N'. 
    econstructor 2. constructor; try done.
    constructor.
    move: (honest_blocks_below_slot_preserved N0N NN' ffN b).
    rewrite 2!(mem_filter (fun b => sl b < t_now N)).
      by move/andP: tb => [] H1 H2; move: (ltn_leq_trans H2 leqm) -> => //=. 
  - move=> prog_N N0N IH n m ffN gtn. move: gtn => /IH {} IH //=.
    rewrite leq_eqVlt=> /orP []; last first. 
    { rewrite ltnS=> /IH <- //.
      apply/(forging_free_prev _ ffN).
      by do 2! econstructor. }
    move/eqP ->. 
    case n_now: (n <= t_now N) => //=; last first. 
    { rewrite /p_slots_range empty_range //=.
      - apply/esym/eqP. rewrite size_eq0. 
        elim: (undup _) => //= > IH'.
        case H1: (_ <= _) => //=. 
        case H2: (_ <= _) => //=.
        move: H2. rewrite ltnS=> H2. move: (leq_trans H1 H2).
        by rewrite n_now. 
      - by rewrite ltnNge n_now. } 
    rewrite (@p_slots_range_split _ _ (t_now N)); last first.
    { by apply/andP; constructor. }
    rewrite size_cat IH //; last first. 
    { apply/(forging_free_prev _ ffN).
      by do 2! econstructor. }
    apply/esym=> /=. set s := undup _.
    have: n <= t_now N <= (t_now N).+1. 
    { by apply/andP; constructor. }
    move/filter_range_split_blocks. move/(_ s)/perm_size ->. 
    rewrite size_cat. rewrite addnC. set s' := |_|. 
    apply/esym. rewrite addnC. set s'' := |_|.
    suff ->: s' = s'' by done. 
    rewrite /s' /s'' /s /p_slots_range /nat_range /=. 
    rewrite -addn1 -addnBAC // subnn add0n /=. 
    rewrite -/(super_blocks_world_range _ _ _) addn1. 
    rewrite one_super_block //; first by case: super_slot.
    apply/(forging_free_prev _ ffN).
      by do 2!econstructor. 
  - move=> ? perm N0 IH ?? ff ?? /=.
    apply/IH=> //. apply/(forging_free_prev _ ff).
    by do 2!econstructor. 
  - move=> ? perm N0 IH ?? ff ?? /=.
    apply/IH=> //. apply/(forging_free_prev _ ff).
    by do 2!econstructor. 
Qed. 

Lemma suffix_gb_vc c :
  valid_chain c ->
  [:: GenesisBlock] ⪯ c. 
Proof. by move/valid_chain_starts_gb => [] ? <-; rewrite suffix_catl. Qed. 

Lemma suffix_gb_lcs_vcs c1 c2 :
  valid_chain c1 ->
  valid_chain c2 ->
  [:: GenesisBlock] ⪯ lcs c1 c2. 
Proof. by rewrite -lcsP=> /suffix_gb_vc -> /suffix_gb_vc ->. Qed. 

(** Solution for remembering hypothesis is borrowed from
    https://github.com/mattam82/Coq-Equations/issues/232. *)

Notation "( a ; b )" := (exist _ a b).
Definition inspect {Y} (x : Y) : {y | x = y}.
Proof. by exists x. Qed.

(** New defintiion where all equal blocks are removed from the recursive call.  *)
Equations? cfb (b : Block) (bp : seq Block) : Chain by wf (size bp) lt:=
  cfb b bp with b == GenesisBlock => {
  | true := [:: b];
  | false with (Blocks.pred b == HashB GenesisBlock) => {
    | true => [:: b; GenesisBlock];
    | false with inspect (findo (fun b' => Blocks.pred b == HashB b') bp) => {
      | (Some b';H) with cfb b' [seq x <- bp | predC1 b' x] => {
        | [::] => [::];
        | b'' :: cs => b :: b'' :: cs
        };
      | (None;H) => [::]
      }
    }
  }. 
Proof. 
  apply/ltP. move/esym/findo_mem: H. clear.
  elim: bp=> //= > IH. rewrite inE=> /orP [/eqP ->|].
  - by rewrite eq_refl size_filter; apply/(leq_ltn_trans (count_size _ _)). 
  - by move/IH=> {}IH; case: (_==_)=>//=; apply/(ltn_trans IH).
Qed. 


Lemma progress_no_effect_history p N : 
  block_history N = block_history (N[[progress := p]]).
Proof. done. Qed. 

Definition pos (b : Block) (N : GlobalState) : nat := |cfb b (block_history N)|.

Arguments pos _ _/. 

Lemma progress_no_effect_pos p N b: 
  pos b N = pos b (N[[progress := p]]).
Proof. done. Qed. 

Lemma cfb_subset b bp :
  {subset cfb b bp <= GenesisBlock :: b :: bp}. 
Proof. 
  move=> b'.
  funelim (cfb b bp); try by rewrite -Heqcall. 
  - rewrite -Heqcall inE inE orbC => /eqP ->.
      by rewrite mem_head.
  - rewrite -Heqcall. rewrite inE=> /orP [/eqP ->|].
    + by rewrite inE orbC mem_head. 
    + by rewrite inE=> /eqP ->; rewrite mem_head. 
  - rewrite -Heqcall inE -Heq => /orP [/eqP ->| /Hind].
    + by rewrite inE mem_head orbC. 
    + rewrite 2!inE=> /or3P  [/eqP ->| |]; [by rewrite mem_head| |]. 
      * move: (e) => + H. move/eqP: H <- => /esym/findo_mem.
        by rewrite inE orbC inE -orbA orbC => ->. 
      * by move/filter_subset/(subset_cons b)/(subset_cons GenesisBlock). 
Qed. 

Lemma cfb_non_empty_starts_block b bp : cfb b bp != [::] -> exists c, cfb b bp = b :: c. 
Proof.
  funelim (cfb b bp).
  - move=> _. exists [::]. by apply/esym.
  - move=> _. exists [:: GenesisBlock]. by apply/esym.
  - by rewrite Heqcall eq_refl. 
  - by rewrite Heqcall eq_refl. 
  - rewrite -Heqcall=> _. by exists [:: b1 & l]. 
Qed. 

Lemma perm_cfb b : forall bp bp1,
    {in bp1 &, injective HashB} -> 
    perm_eq bp bp1 -> cfb b bp = cfb b bp1. 
Proof.
  move=> bp1. 
  funelim (cfb b bp1); move=> bp2.
  - by move/eqP: Heq ->; simp cfb ;rewrite eq_refl.  
  - by simp cfb; rewrite Heq0 /= Heq //. 
  - move=> _ /(perm_findo (fun b' : Block => Blocks.pred b == HashB b')).
    rewrite e -Heqcall. simp cfb. rewrite Heq1 /= Heq0 /=.
    case: inspect=> bo. case bo=> //= ? H.
    by rewrite H. 
  - move=> no_coll perm. rewrite -Heqcall.
    have: findo (fun b' : Block => Blocks.pred b == HashB b') bp2 = Some b0.
    { move: (perm_findo (fun b' : Block => Blocks.pred b == HashB b') perm). 
      rewrite e. case f: findo=> [b'|]//= _.
      move/findo_pred: (f). move/findo_pred/eqP: (e) => -> /eqP /no_coll -> //=.
      - by move/esym/findo_mem: (e); move/perm_mem: perm ->. 
      - by move/esym/findo_mem: (f). }
    simp cfb. rewrite Heq2 /= Heq1 /=. case: inspect => [] [] //= b'' H.
    rewrite H => [] /= [] H'. 
    suff -> : (cfb b'' [seq x <- bp2 | x != b''] = [::]) by done.  
    rewrite H' -Hind.
    + by rewrite Heq. 
    + by apply/(in_subset2 _ no_coll)/filter_subset. 
    + by apply/perm_filter.  
  - move=> no_coll perm. rewrite -Heqcall.
    have: findo (fun b' : Block => Blocks.pred b == HashB b') bp2 = Some b0.
    { move: (perm_findo (fun b' : Block => Blocks.pred b == HashB b') perm). 
      rewrite e. case f: findo=> [b'|]//= _.
      move/findo_pred: (f). move/findo_pred/eqP: (e) => -> /eqP /no_coll -> //=.
      - by move/esym/findo_mem: (e); move/perm_mem: perm ->. 
      - by move/esym/findo_mem: (f). }
    simp cfb. rewrite Heq2 /= Heq1 /=.
    case: inspect => [] [] //= b'' H; last first.
    { by move: b''; rewrite H. }
    rewrite H => [] /= [] H' /=. 
    suff -> : (cfb b'' [seq x <- bp2 | x != b'']  = b1 :: l) by done.  
    rewrite H' -Hind.
    + by rewrite Heq. 
    + by apply/(in_subset2 _ no_coll)/filter_subset. 
    + by apply/perm_filter.  
Qed. 

Lemma undup_cfb b bp :
  {in bp &, injective HashB} ->
  cfb b bp = cfb b (undup bp). 
Proof.
  funelim (cfb b bp).
  - by move/eqP: Heq ->; simp cfb;rewrite eq_refl.
  - by simp cfb; rewrite Heq0 /= Heq //. 
  - move: (mem_undup bp)=> /(mem_findo (fun b' : Block => Blocks.pred b == HashB b')).
    rewrite e -Heqcall. simp cfb. rewrite Heq1 /= Heq0 /=.
    case: inspect=> bo. case bo=> //= ? H.
    by rewrite H. 
  - move=> no_coll. 
    have: findo (fun b' : Block => Blocks.pred b == HashB b') (undup bp) = Some b0.
    { move: (mem_findo (fun b' : Block => Blocks.pred b == HashB b') (mem_undup bp)). 
      rewrite e. case f: findo=> [b'|]//= _.
      move/findo_pred: (f). move/findo_pred/eqP: (e) => -> /eqP /no_coll -> //=.
      - by move/esym/findo_mem: (e).  
      - by move/esym/findo_mem: (f); rewrite mem_undup. } 
    rewrite -Heqcall. simp cfb. rewrite Heq2 /= Heq1 /=. 
    case: inspect => [] [] //= b'' H; last first.
    rewrite H=> [] [] H'. rewrite filter_undup. 
    move: Hind Heq. rewrite -H' => <-. 
    + by move->.
    + by apply/(in_subset2 _ no_coll)/filter_subset. 
  - move=> no_coll. 
    have: findo (fun b' : Block => Blocks.pred b == HashB b') (undup bp) = Some b0.
    { move: (mem_findo (fun b' : Block => Blocks.pred b == HashB b') (mem_undup bp)). 
      rewrite e. case f: findo=> [b'|]//= _.
      move/findo_pred: (f). move/findo_pred/eqP: (e) => -> /eqP /no_coll -> //=.
      - by move/esym/findo_mem: (e).  
      - by move/esym/findo_mem: (f); rewrite mem_undup. } 
    rewrite -Heqcall. simp cfb. rewrite Heq2 /= Heq1 /=. 
    case: inspect => [] [] //= b'' H //=; last first.
    { by move: b''; rewrite H. }
    rewrite H=> [] [] H'. rewrite filter_undup. 
    move: Hind Heq. rewrite -H' => <-. 
    + by move->. 
    + by apply/(in_subset2 _ no_coll)/filter_subset. 
Qed. 

Lemma cfb_mem b bp1 bp2: 
    {in bp1 &, injective HashB} -> 
    bp1=i bp2 -> cfb b bp1 = cfb b bp2. 
Proof.
  move=> no_coll mem. 
  rewrite undup_cfb // [cfb _ bp2]undup_cfb; last first.
  { by apply/(in_subset2 _ no_coll)=> ?; rewrite mem. } 
  apply/perm_cfb.
  - by apply/(in_subset2 _ no_coll)=> ?; rewrite mem mem_undup. 
  - by apply/perm_undup. 
Qed. 

Lemma cfb_non_empty_subset b bp1 : forall bp2,  
    {in bp2 &, injective HashB} -> 
    {subset bp1 <= bp2} ->
    cfb b bp1 != [::] ->
    cfb b bp1 = cfb b bp2. 
Proof.   
  funelim (cfb b bp1); move=> bp2 coll sub nnil.
  - by rewrite -Heqcall; simp cfb; rewrite Heq.   
  - by rewrite -Heqcall; simp cfb; rewrite Heq0 /= Heq.   
  - by move: nnil; rewrite -Heqcall.
  - by move: nnil; rewrite -Heqcall.
  - have: findo (fun b' : Block => Blocks.pred b == HashB b') bp2 = Some b0.
    { move/esym/findo_mem/sub : (e). move: coll. move/findo_pred: (e). 
      clear. move=> predb0. elim: bp2=> //= > IH coll.
      rewrite inE=> /orP [/eqP <-|]; [by rewrite predb0|]. 
      case eq: (_==_)=> //= .
      - move=> bin. apply/f_equal/coll. 
        + by rewrite mem_head.
        + by rewrite inE orbC bin.
        + by move/eqP: predb0 <-; move/eqP: eq <-.
      - by apply/IH/(in_subset2 _ coll)/subset_cons. }
    rewrite -Heqcall. simp cfb. rewrite Heq2 /= Heq1 /=.
    case: inspect => [] [] //= b'' H //=; last first.
    { by move: b''; rewrite H. }
    rewrite H=> [] [] H'. 
    move: Hind (Heq). rewrite -H' => <-. 
    - by move->. 
    - by apply/(in_subset2 _ coll)/filter_subset. 
    - by apply/subset_filter. 
    - by rewrite H' Heq. 
Qed. 

Lemma cfb_valid_subset b bp1 bp2 :  
    {in bp2 &, injective HashB} -> 
    {subset bp1 <= bp2} ->
    valid_chain (cfb b bp1) ->
    valid_chain (cfb b bp2). 
Proof.   
  move=> coll sub vc. rewrite -(@cfb_non_empty_subset _ bp1) //. 
  move/valid_chain_starts_gb : vc => [] c <-.
  by case c. 
Qed. 

Lemma only_gb_valid c :
  reflect (c = [::]) ((GenesisBlock :: c) ✓).
Proof.
  apply/(iffP idP); last by move->; apply/valid_chain_block_gb.
  case: c=> // >. rewrite valid_chain_ext=> /and3P [] _ _ /=.
    by rewrite /= /lt_slots GenesisSlot ltn0. 
Qed. 

Lemma cfb_valid_chain  b bp c :
  {in bp &, injective HashB} ->
  valid_chain (b :: c) ->
  {subset c <= bp} ->
  cfb b bp = b :: c.
Proof.
  move=> coll vc sub.
  funelim (cfb b bp); rewrite -Heqcall.
  - by move/eqP: Heq vc -> =>  /only_gb_valid ->.
  - have gbin: GenesisBlock \in bp. 
    { move: vc sub.
      case ceq: c=> [| b' c']//=; first by move/valid_chain_block_gb/eqP; rewrite Heq0.
      rewrite valid_chain_ext /linked=> /and4P [] _ _ _vc /suffix_gb_vc/suffixP [] ? <- -> //.
      by rewrite mem_cat orbC inE eq_refl. }
    apply/f_equal. 
    move: sub vc. case: c=> //= [_|].
    + by move/valid_chain_block_gb/eqP; rewrite Heq0.
    + move=> b' l sub. rewrite valid_chain_ext=> /and3P [] _.
      rewrite /linked. move/eqP: Heq -> => /eqP.
      move/coll. rewrite gbin=> /trueI. rewrite sub; [| by rewrite mem_head].
      by move/trueI <- => /andP [] _ /only_gb_valid ->. 
  - move: sub vc.
    case ceq: c=> [|b' c'] //=; first by move=> _ /valid_chain_block_gb/eqP; rewrite Heq1. 
    rewrite valid_chain_ext=> sub /and3P [] ?. 
    rewrite /linked => H. 
    move: (findo_has (fun b' : Block => Blocks.pred b == HashB b') bp).
    rewrite e /=. 
    move/esym/hasP => /=. rewrite /(~_) => H'. exfalso. apply/H'=> //.
    exists b'; by [apply/sub; rewrite mem_head|]. 
  - move: sub vc.
    case ceq: c=> [| b' c']//=; first by move=> _ /valid_chain_block_gb/eqP; rewrite Heq2.
    move=> sub. rewrite valid_chain_ext /linked=> /and4P [] corr link dec vc.
    have b0b'eq: b0 = b'.
    { apply/coll.
      + by apply/findo_mem/esym/e. 
      + by apply/sub; rewrite mem_head. 
      + by move/eqP: link <-  => {Heq0}; move/findo_pred/eqP: e ->. }
    move: Heq. rewrite (@Hind c') //.
    + by apply/(in_subset2 _ coll)/mem_subseq/filter_subseq.
    + by rewrite b0b'eq. 
    + rewrite b0b'eq=> b'' b''in. rewrite mem_filter sub; last by rewrite inE orbC b''in.  
      rewrite andbC //=. apply/(in_not_in b''in).
      by move/uniq_valid_chain: vc => /andP []. 
  - move: sub vc.
    case ceq: c=> [| b' c']//=; first by move=> _ /valid_chain_block_gb/eqP; rewrite Heq2.
    move=> sub. rewrite valid_chain_ext /linked=> /and4P [] corr link dec vc.
    have b0b'eq: b0 = b'.
    { apply/coll.
      + by apply/findo_mem/esym/e. 
      + by apply/sub; rewrite mem_head. 
      + by move/eqP: link <-  => {Heq0}; move/findo_pred/eqP: e ->. }
    apply/f_equal. rewrite -Heq -b0b'eq. apply/Hind. 
    + by apply/(in_subset2 _ coll)/mem_subseq/filter_subseq.
    + by rewrite b0b'eq.
    + rewrite b0b'eq=> b'' b''in. rewrite mem_filter sub; last by rewrite inE orbC b''in.  
      rewrite andbC //=. apply/(in_not_in b''in).
        by move/uniq_valid_chain: vc => /andP [].
Qed.

Lemma cfb_valid_chain'  b bp c :
  {in GenesisBlock :: bp &, injective HashB} ->
  valid_chain (b :: c) ->
  {subset c <= GenesisBlock:: bp} ->
  cfb b bp = b :: c.
Proof.
  move=> coll vc sub.
  funelim (cfb b bp); rewrite -Heqcall.
  - by move/eqP: Heq vc -> =>  /only_gb_valid ->.
  - apply/f_equal. 
    move: sub vc. case: c=> //= [_|].
    + by move/valid_chain_block_gb/eqP; rewrite Heq0.
    + move=> b' l sub. rewrite valid_chain_ext=> /and3P [] _.
      rewrite /linked. move/eqP: Heq -> => /eqP.
      move/coll. rewrite mem_head sub; last by rewrite mem_head.
        by move/trueI/trueI <- => /andP [] _ /only_gb_valid ->. 
  - move: sub vc.
    case ceq: c=> [|b' c'] //=; first by move=> _ /valid_chain_block_gb/eqP; rewrite Heq1. 
    rewrite valid_chain_ext=> sub /and3P [] ?. 
    rewrite /linked => H. 
    move: (findo_has (fun b' : Block => Blocks.pred b == HashB b') bp).
    rewrite e /=. 
    move/esym/hasP => /=. rewrite /(~_) => H'. exfalso. apply/H'=> //.
    exists b'; try done. move/(_ b'): sub. rewrite mem_head inE => /trueI/orP [/eqP eqb'| //].
      by move/eqP: H Heq0 ->; rewrite eqb' eq_refl.
  - move: sub vc.
    case ceq: c=> [| b' c']//=; first by move=> _ /valid_chain_block_gb/eqP; rewrite Heq2.
    move=> sub. rewrite valid_chain_ext /linked=> /and4P [] corr link dec vc.
    have b0b'eq: b0 = b'.
    { apply/coll.
      + rewrite inE. apply/orP. constructor 2.
          by apply/findo_mem/esym/e. 
      + by apply/sub; rewrite mem_head. 
      + by move/eqP: link <-  => {Heq0}; move/findo_pred/eqP: e ->. }
    move: Heq. rewrite (@Hind c') //.
    + apply/(in_subset2 _ coll)/mem_subseq=> /=. rewrite eq_refl.
        by apply/filter_subseq.
    + by rewrite b0b'eq. 
    + rewrite b0b'eq=> b'' b''in. rewrite inE mem_filter andbC //=.
      move/(_ b''): sub. rewrite inE orbC b''in inE /= => /trueI/orP [-> | ->] //=.
      apply/orP; right. apply/(in_not_in b''in).
        by move/uniq_valid_chain: vc => /andP []. 
  - move: sub vc.
    case ceq: c=> [| b' c']//=; first by move=> _ /valid_chain_block_gb/eqP; rewrite Heq2.
    move=> sub. rewrite valid_chain_ext /linked=> /and4P [] corr link dec vc.
    have b0b'eq: b0 = b'.
    { apply/coll.
      + rewrite inE. apply/orP. constructor 2.
          by apply/findo_mem/esym/e. 
      + by apply/sub; rewrite mem_head. 
      + by move/eqP: link <-  => {Heq0}; move/findo_pred/eqP: e ->. }
    apply/f_equal. rewrite -Heq -b0b'eq. apply/Hind. 
    + apply/(in_subset2 _ coll)/mem_subseq=> /=. rewrite eq_refl.
        by apply/filter_subseq.
    + by rewrite b0b'eq.
    + rewrite b0b'eq=> b'' b''in. rewrite inE mem_filter andbC //=.
      move/(_ b''): sub. rewrite inE orbC b''in inE /= => /trueI/orP [-> | ->] //=.
      apply/orP; right. apply/(in_not_in b''in).
        by move/uniq_valid_chain: vc => /andP []. 
Qed. 

Lemma adv_broadcast_honest_block_history N nms :
  honest_subset [seq get_block mp.1 | mp <- nms] (block_history N) ->
  honest_block_hist N =i honest_block_hist (flood_msgs_adv nms N). 
Proof.
  elim: nms=> //= [] [] m ? nms IH sub.
  rewrite IH; last first.
  - apply/(subset_trans _ sub).
    by case is_honest => //=; apply/subset_cons. 
  - rewrite /flood_msg_adv /=.
    move: sub. case: is_honest => //= sub b. 
    apply/idP/idP. 
    + by apply/subset_cons.
    + rewrite inE=> /orP [/eqP ->| //].
      move/(_ (get_block m)) : sub.
      rewrite mem_head 2!mem_filter=> /trueI /andP [] ??.
      apply/andP; constructor; try done. 
        by apply/block_history_adv_broadcast_subset.
Qed. 
  
Lemma coll_free_big_step N N' :
  collision_free N -> N' ⇓ N -> collision_free N'.
Proof.
  move=> no_coll ?.
  by apply/(in_subset2 _ no_coll)/subset_cons2/block_history_monotone. 
Qed. 

Lemma honest_block_cfb_valid N b:
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  b \in honest_block_hist N ->
  valid_chain (cfb b (block_history N)). 
Proof.
  elim=> // y z [] {y z} // {}N prog_N N0N IH ff no_coll.
  (* Delivery step *)
  - rewrite -delivery_preserves_honest_block_hist // => /IH.
    apply: instant1.
    { apply/(forging_free_prev _ ff).
      by do 2! econstructor. }
    set N' := (_[[_ := _]]). 
    have NN': N ⇓ N'  by do 2! econstructor. 
    move/(_ (coll_free_big_step no_coll NN'))=> vc /=. 
    move: no_coll => /=. 
    elim: exec_order=> //= p ps. set N'' := foldr _ _ _.
    move=> IH' coll.
    have: cfb b [seq get_block m | m <- history N''] ✓. 
    { apply/IH' => b1 b2 H1 H2. apply/coll.
      - move: H1. rewrite inE=> /orP [/eqP ->|]; [by rewrite mem_head|].
        rewrite inE orbC=> /mapP [] m + ->.
        move/(history_monotone_delivery p)=> H.
        apply/orP; constructor 1. apply/mapP=> /=.
        by exists m. 
      - move: H2. rewrite inE=> /orP [/eqP ->|]; [by rewrite mem_head|].
        rewrite inE orbC=> /mapP [] m + ->.
        move/(history_monotone_delivery p)=> H.
        apply/orP; constructor 1. apply/mapP.
          by exists m. }
    move=> {}IH'.
    rewrite -(@cfb_non_empty_subset _ [seq get_block m | m <- history N'']) //. 
    + by apply/(in_subset2 _ coll)/subset_cons.
    + by apply/map_subset/history_monotone_delivery. 
    + by move/valid_chain_starts_gb: IH'=> [] c <-; case: c. 
  (* Baking step *)
  - set N' := (_[[_ := _]]).
    have NN': N ⇓ N'  by do 2! econstructor.
    move: no_coll=> /=. 
    move: IH. apply: instant1=> [|IH].
    { apply/(forging_free_prev _ ff).
        by do 2! econstructor. }
    move/ProgressB: (baking_steps_refl N') (uniq_exec_order N0N).  
    elim: exec_order=> //= p ps.
    set N'' := foldr _ _ _. move=> + /BakeStep be /andP [] pinps ups. move/(_ be ups) => IH'. 
    rewrite /party_bake_step_world.
    case state_p: (_.[? _])=> [l|] //=. 
    case honesty_p: (~~_)=> //=.
    (* Honest party *)
    + rewrite /honest_bake /=.
      case win : Winner=> //=. 
      set nb := MkBlock _ _ _ _. case honest_pk: is_honest => //=; last first.
      { move => coll bin.
        apply/(@cfb_valid_subset _ [seq get_block m | m <- history N''])=> //. 
        - by apply/(in_subset2 _ coll)/subset_cons.
        - by apply/subset_cons.
        -  apply/IH'=> //.
           by apply/(in_subset2 _ coll)/subset_cons2/subset_cons. }
      move=> coll. rewrite inE=> /orP [/eqP ->|]; last first.  
      { move => bin.
        apply/(@cfb_valid_subset _ [seq get_block m | m <- history N''])=> //. 
        - by apply/(in_subset2 _ coll)/subset_cons.
        - by apply/subset_cons.
        -  apply/IH'=> //.
             by apply/(in_subset2 _ coll)/subset_cons2/subset_cons. }
      rewrite -/(block_history _).
      have ->: cfb nb (nb :: [seq get_block m | m <- history N'']) = nb :: (bestChain (t_now N'' - 1) (tree l)). 
      { apply/cfb_valid_chain'. 
        - by apply/(in_subset2 _ coll). 
        - move: (best_chain_valid (tree l) (t_now N'' - 1)). 
          case bc: (bestChain (t_now N'' - 1) (tree l))=> //=.
          rewrite valid_chain_ext=> -> //=. rewrite win bc /= eq_refl. 
          rewrite /= andbC /=. apply/(@leq_ltn_trans (t_now N'' -1)).
          + by apply/(@best_chain_time _ (tree l)); rewrite bc mem_head.
          + by rewrite subn1 ltn_predL baking_preserves_time; apply/lt_0_time.
            have state_pN: has_state p N l.
            { by move: state_p; rewrite no_state_change_bake_different_parties. }
            apply/subset_trans; first by apply/best_chain_in_all.
            apply/subset_trans; first by apply/filter_subset. 
            apply/subset_trans; first
              by apply/(subset_honest_tree N0N _ state_pN); rewrite honest_not_corrupt honesty_p.
            apply/subset_trans; first by apply/(honest_tree_hist_gb_subset N0N).
            apply/subset_cons2/subset_trans; last by apply/subset_cons. 
            by apply/map_subset/history_monotone_bakes. }
      move: (best_chain_valid (tree l) (t_now N'' - 1)). case bc: (bestChain _ _)=> [|??] //.
      rewrite valid_chain_ext /= win bc /= eq_refl andbA andbC=> -> /=.
      apply/(@leq_ltn_trans (t_now N'' -1)).
      * by apply/(@best_chain_time _ (tree l)); rewrite bc mem_head.
      * by rewrite subn1 ltn_predL baking_preserves_time; apply/lt_0_time.
    + case: ff=> _ /(_ _ be) /=. 
      rewrite -/N''. case: AdversarialBake => nms ? /= sub coll bin.
      apply/cfb_valid_subset; last first. 
      * apply/IH'. 
        -- by apply/(in_subset2 _ coll)/subset_cons2/block_history_adv_broadcast_subset.
        -- by move: bin; rewrite -adv_broadcast_honest_block_history.
      * by apply/block_history_adv_broadcast_subset. 
      * by apply/(in_subset2 _ coll)/subset_cons. 
  (* Inc *)
  - apply/IH=> //. apply/(forging_free_prev _ ff).
      by do 2! econstructor.
  (* Perms *)
  - move=> /= ?. apply/ff => //.
    apply/(forging_free_prev _ no_coll).
      by do 2! econstructor.
  - move=> /= ?. apply/ff => //.
    apply/(forging_free_prev _ no_coll).
      by do 2! econstructor.
Qed.         

Definition honest_block_hist_gb N := [seq b <- block_hist_gb N | honest_block b]. 

Arguments honest_block_hist_gb _/. 

Lemma gb_honest_block_cfb_valid N b:
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  b \in honest_block_hist_gb N ->
  valid_chain (cfb b (block_history N)). 
Proof.
  move/honest_block_cfb_valid=> H /H {}H /H {}H.
  rewrite mem_filter inE => /andP [] hb /orP [/eqP ->| bin ].
  - simp cfb. rewrite eq_refl /=.
    by apply/valid_chain_block_gb. 
  - by apply/H; rewrite mem_filter hb bin. 
Qed. 

Lemma all_honest_block_cfb_valid N:
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  all (fun b => valid_chain (cfb b (block_history N))) (honest_block_hist N).
Proof. by move/honest_block_cfb_valid=> H /H {} H /H {} H; apply/allP=> ? /H. Qed.

  
(** cfb := cfb. The reason that this is dependent on
    progress of N, is that this is the only thing that makes the
    no-forging assumption and no-hash-collision valid. **)
Lemma delivery_preserves_honest_cfb N b :
  N0 ⇓ N ->
  forging_free N ->
  collision_free (foldr party_rcv_step_world N (exec_order N)) ->
  b \in honest_block_hist N ->
  N @ Ready ->  
  cfb b (block_history N) =
  cfb b (block_history (foldr party_rcv_step_world N (exec_order N))). 
Proof.
  move=> N0N ff no_coll bin prog_N. apply/esym.
  move: no_coll => /=. rewrite (progress_no_effect_history Delivered)=> no_coll.
  set N' := (_[[_ := _]]). 
  have NN': N ⇓ N'  by do 2! econstructor. 
  apply/esym/cfb_non_empty_subset.
  - apply/(in_subset2 _ no_coll)=> /=. by apply/subset_trans; last apply/subset_cons.
  - by apply/map_subset/history_monotone_deliverys. 
  - have no_coll1: collision_free N. apply/(coll_free_big_step). exact no_coll. by do 2! econstructor. 
    move: (honest_block_cfb_valid N0N ff no_coll1 bin).
    by case: (cfb _ _). 
Qed. 

Lemma delivery_preserves_honest_pos N b :
  N0 ⇓ N ->
  forging_free N ->
  collision_free (foldr party_rcv_step_world N (exec_order N)) ->
  b \in honest_block_hist N ->
  N @ Ready ->  
  pos b N =
  pos b (foldr party_rcv_step_world N (exec_order N)). 
Proof. by move=> ?????; rewrite /= -delivery_preserves_honest_cfb. Qed. 

Lemma valid_chain_non_empty c :
  valid_chain c -> c != [::]. 
Proof. by case: c. Qed.

Lemma honest_valid_chain_bake N N2 ps :
  N0 ⇓ N ->
  N ⇓ N2 ->
  forging_free N2 ->
  let: N' := foldr party_bake_step_world N ps in
  BakingSteps N' N2 ->
  uniq ps -> 
  collision_free N' ->
  all (fun b => valid_chain (cfb b (block_history N'))) (honest_block_hist N').
Proof.
  move=> N0N NN2 ff bs uns no_coll.
  apply/allP=> b. move: bs uns no_coll.
  elim: ps => [_ _ |] //=.
  { apply/honest_block_cfb_valid=> //.
    by apply/(forging_free_prev _ ff). }
  move=> p ps. set N' := foldr _ _ _.
  move=> + /BakeStep bs /andP [] p_not_ps uns. move=> /(_ bs)/(_ uns) IH no_coll.
  move: no_coll.
  rewrite /party_bake_step_world.
  case state_p: (_.[? _])=> [l|] //=.
  case honesty_p: (~~_)=> //=.
  (* Honest party *)
  + rewrite /honest_bake /=.
    case win : Winner=> //=.
    set nb := MkBlock _ _ _ _. case honest_pk: is_honest => //=; last first.
    { move => coll bin.
      apply/(@cfb_valid_subset _ [seq get_block m | m <- history N'])=> //.
      - by apply/(in_subset2 _ coll)/subset_cons.
      - by apply/subset_cons.
      - apply/IH=> //.
           by apply/(in_subset2 _ coll)/subset_cons2/subset_cons. }
    move=> coll. rewrite inE=> /orP [/eqP ->|]; last first.
    { move => bin.
      apply/(@cfb_valid_subset _ [seq get_block m | m <- history N'])=> //.
      - by apply/(in_subset2 _ coll)/subset_cons.
      - by apply/subset_cons.
      -  apply/IH=> //.
           by apply/(in_subset2 _ coll)/subset_cons2/subset_cons. }
    rewrite -/(block_history _).
    have ->: cfb nb (nb :: [seq get_block m | m <- history N']) = nb :: (bestChain (t_now N' - 1) (tree l)).
    { apply/cfb_valid_chain'.
      - by apply/(in_subset2 _ coll).
      - move: (best_chain_valid (tree l) (t_now N' - 1)).
        case bc: (bestChain (t_now N' - 1) (tree l))=> //=.
        rewrite valid_chain_ext=> -> //=. rewrite win bc /= eq_refl.
        rewrite /= andbC /=. apply/(@leq_ltn_trans (t_now N' -1)).
        + by apply/(@best_chain_time _ (tree l)); rewrite bc mem_head.
        + by rewrite subn1 ltn_predL baking_preserves_time; apply/lt_0_time.
          have state_pN: has_state p N l.
          { by move: state_p; rewrite no_state_change_bake_different_parties. }
          apply/subset_trans; first by apply/best_chain_in_all.
          apply/subset_trans; first by apply/filter_subset.
          apply/subset_trans; first
            by apply/(subset_honest_tree N0N _ state_pN); rewrite honest_not_corrupt honesty_p.
          apply/subset_trans; first by apply/(honest_tree_hist_gb_subset N0N).
          apply/subset_cons2/subset_trans; last by apply/subset_cons.
            by apply/map_subset/history_monotone_bakes. }
    move: (best_chain_valid (tree l) (t_now N' - 1)). case bc: (bestChain _ _)=> [|??] //.
    rewrite valid_chain_ext /= win bc /= eq_refl andbA andbC=> -> /=.
    apply/(@leq_ltn_trans (t_now N' -1)).
    * by apply/(@best_chain_time _ (tree l)); rewrite bc mem_head.
    * by rewrite subn1 ltn_predL baking_preserves_time; apply/lt_0_time.
  + case: ff => _ /(_ _ bs) /=. 
    rewrite -/N'.
    case: AdversarialBake => nms ? /= sub coll bin.
    apply/cfb_valid_subset; last first.
    * apply/IH.
      -- by apply/(in_subset2 _ coll)/subset_cons2/block_history_adv_broadcast_subset.
      -- by move: bin; rewrite -adv_broadcast_honest_block_history.
    * by apply/block_history_adv_broadcast_subset.
    * by apply/(in_subset2 _ coll)/subset_cons.
Qed.


Lemma ready_before_delivered N :
  N0 ⇓ N -> N @ Delivered ->
  exists N', [/\ N0 ⇓ N', N' ⇓[0] N & N' @ Ready]. 
Proof. 
  elim=> //= x y [] N' {x y} //.
  - move=> prog_N' N0N' IH _.
    exists N'. constructor; try done.
    constructor.
    + by econstructor; econstructor.
    + by rewrite add0n delivery_preserves_time. 
  - move=> ?? N0N' IH /= /IH [] N'' [] ?[]???.
    exists N''. constructor; try done. 
    constructor; try done.
      by econstructor; first by econstructor; try done.
  - move=> ?? N0N' IH /= /IH [] N'' [] ?[]???.
    exists N''. constructor; try done. 
    constructor; try done.
      by econstructor; first by econstructor; try done.
Qed.       

Lemma delivered_before_baked N :
  N0 ⇓ N -> N @ Baked ->
  exists N', [/\ N0 ⇓ N', N' ⇓[0] N & N' @ Delivered]. 
Proof. 
  elim=> //= x y [] N' {x y} //.
  - move=> prog_N' N0N' IH _.
    exists N'. constructor; try done.
    constructor.
    + by econstructor; econstructor.
    + by rewrite add0n baking_preserves_time. 
  - move=> ?? N0N' IH /= /IH [] N'' [] ?[]???.
    exists N''. constructor; try done. 
    constructor; try done.
      by econstructor; first by econstructor; try done.
  - move=> ?? N0N' IH /= /IH [] N'' [] ?[]???.
    exists N''. constructor; try done. 
    constructor; try done.
      by econstructor; first by econstructor; try done.
Qed.       

Lemma delivery_preserves_honest_block_hist' N N':
  N0 ⇓ N -> N @  Ready -> N ⇓[0] N' -> forging_free N' -> N' @ Delivered ->
  honest_block_hist N =i honest_block_hist N'. 
Proof.
  move=> N0N prog_N [].
  rewrite add0n. 
  elim=> // ?? [] // {}N' prog_N' NN' IH.
  - rewrite delivery_preserves_time => teq ff. 
    rewrite -delivery_preserves_honest_block_hist //; last by apply/(big_step_trans N0N NN').
    move: teq prog_N prog_N'. elim: NN'=> //= ?? [] //=.
    move=> N'' _ NN'' _ teq.
    move: (monotone_time NN'').
      by rewrite teq ltnn. 
  - move=> {}IH ? ff ?.
    apply/IH=> //. apply/(forging_free_prev _ ff).
    by do 2!econstructor. 
  - move=> {}IH ? ff ?.
    apply/IH=> //. apply/(forging_free_prev _ ff).
    by do 2!econstructor. 
Qed. 

Lemma cfb_subset_honest_tree N b :
  N0 ⇓ N ->
  forging_free N -> 
  collision_free N ->
  b \in honest_block_hist N ->
  {subset cfb b (block_history N) <= allBlocks (honest_tree N)}.
Proof.
  move=> N0N. 
  elim: N0N=> // A B [] {A B} // {} N.
  (* Delivery *)
  - move=> prog_N N0N +  ff no_coll.
    have ffN: forging_free N.
    { by apply/(forging_free_prev _ ff); do 2!econstructor. } 
    apply: instant2=> //.
    { by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_deliverys. }
    rewrite -delivery_preserves_honest_block_hist // => IH bin.
    move: (IH bin) => {}IH.
    rewrite -(@cfb_non_empty_subset _ (block_history N)); last first. 
    + apply/valid_chain_non_empty/honest_block_cfb_valid=> //. 
      by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_deliverys. 
    + by apply/map_subset/history_monotone_deliverys. 
    + by apply/(in_subset2 _ no_coll)/subset_cons. 
    + apply/(subset_trans IH)=> /=.
      apply/(monotone_honest_tree N0N).
      by do 2! econstructor.
  (* Baking *)
  - move=> prog_N N0N + ff no_coll.
    have ffN: forging_free N.
    { by apply/(forging_free_prev _ ff); do 2!econstructor. } 
    apply: instant2 => //; first
      by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_bakes.  
    set N2 := _ [[_:=_]].
    have NN2: N ⇓ N2 by do 2! econstructor. 
    move/ProgressB: (baking_steps_refl N2) (uniq_exec_order N0N) no_coll => +++ IH. 
    rewrite {2 3 4}/N2. 
    elim : exec_order=> //= p ps.
    set N' := foldr _ _ _. move=> + /BakeStep bs /andP [] pnotps ups no_coll.
    move/(_ bs)/(_ ups). 
    apply: instant1; first 
      by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_bake. 
    move: no_coll=> + {}IH. rewrite /party_bake_step_world /=.
    case state_p: (_.[?_]) => [l|] //=.
    case corrupt_p: (~~_)=> //=. 
    (* Honest baker *)
    + rewrite /honest_bake /=.
      case win_p: Winner => //=; last first.
      { move=> no_coll /IH {}IH. apply/(subset_trans IH).
        rewrite /honest_tree /honest_parties /=. 
        elim exec_order=> //= p' ps' {}IH /=.
        case honest_p': is_honest=> //=. rewrite /blocks /= fnd_set.
        case: (_==_)/eqP => [->|].
        - rewrite state_p=> b'.
          rewrite 2!allBlocks_build_cat.
          by move: b'; apply/subset_cat2/IH. 
        - case: (_.[? _])=> //= ? _ b'. 
          rewrite 2!allBlocks_build_cat.
          by move: b'; apply/subset_cat2/IH. }
      move: state_p. 
      rewrite (no_state_change_bake_different_parties _ pnotps)=> state_p.      
      move/(pk_preserved N0N): (state_p) ->. 
      set nb:= MkBlock _ _ _ _. 
      rewrite honest_not_corrupt corrupt_p inE => no_coll /orP [/eqP bnbeq|].
      * rewrite bnbeq. 
        have ->: cfb nb (nb :: [seq get_block m | m <- history N'])
          = (nb :: (bestChain (t_now N' - 1) (tree l))). 
        { apply/cfb_valid_chain'. 
          - by apply/(in_subset2 _ no_coll). 
          - move: (best_chain_valid (tree l) (t_now N' - 1)).
            case bc: (bestChain (t_now N' - 1) (tree l))=> //=.
            rewrite valid_chain_ext=> -> //=.
            move/(pk_preserved N0N): (state_p) <-. 
            rewrite win_p bc /= eq_refl.
            rewrite /= andbC /=. apply/(@leq_ltn_trans (t_now N' -1)).
            + by apply/(@best_chain_time _ (tree l)); rewrite bc mem_head.
            + by rewrite subn1 ltn_predL baking_preserves_time; apply/lt_0_time.
              apply/subset_trans; first by apply/best_chain_in_all.
              apply/subset_trans; first by apply/filter_subset.
              apply/subset_trans; first
                by apply/(subset_honest_tree N0N _ state_p); rewrite honest_not_corrupt corrupt_p.
              apply/subset_trans; first by apply/(honest_tree_hist_gb_subset N0N).
              apply/subset_cons2/subset_trans; last by apply/subset_cons.
                by apply/map_subset/history_monotone_bakes. }
        have: p \in exec_order N'. 
        { rewrite bakes_preserves_order.
          apply/has_state_in_exec_order => //=.
          exact state_p. }
        rewrite/honest_tree /honest_parties /=.  
        elim exec_order=> //= p' ps' {}IH /=.
        rewrite inE => /orP [/eqP <-|]. 
        -- rewrite honest_not_corrupt corrupt_p /= => b'. 
           rewrite all_build /blocks /= fnd_set eq_refl /=.
           move=> H. rewrite inE. apply/orP. constructor 2. move: H. 
           rewrite mem_cat=> H. apply/orP. constructor 1.
           move: H. rewrite all_extend mem_cat orbC inE=> /orP [/eqP -> //|]; first by rewrite mem_head.
           rewrite orbC. move/best_chain_in_all.
           by rewrite mem_filter=> /andP [] _ ->.  
        -- move/IH=> {} IH.
           apply/(subset_trans IH). case: is_honest=> //= b'.
           rewrite all_build allBlocks_build_cat mem_cat orbC. rewrite /blocks /=.
           by rewrite all_build=> ->. 
      * move=> bin. move: (IH bin) => {}IH. 
        rewrite -(@cfb_non_empty_subset _ (block_history N')); last first.
        -- apply/valid_chain_non_empty.
           move: (honest_valid_chain_bake N0N NN2 ff bs ups).
            apply: instant1. 
            { by apply/(in_subset2 _ no_coll)/subset_cons2/subset_cons. }
            by move/allP/(_ b); rewrite bin=> /trueI. 
        -- by apply/subset_cons.
        -- by apply/(in_subset2 _ no_coll)/subset_cons. 
        -- apply/(subset_trans IH). 
           rewrite /honest_tree /honest_parties /=. 
           elim exec_order=> //= p' ps' {}IH /=.
           case honest_p': is_honest=> //=. rewrite /blocks /= fnd_set.
           case: (_==_)/eqP => [-> /=|].
           ++ rewrite (no_state_change_bake_different_parties _ pnotps) state_p => b'.
              rewrite 2!allBlocks_build_cat => H. 
              rewrite mem_cat /=. rewrite all_build inE .
              rewrite all_extend mem_cat.  
              
              move: H. rewrite mem_cat=> //= /orP [].
              ** by rewrite all_build inE orbA => -> //. 
              ** by move/IH ->; rewrite orbC. 
           ++ move=> _ b'. rewrite 2!allBlocks_build_cat.
              by apply/subset_cat2. 
    (* Dishonest baker *)
    + case: (ff)=> _ /(_ _ bs) /=. 
      rewrite -/N'.
      case : AdversarialBake=> //= mds ?. 
      move/adv_broadcast_honest_block_history => <- no_coll bin.
      move: (IH bin)=> {}IH.
      rewrite -(@cfb_non_empty_subset _ (block_history N')); last first.
      * apply/valid_chain_non_empty.
        move: (honest_valid_chain_bake N0N NN2 ff bs ups).
        apply: instant1. 
        { by apply/(in_subset2 _ no_coll)/subset_cons2/block_history_adv_broadcast_subset. }
        by move/allP/(_ b); rewrite bin=> /trueI. 
      * by apply/block_history_adv_broadcast_subset.
      * by apply/(in_subset2 _ no_coll)/subset_cons.
      * rewrite /honest_tree. rewrite /(_ [[_ := _]]). 
        rewrite broadcast_adv_msgs_preserves_state.
        rewrite broadcast_adv_msgs_preserves_order /=. rewrite /honest_parties /=.
        by rewrite /blocks /=. 
  - move=> ps N0N IH ff no_coll /=.
    apply/IH=> //. apply/(forging_free_prev _ ff).
    by do 2! econstructor. 
  - move=> ps perm N0N IH ff /= /IH {} IH /IH {} IH ? /IH {}IH.
    rewrite -(@honest_tree_preservation N _ (progress N)) //. 
    + by apply/IH/(forging_free_prev _ ff); do 2! econstructor.
    + by do 2! econstructor.
  - move=> ??? IH ff no_coll.
    by apply/IH=> //; apply/(forging_free_prev _ ff); do 2! econstructor. 
Qed. 

Lemma no_honest_pos_share_sb N:
  N0 ⇓ N ->
  forging_free N -> 
  collision_free N ->
  forall b, b \in super_blocks_world N ->
             all (fun b' => ((pos b N) != pos b' N) || (b == b')) (honest_block_hist N). 
Proof.
  move=> N0N. 
  elim: N0N=> // y z [] {y z} // {}N prog_N N0N IH ff no_coll b.
  (* Delivery case *)
  - have ffN : forging_free N.
    { by apply/(forging_free_prev _ ff); do 2! econstructor. }
    have/IH: {in GenesisBlock :: block_history N &, injective HashB}. 
    { apply/(in_subset2 _ no_coll)/subset_cons2. 
        by apply/map_subset/history_monotone_deliverys. }
    move=> /(_ ffN) {}IH.
    rewrite mem_undup mem_filter -andbA andbC -andbA => /andP [] sslb.
    rewrite andbC -(mem_filter honest_block). 
    rewrite -delivery_preserves_honest_block_hist // => bin.
    move: (IH b). rewrite /= mem_undup mem_filter sslb -andbA andbC /=.
    rewrite andbC -(mem_filter honest_block) bin => /trueI H. 
    apply/allP=> b'. rewrite -delivery_preserves_honest_block_hist //. 
    rewrite -/(pos _ _) -delivery_preserves_honest_pos // => b'in. 
    rewrite -/(pos _ _) -delivery_preserves_honest_pos //. 
      by move: b' b'in; apply/allP. 
  (* Baking case. *)
  - have ffN : forging_free N.
    { by apply/(forging_free_prev _ ff); do 2! econstructor. }
    move: IH. apply: instant2=> // [|IH]. 
    { apply/(in_subset2 _ no_coll)/subset_cons2. 
      by apply/map_subset/history_monotone_bakes. } 
    rewrite mem_undup mem_filter -andbA => /and3P [] honest_b ssb.
    set N' := _[[ progress := _]].
    have NN': N ⇓ N' by do 2! econstructor. 
    move=> bin. 
    move/allP/(_ b): (no_premature_honest_blocks (big_step_trans N0N NN') ff)=> /=.
    (* We test if it is a block baked in this round or not. *)
    rewrite mem_filter honest_b bin leq_eqVlt => /trueI/orP []; last first. 
    (** It is baked in previous round **)
    { move=> sl_lt.
      have: b \in [seq b <- honest_block_hist N'| sl b < t_now N']. 
      { by rewrite 2!mem_filter sl_lt /= honest_b bin. }
      rewrite baking_preserves_time.
      rewrite -(honest_blocks_below_slot_preserved N0N NN') //.
      move=> {}bin. 
      move: (ready_before_delivered N0N prog_N)=> [] N_R [] N0N_R NR_N prog_NR.
      move/(_ b): IH.
      apply: instant1=> [| {}IH].  
      { rewrite /= mem_undup mem_filter honest_b ssb.
        by move: bin; rewrite 2!mem_filter=> /andP [] _ /andP [] _ ->. } 
      move: bin. rewrite mem_filter=> /andP [] ltsl. 
      rewrite -(delivery_preserves_honest_block_hist' N0N_R) // => bin. 
      apply/allP=> b' b'in.
      move: NR_N=> [] N_RN. rewrite add0n=> teq.
      move: IH. 
      have ffNR : forging_free N_R by apply/(forging_free_prev _ ffN). 
      have no_collR: collision_free N_R. 
      { apply/(in_subset2 _ no_coll)/subset_cons2.
        apply/subset_trans; first by apply/(block_history_monotone N_RN). 
          by apply/map_subset/history_monotone_bakes. }
      rewrite /= -(@cfb_non_empty_subset _ (block_history N_R)); last first.
      - apply/valid_chain_non_empty.
        move/allP/(_ b): (all_honest_block_cfb_valid N0N_R ffNR no_collR).
        by rewrite bin => /trueI. 
      - by apply/block_history_monotone. 
      - apply/(in_subset2 _ no_coll). apply/subset_trans; last by apply/subset_cons. 
        by apply/map_subset/history_monotone_bakes. 
        move=> /allP/(_ b') IH. rewrite -2!/(pos _ _).
        rewrite (progress_no_effect_pos Baked) eq_sym (progress_no_effect_pos Baked) eq_sym /pos.
      rewrite -(@cfb_non_empty_subset _ (block_history N_R)); last first.
      - apply/valid_chain_non_empty.
        move/allP/(_ b): (all_honest_block_cfb_valid N0N_R ffNR no_collR).
        by rewrite bin => /trueI. 
      - apply/block_history_monotone. 
        by apply/(big_step_trans N_RN NN'). 
      - by apply/(in_subset2 _ no_coll)/subset_cons. 
        move/ProgressB: (baking_steps_refl N') no_coll (uniq_exec_order N0N) b'in.
      elim: exec_order=> //= p ps +.
      set N'' := foldr _ _ _.
      move=> + /BakeStep bs. 
      move=> /(_ bs) + no_coll.
      apply: instant1.
      { apply/(in_subset2 _ no_coll)/subset_cons2.
        by apply/map_subset/history_monotone_bake. }
      move=> + /andP [] pnotps ups.
      rewrite ups=> /trueI {}IH.
      move: no_coll. 
      rewrite /party_bake_step_world /=.
      case state_p: (_.[? _])=> [l |]//=. 
      case corrupt_p : (~~_)=> //=. 
      (* Honest baker *)
      { rewrite /honest_bake /=.
        case win_p: Winner => //=. 
        move: state_p. 
        rewrite (no_state_change_bake_different_parties _ pnotps)=> state_p.
        move: win_p.
        move/(pk_preserved N0N): (state_p) -> => win_p. 
        rewrite honest_not_corrupt corrupt_p.
        set nb := MkBlock _ _ _ _. move=> no_coll.
        rewrite inE=> /orP [/eqP b'nb|]; last first.
        (* Not the new block *)
        - move=> b'in.
          rewrite eq_sym. 
          rewrite -(@cfb_non_empty_subset _ (block_history N'')); last first. 
          + apply/valid_chain_non_empty.
            move: (honest_valid_chain_bake N0N NN' ff bs ups).
            apply: instant1 => //.
            { by apply/(in_subset2 _ no_coll)/subset_cons2/subset_cons. }
            by move/allP/(_ b'); rewrite b'in=> /trueI. 
          + by apply/subset_cons. 
          + by apply/(in_subset2 _ no_coll)/subset_cons. 
          + by rewrite eq_sym; apply/IH. 
        (* The new block *)
        - rewrite b'nb.
          have ->: cfb nb (nb :: [seq get_block m | m <- history N''])
          = (nb :: (bestChain (t_now N'' - 1) (tree l))). 
          { apply/cfb_valid_chain'. 
            - by apply/(in_subset2 _ no_coll). 
            - move: (best_chain_valid (tree l) (t_now N'' - 1)).
              case bc: (bestChain (t_now N'' - 1) (tree l))=> //=.
              rewrite valid_chain_ext=> -> //=. rewrite win_p bc /= eq_refl.
              rewrite /= andbC /=. apply/(@leq_ltn_trans (t_now N'' -1)).
              + by apply/(@best_chain_time _ (tree l)); rewrite bc mem_head.
              + by rewrite subn1 ltn_predL baking_preserves_time; apply/lt_0_time.
                apply/subset_trans; first by apply/best_chain_in_all.
                apply/subset_trans; first by apply/filter_subset.
                apply/subset_trans; first
                  by apply/(subset_honest_tree N0N _ state_p); rewrite honest_not_corrupt corrupt_p.
                apply/subset_trans; first by apply/(honest_tree_hist_gb_subset N0N).
                apply/subset_cons2/subset_trans; last by apply/subset_cons.
                  by apply/map_subset/history_monotone_bakes. }
          case cfb_NR: cfb=> [|h c] //=. apply/orP. constructor. 
          apply/eqP. case=> H.
          have: |h :: c| <= | bestChain (t_now N'' - 1) (tree l) |. 
          { move=> {H}. rewrite -cfb_NR. 
            apply/best_chain_best. 
            - by apply/honest_block_cfb_valid.
            - move=> b'' b''in. rewrite mem_filter.
              apply/andP; constructor.
              + rewrite subn1. rewrite baking_preserves_time. apply/(@leq_trans (sl b)).
                * move: (honest_block_cfb_valid N0N_R ffNR no_collR bin).
                  rewrite cfb_NR. 
                  move: (@cfb_non_empty_starts_block b (block_history N_R)).
                  rewrite cfb_NR => /trueI [] c' [] <- _.
                  move: b''in. rewrite cfb_NR. rewrite inE => /orP [/eqP ->|] //=. 
                  clear. move=> b''in. rewrite/valid_chain=> /and3P [] _ _ .  
                  move/(order_path_min lt_slots_trans)/allP/(_ b'').
                  rewrite b''in=> /trueI H. by apply/ltnW. 
                * rewrite -(leq_add2r 1) 2!addn1. rewrite prednK //.
                  by apply/lt_0_time. 
              + move: b'' b''in.
                apply/(subset_trans (cfb_subset_honest_tree N0N_R ffNR no_collR bin)). 
                apply/(@honest_tree_subset N_R N p l)=> //.
                  by rewrite honest_not_corrupt.
          }
          by rewrite -H /= ltnn. 
      }
      (* Dishonest baker *)
      { case: (ff) => _ /(_ _ bs) /=. 
        case: AdversarialBake => //= mds _ /adv_broadcast_honest_block_history <- no_coll b'in. 
        move: (IH b'in)=> {}IH.
        rewrite eq_sym. 
        rewrite -(@cfb_non_empty_subset _ (block_history N'')); last first. 
        - apply/valid_chain_non_empty. 
          move: (honest_valid_chain_bake N0N NN' ff bs ups).
          apply: instant1. 
          { by apply/(in_subset2 _ no_coll)/subset_cons2/block_history_adv_broadcast_subset. }
            by move/allP/(_ b'); rewrite b'in=> /trueI.
        - by apply/block_history_adv_broadcast_subset.
        - by apply/(in_subset2 _ no_coll)/subset_cons.
        - by rewrite eq_sym. 
      }
    }
    (** It is baked in this round. **)
    rewrite baking_preserves_time=> /eqP slb.
    move: no_coll (uniq_exec_order N0N) bin. 
    move/ProgressB: (baking_steps_refl N'). 
    move: ssb. rewrite /super_slot. 
    move/permP: (perm_exec_order0 N0N) ->. 
    move: (all_parties_state N0N)=> /=. 
    elim: exec_order=> [|p ps] //=.
    set N'1 := foldr _ _ _.
    rewrite -/(block_history _) -/(block_history _)=> {}IH  /andP [] ep eall wc /BakeStep bs no_coll. 
    have/IH: {in GenesisBlock :: block_history N'1 &, injective HashB}. 
    { apply/(in_subset2 _ no_coll)/subset_cons2. 
        by apply/map_subset/history_monotone_bake. } 
    move=> + /andP [] pnotps ups.
    move/(_ eall)/(_ _ bs)/(_ ups)=> {}IH.
    move: no_coll.
    rewrite/party_bake_step_world.
    rewrite (no_state_change_bake_different_parties _ pnotps). 
    move: ep. rewrite /exists_state. 
    case state_p: (_.[? _]) => [l|] //= _.
    case corrupt_p: (~~_)=> //=.
    (* Honest baker *)
    + rewrite /honest_bake /=.
      move/(pk_preserved N0N): (state_p) ->.
      case win_sl: Winner => //=; last first.
      (* Not slow winner *)
      { move: wc. rewrite slb. move: win_sl.
        rewrite baking_preserves_time => -> /=.
        rewrite add0n -slb. 
          by move=> /IH {}IH no_coll /IH. }
      (* Slot winner *)
      set nb := MkBlock _ _ _ _. move=> no_coll.
      rewrite honest_not_corrupt corrupt_p /=. 
      have hbh_mem: honest_block_hist N =i honest_block_hist N'1. 
      { move: win_sl wc.
        rewrite baking_preserves_time slb honest_not_corrupt corrupt_p=> -> /=.
        case no_win: (count _ _)=> //= _.
        move: ff N0N ups bs no_win.
        clear. 
        rewrite /N'1=> {N'1} ff N0N.
        elim: ps=> //= p ps. set N'1 := foldr _ _ _. move=> + /andP [] pnotps ups /BakeStep bs.
        move/(_ ups bs)=> IH.
        rewrite /party_bake_step_world.
        case state_p: (_.[? _])=> //= [l |]; last case: (_ && _) => //=. 
        case corrupt_p: (~~_)=> //=. 
        - rewrite /honest_bake /= baking_preserves_time. 
          move: state_p . 
          rewrite no_state_change_bake_different_parties //. 
          move/(pk_preserved N0N) ->. case: Winner=> //=.
            by rewrite honest_not_corrupt corrupt_p.
        - rewrite honest_not_corrupt andbC corrupt_p /= add0n => /IH ->. 
          case: ff => _ /(_ _ bs) /=. 
          rewrite baking_preserves_time.
          case: AdversarialBake=> //= mdms _.
          by move/adv_broadcast_honest_block_history => ->. }
      rewrite inE => /orP [/eqP nbeq| bin]; last first. 
      { move/allP/(_ b): (no_premature_honest_blocks_D N0N ffN prog_N).
          by rewrite hbh_mem mem_filter /= honest_b bin slb ltnn => /trueI. }
      rewrite nbeq 2!eq_refl /=. 
      have ->: cfb nb (nb :: [seq get_block m | m <- history N'1]) = (nb :: (bestChain (t_now N'1 - 1) (tree l))). 
      { apply/cfb_valid_chain'. 
        - by apply/(in_subset2 _ no_coll). 
        - move: (best_chain_valid (tree l) (t_now N'1 - 1)).
          case bc: (bestChain (t_now N'1 - 1) (tree l))=> //=.
          rewrite valid_chain_ext=> -> //=. rewrite win_sl bc /= eq_refl.
          rewrite /= andbC /=. apply/(@leq_ltn_trans (t_now N'1 -1)).
          + by apply/(@best_chain_time _ (tree l)) ; rewrite bc mem_head.
          + by rewrite subn1 ltn_predL baking_preserves_time; apply/lt_0_time.
            apply/subset_trans; first by apply/best_chain_in_all.
            apply/subset_trans; first by apply/filter_subset.
            apply/subset_trans; first
              by apply/(subset_honest_tree N0N _ state_p); rewrite honest_not_corrupt corrupt_p.
            apply/subset_trans; first by apply/(honest_tree_hist_gb_subset N0N).
            apply/subset_cons2/subset_trans; last by apply/subset_cons.
              by apply/map_subset/history_monotone_bakes. }
      apply/allP=> b'. rewrite -hbh_mem=> b'in. apply/orP. constructor.
      move: (ready_before_delivered N0N prog_N)=> [] N_R [] N0N_R NR_N prog_NR.
      move: b'in. rewrite -(delivery_preserves_honest_block_hist' N0N_R) // => bin.
      move: (NR_N) => [] N_RN _.
      have ffNR : forging_free N_R by apply/(forging_free_prev _ ffN). 
      have no_collR: collision_free N_R. 
      { apply/(in_subset2 _ no_coll)/subset_cons2.
        apply/subset_trans; first by apply/(block_history_monotone N_RN). 
          apply/subset_trans; last by apply/subset_cons. 
            by apply/map_subset/history_monotone_bakes. }
      rewrite -(@cfb_non_empty_subset _ (block_history N_R)); last first. 
      * apply/valid_chain_non_empty. move/allP/(_ b'): (all_honest_block_cfb_valid N0N_R ffNR no_collR).
          by rewrite bin=> /trueI. 
      * apply/subset_trans; first by apply/(block_history_monotone N_RN). 
        apply/subset_trans; last by apply/subset_cons. 
          by apply/map_subset/history_monotone_bakes.
      * by apply/(in_subset2 _ no_coll)/subset_cons. 
      * case cfb_NR: cfb=> [|h c] //=. 
        apply/eqP. case=> H.
        have: |h :: c| <= | bestChain (t_now N'1 - 1) (tree l) |. 
        { move=> {H}. rewrite -cfb_NR.
          apply/best_chain_best.
          - by apply/honest_block_cfb_valid.
          - move=> b'' b''in. rewrite mem_filter.
            apply/andP; constructor.
            + rewrite subn1. rewrite baking_preserves_time. apply/(@leq_trans (sl b')).
              * move: (honest_block_cfb_valid N0N_R ffNR no_collR bin).
                rewrite cfb_NR.
                move: (@cfb_non_empty_starts_block b' (block_history N_R)).
                rewrite cfb_NR=> /trueI [] c' [] <- _.
                move: b''in. rewrite cfb_NR. rewrite inE => /orP [/eqP ->|] //=.
                clear. move=> b''in. rewrite/valid_chain=> /and3P [] _ _ .
                move/(order_path_min lt_slots_trans)/allP/(_ b'').
                rewrite b''in=> /trueI H. by apply/ltnW.
              * rewrite -(leq_add2r 1) 2!addn1. rewrite prednK //.
                -- move/allP/(_ b'): (no_premature_honest_blocks_R N0N_R ffNR prog_NR). 
                   rewrite bin=> /trueI. case: NR_N=> _. 
                   by rewrite add0n=> ->.
                -- by apply/lt_0_time.
            + move: b'' b''in.
              apply/(subset_trans (cfb_subset_honest_tree N0N_R ffNR no_collR bin)).
              apply/(@honest_tree_subset N_R N p l)=> //.
                by rewrite honest_not_corrupt. }
          by rewrite /= -H /= ltnn. 
    (* Dishonest baker *)
    + case: (ff) => _ /(_ _ bs) /=. 
      (* move/no_forging_bake: (bs).  *)
      rewrite -/N' -/N'1.
      case: AdversarialBake=> //= mds.
      rewrite /= => _ sub no_coll bin. 
      rewrite -/(honest_block_hist _). set N'' := flood_msgs_adv _ _. 
      have mem_eq: honest_block_hist N'' =i honest_block_hist N'1. 
      { move: sub. rewrite /N''. clear.   
        elim: mds=> //= [] [] m dm mds IH /=.
        case honest_m: is_honest => //= sub b.
        apply/idP/idP; last first.
        - rewrite inE orbC IH; first by move->.
          apply/subset_trans; last by apply/sub.
          by apply/subset_cons. 
        - rewrite inE=> /orP [/eqP ->|]; first by apply/sub; rewrite mem_head.
          rewrite IH //. apply/subset_trans; last by apply/sub.
            by apply/subset_cons. }
      move: wc. rewrite honest_not_corrupt andbC corrupt_p /= add0n => /IH {}IH. 
      rewrite (eq_all_r mem_eq). apply/allP=> b' b'in. move: (mem_eq b) IH.
      rewrite 2!mem_filter bin /= honest_b /= => /esym -> /trueI/allP/(_ b').
      rewrite b'in=> /trueI {}IH. 
      rewrite -(@cfb_non_empty_subset _ (block_history N'1)).
      rewrite -(@cfb_non_empty_subset _ (block_history N'1)) //.
      * by apply/(in_subset2 _ no_coll)/subset_cons.
      * by apply/block_history_adv_broadcast_subset.
      * apply/valid_chain_non_empty.
        move: (honest_valid_chain_bake N0N NN' ff bs ups).
        apply: instant1=> //.
        -- by apply/(in_subset2 _ no_coll)/subset_cons2/block_history_adv_broadcast_subset. 
        -- by move/allP/(_ b'); rewrite b'in=> /trueI.
      * by apply/(in_subset2 _ no_coll)/subset_cons.
      * by apply/block_history_adv_broadcast_subset.
      * apply/valid_chain_non_empty.
        move: (honest_valid_chain_bake N0N NN' ff bs ups).
        apply: instant1. 
        -- by apply/(in_subset2 _ no_coll)/subset_cons2/block_history_adv_broadcast_subset. 
        -- by move/allP/(_ b); rewrite -mem_eq mem_filter /= honest_b bin => /trueI.
  (* Inc *)
  - apply/IH=> //. 
    apply/(forging_free_prev _ ff).
      by do 2! econstructor.
  - apply/ff=> //. 
    apply/(forging_free_prev _ no_coll).
      by do 2! econstructor.
  - apply/ff=> //. 
    apply/(forging_free_prev _ no_coll).
      by do 2! econstructor.
Qed. 

Lemma hb_pos_gt_hb N b:
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  b \in honest_block_hist N ->
  all (fun b' => pos b' N < pos b N) [seq b' <- honest_block_hist N | sl b' < sl b].
Proof.
  move=> N0N. 
  elim: N0N=> //.
  move=> {}N N' [] // {N'} N prog_N N0N + ff no_coll.
  (* Delivery *)
  { have ffN : forging_free N.
    { by apply/(forging_free_prev _ ff); do 2! econstructor. }
    apply: instant2=> //.
    { apply/(in_subset2 _ no_coll)/subset_cons2.
        by apply/map_subset/history_monotone_deliverys. }
    move=> IH. 
    rewrite -delivery_preserves_honest_block_hist // => bin.
    apply/allP=> b'.
    rewrite mem_filter -delivery_preserves_honest_block_hist // => /andP [] slb b'in.
    have no_collN: collision_free N. 
    { apply/(in_subset2 _ no_coll)/subset_cons2.
      by apply/map_subset/history_monotone_deliverys. }
    rewrite /= -(@cfb_non_empty_subset _ (block_history N)) //; last first.
    - by apply/valid_chain_non_empty/honest_block_cfb_valid. 
    - by apply/map_subset/history_monotone_deliverys.
    - by apply/(in_subset2 _ no_coll)/subset_cons.
    - rewrite -(@cfb_non_empty_subset _ (block_history N)) //; last first.
      + by apply/valid_chain_non_empty/honest_block_cfb_valid.
      + by apply/map_subset/history_monotone_deliverys.
      + by apply/(in_subset2 _ no_coll)/subset_cons.
      + by move/allP/(_ b'): (IH bin); rewrite mem_filter slb b'in => /trueI. }
  (* Baking *)
  {  have ffN : forging_free N.
     { by apply/(forging_free_prev _ ff); do 2! econstructor. }
     apply: instant2=> //.
    { apply/(in_subset2 _ no_coll)/subset_cons2.
        by apply/map_subset/history_monotone_bakes. }
    move=> IH.
    set N' := _[[progress := _]].
    have NN': N ⇓ N' by do 2! econstructor.
    move=> binh.
    move: (binh); rewrite /= mem_filter => /andP [] honest_b bin.
    move/allP/(_ b): (no_premature_honest_blocks (big_step_trans N0N NN') ff)=> /=.
    (* We test if it is a block baked in this round or not. *)
    rewrite mem_filter honest_b bin leq_eqVlt => /trueI/orP []; last first.
    (* Earlier block *)
    { rewrite baking_preserves_time=> slb.
      apply/allP=> b'. 
      rewrite 2!mem_filter=> /and3P [] slb' honest_b' b'in.
      move/(_ b'): (honest_blocks_below_slot_preserved N0N NN' ff).
      move/esym. 
      rewrite 2!mem_filter /= b'in honest_b' (ltn_trans slb' slb) /= => /esym.
      rewrite 2!mem_filter => /and3P [] _ {}b'in {}honest_b'. 
      have no_collN: collision_free N. 
      { apply/(in_subset2 _ no_coll)/subset_cons2.
          by apply/map_subset/history_monotone_bakes. }
      rewrite -(@cfb_non_empty_subset _ (block_history N)) //; last first.
      - apply/valid_chain_non_empty/honest_block_cfb_valid => //. 
          by rewrite mem_filter honest_b'/= b'in. 
      - by apply/map_subset/history_monotone_bakes.
      - by apply/(in_subset2 _ no_coll)/subset_cons. 
      - move/(_ b): (honest_blocks_below_slot_preserved N0N NN' ff).
        rewrite 4!mem_filter slb /= honest_b bin /= => {}bin. 
        rewrite -(@cfb_non_empty_subset _ (block_history N)) //; last first.
      - apply/valid_chain_non_empty/honest_block_cfb_valid => //.
          by rewrite mem_filter /= honest_b bin. 
      - by apply/map_subset/history_monotone_bakes.
      - by apply/(in_subset2 _ no_coll)/subset_cons. 
      - move: IH. rewrite /= mem_filter honest_b bin => /trueI /allP/(_ b').
          by rewrite !mem_filter /= b'in honest_b' slb' => /trueI. }
    (* Block is baked in this round *)
    { rewrite baking_preserves_time => /eqP tn.
      apply/allP=> b'. rewrite 2!mem_filter => /and3P [] slb' honest_b' b'in.
      move/(_ b'): (honest_blocks_below_slot_preserved N0N NN' ff). 
      rewrite !mem_filter /= honest_b' -tn slb' /= b'in => {}b'in. 
      move: ff. set N2 := _[[_:=_]]. rewrite /N2=> ff.  
      move/ProgressB: (baking_steps_refl N2) no_coll (uniq_exec_order N0N) bin.
      rewrite /N'=> {NN' N' binh}.
      elim: exec_order=> //= [| p ps].
      (* BC *)
      { move=> _ _ _ bin. move: IH. rewrite /= mem_filter honest_b bin => /trueI/allP/(_ b').
          by rewrite 2!mem_filter b'in honest_b' slb'=> /trueI. }
      (* IH *)
      set N' := foldr _ _ _.
      move=> + /BakeStep bs no_coll /andP [] pnotps ups.
      move/(_ bs).
      apply: instant1; first 
        by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_bake. 
      move: no_coll =>+ /(_ ups) {}IH.
      rewrite /party_bake_step_world=> /=.
      case state_p: (_.[? _])=> [l|] //=.
      case corrupt_p: (~~_)=> //=.
      (* Honest baker *)
      { rewrite /honest_bake /=.
        move: state_p. rewrite (no_state_change_bake_different_parties _ pnotps)=> state_p. 
        rewrite (pk_preserved N0N state_p) baking_preserves_time. 
        case win_p: Winner => //=.
        set nb := MkBlock _ _ _ _. move=> no_coll.
        rewrite inE=> /orP [/eqP nbeq | bin]. 
        - rewrite nbeq.
          (* We establish the new chain *)
          have ->: cfb nb (nb :: [seq get_block m | m <- history N']) = (nb :: (bestChain (t_now N - 1) (tree l))). 
          { apply/cfb_valid_chain'. 
            - by apply/(in_subset2 _ no_coll). 
            - move: (best_chain_valid (tree l) (t_now N - 1)).
              case bc: (bestChain (t_now N - 1) (tree l))=> //=.
              rewrite valid_chain_ext=> -> //=. rewrite win_p bc /= eq_refl.
              rewrite /= andbC /=. apply/(@leq_ltn_trans (t_now N' -1)).
              + rewrite baking_preserves_time.
                  by apply/(@best_chain_time _ (tree l)); rewrite bc mem_head.
              + by rewrite baking_preserves_time subn1 ltn_predL; apply/lt_0_time.
                apply/subset_trans; first by apply/best_chain_in_all.
                apply/subset_trans; first by apply/filter_subset.
                apply/subset_trans; first
                  by apply/(subset_honest_tree N0N _ state_p); rewrite honest_not_corrupt corrupt_p.
                apply/subset_trans; first by apply/(honest_tree_hist_gb_subset N0N).
                apply/subset_cons2/subset_trans; last by apply/subset_cons.
                  by apply/map_subset/history_monotone_bakes. }
          (* We establish that the chain from b' must have been
                 known in some earlier Ready state *)
          move: (ready_before_delivered N0N prog_N)=> [] N_R [] N0N_R NR_N prog_NR.
          move: (delivery_preserves_honest_block_hist' N0N_R prog_NR NR_N ffN prog_N).
          move/(_ b'). rewrite 2!mem_filter /= honest_b' b'in /= => b'inNR.
          rewrite -addn1 -[|_|.+1]addn1 leq_add2r.

          have ffNR : forging_free N_R by apply/(forging_free_prev _ ffN); case: NR_N. 
          have no_collR: collision_free N_R. 
          { apply/(in_subset2 _ no_coll)/subset_cons2.
            case: NR_N => N_RN _. 
            apply/subset_trans; first by apply/(block_history_monotone N_RN). 
            apply/subset_trans; last by apply/subset_cons. 
              by apply/map_subset/history_monotone_bakes. }
          rewrite -(@cfb_non_empty_subset _ (block_history N_R)); last first.
          + apply/valid_chain_non_empty/honest_block_cfb_valid=> //.
              by rewrite mem_filter /= honest_b' b'inNR. 
          + apply/subset_trans; last by apply/subset_cons.
            apply/subset_trans; last by apply/map_subset/history_monotone_bakes. 
              by apply/map_subset/history_monotone; case: NR_N. 
          + apply/(in_subset2 _ no_coll)/subset_cons.
          + apply/best_chain_best=> //. 
            * apply/honest_block_cfb_valid=> //.
                by rewrite mem_filter /= honest_b' b'inNR. 
            * move=> b'' b''in. rewrite mem_filter.
              apply/andP; constructor.
              -- rewrite -(leq_add2r 1) 2!addn1 subn1 prednK; last by apply/lt_0_time. 
                 move: (@honest_block_cfb_valid _ b' N0N_R ffNR no_collR).
                 rewrite mem_filter /= honest_b' b'inNR => /trueI.
                 move: (@cfb_non_empty_starts_block b' (block_history N_R)) b''in.
                 case: cfb=> //= x xs /trueI [] ? [] -> _.
                 rewrite inE=> /orP [/eqP -> _| b''in]; rewrite -tn //.  
                 move=> /and3P [] _ _ /(order_path_min lt_slots_trans)/allP/(_ b'' b''in) lt. 
                   by apply/(ltn_trans lt). 
              -- apply/(honest_tree_subset N0N_R _ prog_NR prog_N NR_N state_p).
                 ++ by rewrite honest_not_corrupt.
                 ++ apply/(cfb_subset_honest_tree N0N_R ffNR no_collR _ b''in).
                      by rewrite mem_filter /= honest_b' b'inNR. 
        - have NN2: N ⇓ N2 by do 2! econstructor. 
          rewrite -(@cfb_non_empty_subset _ (block_history N')).
          rewrite -(@cfb_non_empty_subset _ (block_history N')).
          + by apply/IH. 
          + by apply/(in_subset2 _ no_coll)/subset_cons.
          + by apply/subset_cons.
          + apply/valid_chain_non_empty.
            move: (honest_valid_chain_bake N0N NN2 ff bs ups).
            apply: instant1. 
            * by apply/(in_subset2 _ no_coll)/subset_cons2/subset_cons.
            * by move/allP/(_ b); rewrite mem_filter /= honest_b bin=> /trueI.
          + by apply/(in_subset2 _ no_coll)/subset_cons.
          + by apply/subset_cons. 
          + apply/valid_chain_non_empty.
            move: (honest_valid_chain_bake N0N NN2 ff bs ups).
            apply: instant1=> //.
            * by apply/(in_subset2 _ no_coll)/subset_cons2/subset_cons.
            * move/allP/(_ b'); rewrite mem_filter /= honest_b' /=.
                by apply: instant1; [apply/map_subset; [apply/history_monotone_bakes|] |]. }
      (* Dishonest baker *)
      { have NN2: N ⇓ N2 by do 2! econstructor. 
        case: (ff) => _ /(_ _ bs) /=. 
        rewrite baking_preserves_time.
        case: AdversarialBake => //= mdms _.
        move/adv_broadcast_honest_block_history=> + no_coll bin.
        move/(_ b). rewrite 2!mem_filter /= honest_b bin /= => {}bin. 
        move: (IH bin)=> {}IH. 
        rewrite -(@cfb_non_empty_subset _ (block_history N')).
        rewrite -(@cfb_non_empty_subset _ (block_history N'))=> //.
        + by apply/(in_subset2 _ no_coll)/subset_cons.
        + by apply/block_history_adv_broadcast_subset.
        + apply/valid_chain_non_empty.
          move: (honest_valid_chain_bake N0N NN2 ff bs ups).
          apply: instant1. 
          * by apply/(in_subset2 _ no_coll)/subset_cons2/block_history_adv_broadcast_subset. 
          * by move/allP/(_ b); rewrite mem_filter/= honest_b bin=> /trueI.
        + by apply/(in_subset2 _ no_coll)/subset_cons.
        + by apply/block_history_adv_broadcast_subset.
        + apply/valid_chain_non_empty.
          move: (honest_valid_chain_bake N0N NN2 ff bs ups).
          apply: instant1=> //.
          * by apply/(in_subset2 _ no_coll)/subset_cons2/block_history_adv_broadcast_subset.
          * move/allP/(_ b'); rewrite mem_filter /= honest_b' /=.
              by apply: instant1; [apply/map_subset; [apply/history_monotone_bakes|] |]. }}}
  (* Inc *)
  { move=> IH. apply/IH=> //.
    apply/(forging_free_prev _ ff).
      by do 2! econstructor. }
  (* Perms *)
  - move=> ??. apply/ff=> //. 
    apply/(forging_free_prev _ no_coll).
      by do 2! econstructor.
  - move=> ??. apply/ff=> //. 
    apply/(forging_free_prev _ no_coll).
      by do 2! econstructor.
Qed. 

Lemma cfb_gb bp : cfb GenesisBlock bp = [:: GenesisBlock]. 
Proof. by simp cfb; rewrite eq_refl. Qed. 

Lemma hb_pos_gt_hb_gb N b:
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  b \in honest_block_hist_gb N ->
  all (fun b' => pos b' N < pos b N) [seq b' <- honest_block_hist_gb N | sl b' < sl b].
Proof.
  move=> N0N ff /= no_coll.
  rewrite HonestGB inE => /orP [/eqP ->|]; first by apply/allP=> ?; rewrite GenesisSlot mem_filter ltn0 => /andP [].
  move=> bin. apply/allP=> b'.
  rewrite mem_filter inE=> /andP [] slb /orP [/eqP b'eqGB| b'in]; last first.
  { move/allP/(_ b'): (hb_pos_gt_hb N0N ff no_coll bin).
      by rewrite mem_filter slb b'in=> /trueI. }
  move: b'eqGB slb=> ->. rewrite GenesisSlot=> slb.
  move: ff no_coll bin.
  elim: N0N=> // {}N N' // [] // {N'}N prog_N N0N + ff no_coll. 
  (* Delivery *)
  { have ffN : forging_free N.
    { by apply/(forging_free_prev _ ff); do 2! econstructor. }
    apply: instant2=> //.
    { apply/(in_subset2 _ no_coll)/subset_cons2.
        by apply/map_subset/history_monotone_deliverys. }
    rewrite 2!cfb_gb=> IH. 
    rewrite -delivery_preserves_honest_block_hist //.
    rewrite mem_filter => /andP [] /= hb bin.
    have no_collN: collision_free N. 
    { apply/(in_subset2 _ no_coll)/subset_cons2.
        by apply/map_subset/history_monotone_deliverys. }
    rewrite -(@cfb_non_empty_subset _ (block_history N)) //; last first.
    - apply/valid_chain_non_empty. 
      apply/honest_block_cfb_valid=> //.
        by rewrite mem_filter /= hb bin. 
    - by apply/map_subset/history_monotone_deliverys.
    - by apply/(in_subset2 _ no_coll)/subset_cons.
    - by apply/IH; rewrite mem_filter hb bin. }
  (* Baking *)
  { have ffN : forging_free N.
    { by apply/(forging_free_prev _ ff); do 2! econstructor. }
    apply: instant2=> //.
    { apply/(in_subset2 _ no_coll)/subset_cons2.
        by apply/map_subset/history_monotone_bakes. }
    rewrite 2!cfb_gb=> IH.
    move: ff. set N2 := _[[_:=_]]. rewrite /N2.  move=> ff.
    have NN2: N ⇓ N2 by do 2! econstructor. 
    move/ProgressB: (baking_steps_refl N2) no_coll (uniq_exec_order N0N). 
    elim: exec_order=> [|p ps] //=.
    set N' := foldr _ _ _.
    move=> + /BakeStep bs no_coll /andP [] pnotps ups.
    apply: instant1 => //.
    apply: instant1; first by 
        apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_bake.
    apply: instant1 => // {}IH.
    move: no_coll.
    rewrite /party_bake_step_world.
    case state_p: (_.[? _])=> [l|] //=. 
    case corrupt_p : (~~_)=> //=.
    (* Honest case *)
    { rewrite /honest_bake /=.
      rewrite baking_preserves_time.
      move: state_p. rewrite no_state_change_bake_different_parties // => state_p. 
      move: (pk_preserved N0N state_p) ->. 
      case win_p: Winner => //=.
      rewrite honest_not_corrupt corrupt_p.
      set nb := MkBlock _ _ _ _. move=> no_coll.
      rewrite inE => /orP [/eqP| bin]; last first.
      (* Not the new block (IH) *)
      { rewrite -(@cfb_non_empty_subset _ (block_history N')) //; last first.
        - apply/valid_chain_non_empty. 
          move: (honest_valid_chain_bake N0N NN2 ff bs ups).
          apply: instant1=> //; first by apply/(in_subset2 _ no_coll)/subset_cons2/subset_cons. 
          by move/allP/(_ b bin). 
        - by apply/subset_cons.
        - by apply/(in_subset2 _ no_coll)/subset_cons. 
        - by apply/IH. }
      (* The new block *)
      move=> nbeq. rewrite nbeq. 
      have ->: cfb nb (nb :: [seq get_block m | m <- history N']) = (nb :: (bestChain (t_now N' - 1) (tree l))). 
      { apply/cfb_valid_chain'. 
        - by apply/(in_subset2 _ no_coll). 
        - move: (best_chain_valid (tree l) (t_now N' - 1)).
          case bc: (bestChain (t_now N' - 1) (tree l))=> //=.
          rewrite valid_chain_ext=> -> //=. rewrite win_p.
          move: (bc). rewrite baking_preserves_time=> -> /=.
          rewrite eq_refl.
          rewrite /= andbC /=. apply/(@leq_ltn_trans (t_now N' -1)).
          + by apply/(@best_chain_time _ (tree l)); rewrite bc mem_head.
          + rewrite subn1 baking_preserves_time ltn_predL; apply/lt_0_time=> //.
            apply/subset_trans; first by apply/best_chain_in_all.
            apply/subset_trans; first by apply/filter_subset.
            apply/subset_trans; first
              by apply/(subset_honest_tree N0N _ state_p); rewrite honest_not_corrupt corrupt_p.
            apply/subset_trans; first by apply/(honest_tree_hist_gb_subset N0N).
            apply/subset_cons2/subset_trans; last by apply/subset_cons.
              by apply/map_subset/history_monotone_bakes. }
      move=> /=. rewrite -addn1 -[|_|.+1]addn1. 
      rewrite leq_add2r baking_preserves_time.
      rewrite lt0n size_eq0. move: (@best_chain_valid _ (tree l) (t_now N -1)).
      by case: (bestChain _ _). }
    (* Dishonest case *)
    { case: (ff) => _ /(_ _ bs) /=.
      rewrite baking_preserves_time.
      case: AdversarialBake=> //= mds _.
      move/adv_broadcast_honest_block_history <- => no_coll.
      move=> bin.
      rewrite -(@cfb_non_empty_subset _ (block_history N')) //; last first.
      - apply/valid_chain_non_empty. move: (honest_valid_chain_bake N0N NN2 ff bs ups).
        apply: instant1=> //=.
        + by apply/(in_subset2 _ no_coll)/subset_cons2/block_history_adv_broadcast_subset. 
        + by move/allP/(_ b bin). 
      - by apply/block_history_adv_broadcast_subset.
      - by apply/(in_subset2 _ no_coll)/subset_cons.
      - by apply/IH. }
    }
    { move=> IH. apply/IH=> //.
    apply/(forging_free_prev _ ff).
      by do 2! econstructor. }
  (* Perms *)
  - move=> ??. apply/ff=> //. 
    apply/(forging_free_prev _ no_coll).
      by do 2! econstructor.
  - move=> ??. apply/ff=> //. 
    apply/(forging_free_prev _ no_coll).
      by do 2! econstructor.
Qed.     

Lemma unique_sb_pos N:
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  uniq [seq pos b N | b <- super_blocks_world N].
Proof.
  move=> N0N ff no_coll.
  move: (no_honest_pos_share_sb N0N ff no_coll). 
  rewrite/super_blocks_world /=.
  set bh := {2 3 5} (block_history _). 
  elim: block_history=> // b bs IH.
  move=> H. 
  have: uniq [seq pos b N | b <- undup [seq b <- bs | is_honest (bid b) & super_slot (sl b)] ]. 
  { apply/IH.
    move=> b' H'. move: H. move/(_ b'). move=> /=. case: (_ &&_)/andP; last first.
    - move=> ?. rewrite H'=> /trueI. by case: is_honest=> //= /andP [] //. 
    - case=> -> ? /=. case: (b \in [seq b0 <- bs | is_honest (bid b0) & super_slot (sl b0)]) => //=.
      + by rewrite H'=> /trueI/andP []. 
      + by rewrite inE H' orbC /= => /trueI/andP []. }
  move=> /=. 
  case honest_b: is_honest=> //=. case sslb: super_slot=> //=; last first.
  case bin: (_ \in _)=> //= ->. rewrite andbC /=.
  apply/mapP=> [] [] b' b'in poseq. move: (H b')=> /=.
  rewrite honest_b sslb /= bin poseq inE b'in orbC eq_refl /==> /trueI /andP [] /eqP beq. 
  move: b'in. by rewrite mem_undup beq bin. 
Qed. 

Lemma iota_rcons: forall m n, rcons (iota n m) (m + n) = n :: iota n.+1 m. 
Proof.
  elim=> //= m IH n. apply/f_equal.
  by rewrite -IH addSnnS. 
Qed.                  

Lemma cfb_map_iota c bp:
  {in GenesisBlock :: bp &, injective HashB} ->
  valid_chain c ->
  {subset c <= GenesisBlock:: bp} ->
  [seq |cfb b bp| | b <- c] = rev (iota 1 (|c|)). 
Proof.
  move=> no_coll. elim: c => //= b c. 
  case ceq: c=> //= [|b' c']. 
  - move=> _ /valid_chain_block_gb -> _ /=.
    rewrite rev_cons /=.
    by simp cfb; rewrite eq_refl /=. 
  - move=> IH vc_b. move: (vc_b). rewrite valid_chain_ext=> /and4P [] _ _ _ /IH + sub.
    apply: instant1=> [| ->]; first by apply/(subset_trans _ sub)/subset_cons. 
    have ->: |cfb b bp| = |c'| + 2.
    { rewrite (@cfb_valid_chain' b bp (b' :: c')) //=.
      - by rewrite addn2. 
      - by apply/(subset_trans _ sub)/subset_cons. }
    rewrite -rev_rcons rcons_cons. apply/f_equal.
    by apply/f_equal/iota_rcons.
Qed. 

(** *Common Prefix*)

Lemma rewind_one_step_ready N:
  N0 ⇓^+ N ->
  exists N', [/\ N0 ⇓ N', N' ⇓ N, N' @ Ready & t_now N' = t_now N-1 ]. 
Proof.
  case. elim=> //= ?? [] {}N prog_N //.
  - move=> N0N IH.
    rewrite delivery_preserves_time=> /IH [] N' [] ????. 
    exists N'; constructor; try done. 
    econstructor. constructor; try done. done. 
  - move=> N0N IH.
    rewrite baking_preserves_time=> /IH [] N' [] ????. 
    exists N'; constructor; try done. 
    econstructor. constructor; try done. done. 
  - move=> N0N _ _.
    move: (delivered_before_baked N0N prog_N)=> [] N_D [] N0N_D [] N_DN.
    rewrite add0n => tD prog_ND.
    move: (ready_before_delivered N0N_D prog_ND)=> [] N_R [] N0N_R [] N_RN.
    rewrite add0n => tR prog_NR.
    exists N_R; constructor; try done.
    + apply/(big_step_trans N_RN). 
      apply/(big_step_trans N_DN). 
      econstructor. constructor; try done.
        by constructor. 
    + by rewrite subn1 /= tR tD. 
  - move=> pq N0N IH /IH [] N' [] ????. 
    exists N'; constructor; try done. 
    econstructor. constructor; try done. done. 
  - move=> pq N0N IH /IH [] N' [] ????. 
    exists N'; constructor; try done. 
    econstructor. constructor; try done. done. 
Qed. 

(** ** Pruning *)

Definition prune_time t (c : Chain) := [seq b <- c | sl b <= t].  

Arguments prune_time _ _ /.

Lemma or_rIl (A : bool) (B : Prop) : (~~ A -> B) -> A \/ B. 
Proof.
  case: A=> //=.
  - by move=> _; constructor.
  - by move/trueI => ?; constructor 2. 
Qed. 

Lemma lcs_vcs_non_empty c c' :
  valid_chain c ->
  valid_chain c' ->
  lcs c c' != [::]. 
Proof.
    by move=> vc vc'; move/suffixP: (suffix_gb_lcs_vcs vc vc')=> [] [| >] //= <-.
Qed.

Lemma lcs_vcs_valid c c' :
  valid_chain c ->
  valid_chain c' ->
  valid_chain (lcs c c'). 
Proof.
  move=> vc vc'. move: (vc) (vc'). 
  move/andP: (lcs_suffix c c')=> [] + _.
  move/suffixP=> [] bs H. 
  rewrite -{1}H. move: (lcs_vcs_non_empty vc vc'). 
  by case: lcs=> //= > _ /valid_chain_short_l. 
Qed. 

Lemma sorted_max b bs bs': sorted lt_slots (bs' ++ b :: bs) -> all (lt_slots^~ b) bs'. 
Proof.
  elim: bs' => //= > IH H. rewrite IH. 
  - move/(order_path_min lt_slots_trans)/allP/(_ b): H.
    by rewrite mem_cat orbC mem_head =>/trueI ->. 
  - by move/path_sorted: H.   
Qed. 

Lemma prune_sorted b k bs :
  sl b <= k -> 
  sorted lt_slots (b :: bs) ->
  prune_time k (b :: bs) = b :: bs.
Proof.
  move=> le /(order_path_min lt_slots_trans)/allP /=.
  rewrite le=> H. apply/f_equal. elim: bs H=> //= b' bs IH H.
  rewrite IH; last by apply/(in_subset1 _ H)/subset_cons. 
  move: (H b'). rewrite mem_head=> /trueI. rewrite /lt_slots=> H'.
  suff ->: (sl b' <= k) by done.
  by apply/(leq_trans _ le); rewrite ltnW. 
Qed. 

Lemma prune_time_suffix k c:  sorted lt_slots c -> prune_time k c ⪯ c. 
Proof.
  elim: c => //b bs IH H. 
  case bklt: ((sl b) <= k). 
  - by rewrite prune_sorted //; apply/suffix_refl.  
  - move=> /=. rewrite bklt orbC IH //.
    by move/path_sorted: H. 
Qed. 

Lemma cp_lemma_gen_inc a N p1 l1 c:
  let bc1 := bestChain (t_now N - 1) (tree l1) in
  {subset c <= [seq b <- block_hist_gb N| sl b <= t_now N-1 + a]} ->
  valid_chain c ->
  |bc1| <= |c| ->
  let b := head GenesisBlock (lcs bc1 c)in
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  is_honest p1 ->
  has_state p1 N l1 ->
  exists t,
    t <= sl b /\
    |super_slots_range (t + 1) (t_now N -1)| <=
    2 * | adv_slots_range (t + 1) (t_now N + a)|.
Proof.
  move=> bc1 sub vc bclt.
  set cs := lcs _ _. move=>b N0N ff no_coll honest_p1 state_p1.
  (** We define [b'] to be the first honest block in the stem. **)
  set b' := findo honest_block cs.
  have/findoP: isSome b'.
  { rewrite /b' /cs. move: (@suffix_gb_lcs_vcs bc1 c).
    move/(_ (best_chain_valid _ _)). rewrite vc=> /trueI. move=> /suffixP [] c' <-.
      by elim: c' => //= [|> ?]; [rewrite HonestGB | case: is_honest]. }
  move=> [] cs1 [] cs2 [] {} b' [] cs_layout [] honest_b' honest_cs1.
  (** We choose [sl b'] as our time suggestion. **)
  exists (sl b'). constructor.
  { rewrite /b. move: (best_chain_valid (tree l1) (t_now N -1)).
    move/andP: (lcs_suffix bc1 c) => [] /suffixP [] uc1.
    rewrite -/bc1 -/cs -cs_layout => <- _. clear.
    case: cs1 => //= > /valid_chain_short_l /andP [] _ /andP [] _.
    move/(order_path_min lt_slots_trans)/allP/(_ b').
    by rewrite mem_cat orbC mem_head /= => /trueI /ltnW. }
  (* Let us be explicit about the layout of chains, and record a few *)
  (* usefull facts.  **)
  move: (lcs_suffix bc1 c)=> /andP [] /suffixP [] c1 bc1_layout.
  move=> /suffixP [] c2 c_layout.
  move: (best_chain_valid (tree l1) (t_now N -1)).
  rewrite -/bc1 -bc1_layout -/cs -cs_layout cat1s => /and3P [] corr1 lk1 dec1.
  move: (vc).
  rewrite -c_layout -/cs -cs_layout cat1s => /and3P [] corr2 lk2 dec2.
  (* We now show that each dishonest winning slot maximally can be *)
  (* used once in each branch. *)
  pose abs c := [seq b <- c |corrupt_block b].
  apply/(@leq_trans (|cs1| + |abs c1| + |abs c2|)); last first.
  { have tN : 0 < t_now N by apply/lt_0_time.
    rewrite /= (@p_slots_range_split _ _ (sl b + 1) _); last first.
    - apply/andP; constructor.
      + rewrite 2!addn1 ltnS /b.
        move: dec1. rewrite -cs_layout=> /sorted_cat/andP [] _.
        clear. case: cs1=> //= ?? /(order_path_min lt_slots_trans).
        by move/allP/(_ b'); rewrite mem_cat mem_head orbC => /trueI /ltnW.
      + rewrite addn1 -(@prednK (t_now N)) //.
        rewrite prednK /b //.
        apply/leq_trans; last by apply/leq_addr.
        move: (@best_chain_time _ (tree l1) (t_now N -1)).
        rewrite -/bc1 -bc1_layout -/cs -cs_layout cat1s. move: tN. clear. move=> tN.
        case: cs1=> //= [| b'' ?].
        * move/(_ b'); rewrite mem_cat mem_head orbC /= => /trueI H.
          apply/(leq_ltn_trans H).
          by rewrite subn1 ltn_predL //.
        * move/(_ b''); rewrite mem_cat mem_head orbC /= => /trueI H.
          apply/(leq_ltn_trans H).
            by rewrite subn1 ltn_predL //.
    - rewrite size_cat mulnDr -addnA leq_add //.
      + rewrite mulSn mul1n -[|_|]add0n leq_add //.
        rewrite -(@size_map _ _ sl).
        apply/uniq_leq_size.
        * move: dec1.
          rewrite /= sorted_blocks_slots => /(sorted_uniq gtn_trans gtn_irr).
          by rewrite !map_cat 2!cat_uniq=> /and4P [].
        * move=> t /mapP [] b'' b''in ->.
          rewrite /p_slots_range.
          rewrite mem_filter. apply/andP; constructor.
          -- rewrite /adv_slot /adv_slot_gen. apply/hasP.
             exists (bid b''); [by apply/party_party|].
             move: corr1. rewrite /correct_blocks 2!all_cat=> /and3P [] _.
             move/allP/(_ _ b''in). rewrite /correct_block=> -> _ /=.
             move/allP/(_ _ b''in): honest_cs1=> //=.
               by rewrite honest_not_corrupt => /negbNE.
          -- rewrite /nat_range mem_iota subnKC.
             ++ rewrite 2!addn1 /b -cs_layout.
                move: b''in dec1; clear. case: cs1=> //= ?? b''in.
                move/sorted_cat/andP=> [] _ so.
                apply/andP; constructor.
                ** move/inP: b''in so => [] ? [] ? H.
                   rewrite -cat1s catA cat1s H -catA.
                   move/sorted_cat/andP => [] _ /(order_path_min lt_slots_trans).
                   rewrite -/cat => /allP /(_ b').
                     by rewrite mem_cat mem_head orbC /= => /trueI.
                ** move/inP: b''in so => [] s [] ? H.
                   rewrite -cat1s catA cat1s H -catA.
                   move: H. case: s=> //=; [by case=> -> _ _; apply/ltnSn|].
                   move=> ??. case=> -> _ /(order_path_min lt_slots_trans)/allP/(_ b'').
                   rewrite mem_cat mem_head orbC /= => /trueI H.
                     by apply/ltn_trans; [|apply/ltnSn].
             ++ rewrite 2!addn1 ltnS /b -cs_layout. move: dec1.
                clear. case: cs1 => //= > /sorted_cat /andP [] _.
                move/(order_path_min lt_slots_trans)/allP/(_ b').
                  by rewrite mem_cat mem_head orbC=> /trueI /ltnW.
      + rewrite mulSn mul1n leq_add //.
        * rewrite -(@size_map _ _ sl). apply/uniq_leq_size.
          -- move/sorted_cat: dec1=> /andP [].
             rewrite sorted_blocks_slots=> /(sorted_uniq gtn_trans gtn_irr) /subseq_uniq -> //.
               by rewrite map_subseq // filter_subseq.
          -- move=> t. move/mapP=> [] b'' + ->.
             rewrite 2!mem_filter=> /andP [] honest_b'' b''in.
             rewrite /adv_slot /adv_slot_gen. apply/andP; constructor.
             ++ apply/hasP. exists (bid b''); [by apply/party_party|].
                rewrite andbC. move: honest_b''. rewrite /corrupt_block => -> /=.
                move: corr1. rewrite /correct_blocks all_cat=> /andP [] /allP.
                  by move/(_ _ b''in).
             ++ rewrite mem_iota addn1. apply/andP;constructor.
                ** rewrite /b -cs_layout. move/inP: b''in dec1=> []?[]? ->.
                   rewrite -catA=> /sorted_cat/andP [] _ /(order_path_min lt_slots_trans).
                   rewrite -/cat=> /allP. clear. case: cs1=> //=.
                   --- by move/(_ b'); rewrite mem_cat mem_head orbC /= => /trueI.
                   --- by move=> b''' ? /(_ b'''); rewrite mem_cat mem_head orbC /= => /trueI.
                ** rewrite subnKC.
                   --- move: (@best_chain_time _ (tree l1) (t_now N -1)).
                       rewrite -/bc1 -bc1_layout => /(_ b'').
                       rewrite mem_cat b''in => /trueI H.
                       apply/(leq_ltn_trans H).
                       rewrite subn1.
                       apply/ltn_addr.
                       by apply/(@leq_trans (t_now N)); [rewrite ltn_predL; apply/lt_0_time|].
                   --- apply/ltn_addr.
                       apply/(@ltn_leq_trans (t_now N)); last done.
                       apply/(@leq_ltn_trans (t_now N -1)); last by rewrite subn1 ltn_predL; apply/lt_0_time.
                       apply/(@best_chain_time _ (tree l1)).
                       rewrite -/bc1 -bc1_layout -/cs. rewrite mem_cat.
                       apply/orP. constructor 2. rewrite /b -cs_layout.
                       clear. case: cs1=> //= [| >]; by rewrite mem_head.
        * rewrite -(@size_map _ _ sl). apply/uniq_leq_size.
          -- move/sorted_cat: dec2=> /andP [].
             rewrite sorted_blocks_slots=> /(sorted_uniq gtn_trans gtn_irr) /subseq_uniq -> //.
               by rewrite map_subseq // filter_subseq.
          -- move=> t. move/mapP=> [] b'' + ->.
             rewrite 2!mem_filter=> /andP [] honest_b'' b''in.
             rewrite /adv_slot /adv_slot_gen. apply/andP; constructor.
             ++ apply/hasP. exists (bid b''); [by apply/party_party|].
                rewrite andbC. move: honest_b''. rewrite /corrupt_block => -> /=.
                move: corr2. rewrite /correct_blocks all_cat=> /andP [] /allP.
                  by move/(_ _ b''in).
             ++ rewrite mem_iota addn1. apply/andP;constructor.
                ** rewrite /b -cs_layout. move/inP: b''in dec2=> []?[]? ->.
                   rewrite -catA=> /sorted_cat/andP [] _ /(order_path_min lt_slots_trans).
                   rewrite -/cat=> /allP. clear. case: cs1=> //=.
                   --- by move/(_ b'); rewrite mem_cat mem_head orbC /= => /trueI.
                   --- by move=> b''' ? /(_ b'''); rewrite mem_cat mem_head orbC /= => /trueI.
                ** rewrite subnKC.
                   --- move: sub.
                       rewrite -c_layout => /(_ b'').
                       rewrite mem_cat b''in mem_filter => /trueI/andP [] + _.
                       rewrite -(@leq_add2r 1) addn1=> H. apply/(leq_trans H).
                       by rewrite subn1 -addnA [_ + 1]addnC addnA addn1 prednK; last by apply/lt_0_time.
                   ---  apply/ltn_addr.
                        apply/(@leq_ltn_trans (t_now N -1)); last by rewrite subn1 ltn_predL; apply/lt_0_time.
                        apply/(@best_chain_time _ (tree l1)).
                        rewrite -/bc1 -bc1_layout -/cs. rewrite mem_cat.
                        apply/orP. constructor 2. rewrite /b -cs_layout.
                        clear. case: cs1=> //= [| >]; by rewrite mem_head. }
  (* We show that the amount of dishonest blocks in both chains must *)
  (*       be larger than or equal to the amount of honest blocks (as no *)
  (*       honest super block goes on both chains). **)
  { rewrite (@super_slots_blocks _ _ N) //; [| by rewrite addn1| by rewrite subn1 leq_pred].
    rewrite -2!size_cat -2!(size_map (pos^~ N)).
    apply/uniq_leq_size.
    (** Uniqueness of SBs in world-tree *)
    { rewrite /=.
      apply/subseq_uniq; [|apply/(unique_sb_pos N0N) => //].
      by apply/map_subseq/filter_subseq. }
    (** Subset of positions. *)
    move=> sbpo/mapP [] sb + -> {sbpo}.
    rewrite /super_blocks_world_range mem_filter.
    move/andP=> [] time=> sbin /=.
    rewrite 2!map_cat.
    set bh := block_history _.
    (* Establishing positions in cs1 and c1 *)
    move/(@cfb_map_iota _ bh): (best_chain_valid (tree l1) (t_now N -1)).
    do 2!apply: instant1=> //.
    { apply/subset_trans; first by apply/best_chain_in_all.
      apply/subset_trans; first by apply/filter_subset.
      apply/subset_trans; first by apply/(subset_honest_tree N0N honest_p1).
      by apply/honest_tree_gb_history_subset. }
    rewrite -/bc1 -bc1_layout -/cs -cs_layout cat1s.
    have ->: (| c1 ++ cs1 ++ b' :: cs2 |) = (| (b' :: cs2) ++ cs1 ++ c1  |).
    { rewrite !size_cat addnA addnC.
      by apply/f_equal; rewrite addnC. }
    rewrite !map_cat !size_cat !iota_add !rev_cat -catA -catA=> /eqP.
    rewrite eqseq_cat=> [/andP []/eqP c1_io |]; last by rewrite size_map size_rev size_iota.
    rewrite eqseq_cat=> [/andP []/eqP cs1_io /eqP cs2_io|]; last by rewrite size_map size_rev size_iota.
    (* Establishing positions in c2 *)
    move/(@cfb_map_iota _ bh): (vc).
    do 2!apply: instant1=> //.
    { by apply/(subset_trans sub)/filter_subset. }
    rewrite -c_layout -/cs -cs_layout cat1s.
    have ->: (| c2 ++ cs1 ++ b' :: cs2 |) = (| (b' :: cs2) ++ cs1 ++ c2  |).
    { rewrite !size_cat addnA addnC.
      by apply/f_equal; rewrite addnC. }
    rewrite !map_cat !size_cat !iota_add !rev_cat -catA => /eqP.
    rewrite eqseq_cat=> [/andP []/eqP c2_io |]; last by rewrite size_map size_rev size_iota.
    (* Moving forward *)
    rewrite mem_cat cs1_io mem_rev mem_iota add1n.
    (* The super block was aware of b' when mined. *)
    have ->: |b' :: cs2 | < |cfb sb bh|.
    { have ->: b' :: cs2 = cfb b' bh.
      { apply/esym/cfb_valid_chain'=> //.
        - apply/(@valid_chain_short_l (c1 ++ cs1)).
          rewrite -catA. rewrite cs_layout bc1_layout.
            by apply/best_chain_valid.
        - apply/(subset_trans _ (honest_tree_gb_history_subset N0N)).
          apply/(subset_trans _ (subset_honest_tree N0N honest_p1 state_p1))=> //.
          apply/(@subset_trans _ _ bc1).
          + rewrite -bc1_layout -/cs -cs_layout 2!catA.
              by apply/subset_catl.
          + by apply/(subset_trans (@best_chain_in_all _ ((t_now N) -1) (tree l1)))/filter_subset. }
      move: (@hb_pos_gt_hb_gb N sb N0N ff no_coll).
      apply: instant1; first by move: sbin; rewrite mem_undup 2!mem_filter -andbA /= inE orbC => /and3P [] /=  -> _ ->.
      move/allP/(_ b')=> -> //.
      rewrite 2!mem_filter honest_tree_gb_history_subset //.
      - by move: time=> /andP [] + _; rewrite addn1 honest_b'=> ->.
      - apply/(subset_trans (subset_honest_tree N0N honest_p1 state_p1))=> //.
        apply/(subset_trans (@best_chain_in_all _ ((t_now N) -1) (tree l1))).
        + by apply/filter_subset.
        + rewrite -/bc1 -bc1_layout mem_cat orbC -/cs -cs_layout.
            by rewrite mem_cat -orbA orbC mem_head. }
    case cfb_lt: (_<_)=> //.
    move=> /=. rewrite mem_cat.
    move/negbT: cfb_lt. rewrite -leqNgt => le_cfb.
    move: (sbin); rewrite mem_undup /super_block !mem_filter /= -andbA => /and3P [] honest_sb _ sbin'.
    (* The sb cannot have a deeper position than bc1 and bc2 *)
    have N0Np: N0 ⇓^+ N.
    { constructor; [done |].
      move: time => /andP [] _ /=. rewrite subn1.
        by case: t_now=> //= [] [] //=. }
    move: (rewind_one_step_ready N0Np) => [] N_R [] N0N_R NR_N prog_NR tNR.
    have sbinR: sb \in honest_block_hist N_R.
    { move: (honest_blocks_below_slot_preserved N0N_R NR_N ff sb).
      rewrite !mem_filter. move: time=> /andP [] _ .
        by rewrite tNR /= honest_sb sbin'=> -> /= ->. }
    have ffR: forging_free N_R by apply/(forging_free_prev _ ff). 
    have no_collR: collision_free N_R.
    { apply/(in_subset2 _ no_coll)/subset_cons2.
      by apply/subset_trans/(block_history_monotone NR_N). }
    have sb_lt_bc: | cfb sb bh | <= | bc1 |.
    { apply/best_chain_best.
      - apply/honest_block_cfb_valid=> //.
          by move: sbin; rewrite mem_undup /super_block !mem_filter /= -andbA => /and3P [] -> _ ->.
      - move=> b'' b''in. rewrite mem_filter.
        apply/andP; constructor.
        + rewrite -(leq_add2r 1) 2!addn1 subn1 prednK; last by apply/lt_0_time.
          apply/ltn_leq_trans; last by apply/leq_pred. rewrite -subn1.
          move: (@honest_block_cfb_valid _ sb N0N ff no_coll).
          rewrite mem_filter /= honest_sb sbin' => /trueI.
          move: (@cfb_non_empty_starts_block sb (block_history N)) b''in.
          case: cfb=> //= x xs /trueI [] ? [] -> _.
          rewrite inE=> /orP [/eqP -> _| b''in] //; first by case/andP: time.
          move=> /and3P [] _ _ /(order_path_min lt_slots_trans)/allP/(_ b'' b''in) lt.
          case/andP : time=> _.
            by apply/(ltn_trans lt).
        + apply/(honest_tree_subset_ext N0N_R honest_p1 prog_NR _ state_p1)=> //.
          { constructor; try done. rewrite tNR subn1 ltn_predL. apply/lt_0_time. done. }
          apply/(@cfb_subset_honest_tree N_R sb N0N_R)=> //.
          rewrite (@cfb_non_empty_subset _ _ bh) //.
          * by apply/(in_subset2 _ no_coll)/subset_cons.
          * by apply/block_history_monotone.
          * by apply/valid_chain_non_empty/honest_block_cfb_valid. }
    have: (|cfb sb bh|) \in [seq | cfb b bh | | b <- c1].
    { rewrite c1_io mem_rev mem_iota add1n le_cfb.
      rewrite -[|_::_|.+1]addn1 -2!addnA addnC -add1n. apply/f_equal.
      rewrite -addnA leq_add2l [_ + |c1 |]addnC -size_cat -size_cat -catA.
      by rewrite cs_layout bc1_layout. }
    move/mapP=> [] x1 x1in x1eq.
    have: (|cfb sb bh|) \in [seq | cfb b bh | | b <- c2].
    { rewrite c2_io mem_rev mem_iota add1n le_cfb.
      rewrite -[|_::_|.+1]addn1 -2!addnA addnC.
      rewrite -add1n andTb -addnA leq_add2l.
      rewrite [_ + |c2 |]addnC -size_cat -size_cat -catA cs_layout c_layout.
      by apply/(leq_trans sb_lt_bc). }
    move/mapP=> [] x2 x2in x2eq.
    (* Usefull facts *)
    have subc1: {subset c1 <= bh}.
    { apply/subset_trans; last by apply/not_gb_honest_tree_history_subset.
      move=> b'' b''in.
      rewrite mem_filter /=. apply/andP; constructor; last first.
      - apply/(subset_trans _ (subset_honest_tree N0N honest_p1 state_p1))=> //; last by apply/b''in.
        apply/subset_trans; first by apply/(@subset_catr _ _ cs).
        rewrite bc1_layout.
          by apply/(subset_trans (@best_chain_in_all _ ((t_now N) -1) (tree l1)))/filter_subset.
      - case: (_==_)/eqP=> //= b''eq. rewrite -(ltn0 (sl b')).
        rewrite -GenesisSlot -b''eq.
        move: dec1.
        case x1_l: _/(splitPr b''in)=> [b''1 b''2] /=.
        rewrite -catA. rewrite cat_cons.
        move/sorted_cat=> /andP [] _ /(order_path_min lt_slots_trans)/allP/(_ b').
        by rewrite catA mem_cat orbC mem_head=> /trueI.  }
    have subc2: {subset c2 <= bh}.
    { move=> b'' b''in. move: (sub b'').
      rewrite -c_layout mem_cat b''in mem_filter=> /trueI/andP [] _ /=.
      rewrite inE=> /orP [/eqP b''eq| //].
      move: (ltn0 (sl b')).
      rewrite -GenesisSlot -b''eq.
      move: dec2.
      case x1_l: _/(splitPr b''in)=> [b''1 b''2] /=.
      rewrite -catA. rewrite cat_cons.
      move/sorted_cat=> /andP [] _ /(order_path_min lt_slots_trans)/allP/(_ b').
      rewrite catA mem_cat orbC mem_head /= => /trueI /=.
        by rewrite /lt_slots=> ->. }
    (* One must be corrupt as the sb can at most sit in one of the *)
(*        chains.  *)
    have/orP []: corrupt_block x1 || corrupt_block x2.
    { rewrite /corrupt_block.
      case x1_cr: is_corrupt=> //=.
      move/negbT: x1_cr. rewrite -honest_not_corrupt=> honest_x1.
      case x2_cr: is_corrupt=> //=.
      move/negbT: x2_cr. rewrite -honest_not_corrupt=> honest_x2.
      move/(_ sb sbin): (no_honest_pos_share_sb N0N ff no_coll)=> all_sb.
      move/allP/(_ x1): (all_sb). rewrite mem_filter /= honest_x1 /=.
      apply: instant1; first by apply/subc1.
      rewrite x1eq eq_refl /==> /eqP sbx1.
      move/allP/(_ x2): (all_sb). rewrite mem_filter /= honest_x2 /=.
      apply: instant1; first by apply/subc2.
      rewrite x2eq eq_refl /==> /eqP sbx2.
      case x1_l: _/(splitPr x1in)=> [x1c1 x1c2].
      case x2_l: _/(splitPr x2in)=> [x2c1 x2c2].
      move: (@eq_head_eq_chains N (x1c2 ++ cs) (x2c2 ++ cs) sb N0N no_coll).
      (* do 4! (apply: instant1; last first).  *)
      apply: instant1; last first.
      apply: instant1; last first.
      apply: instant1; last first.
      apply: instant1; last first.
      - move=> llcs. move: (lcsP (sb:: x1c2 ++cs ) bc1 c).
        rewrite -/cs sbx1 -bc1_layout x1_l.
        rewrite -catA cat_cons.
        rewrite suffix_catl /=.
        rewrite -sbx1 sbx2 -c_layout x2_l llcs.
        rewrite -catA -/cs cat_cons.
        rewrite suffix_catl /=.
        by rewrite -cat_cons suffix_catl_F.
      - apply/(@subset_trans _ _ c).
        + rewrite -c_layout x2_l.
          rewrite -[x2 :: _]cat1s -/cs !catA -catA.
          by apply/subset_catl.
        + by apply/(subset_trans sub)/filter_subset.
      - apply/(subset_trans _ (honest_tree_gb_history_subset N0N)).
        apply/(subset_trans _ (subset_honest_tree N0N honest_p1 state_p1))=> //.
        apply/(@subset_trans _ _ bc1).
        + rewrite -bc1_layout -/cs -cs_layout x1_l.
          rewrite -[x1 :: _]cat1s -catA -catA 2!catA.
          by apply/subset_catl.
        + by apply/(subset_trans (@best_chain_in_all _ ((t_now N) -1) (tree l1)))/filter_subset.
      - apply/(@valid_chain_short_l x2c1). rewrite sbx2.
        by rewrite -cat_cons catA -x2_l c_layout.
      - apply/(@valid_chain_short_l x1c1). rewrite sbx1.
        rewrite -cat_cons catA -x1_l bc1_layout.
          by apply/best_chain_valid. }
    - move=> cx1 _. apply/orP; constructor 1.
      apply/mapP. exists x1; try done. by rewrite mem_filter cx1.
    - move=> cx2 _. apply/orP; constructor 2.
      apply/mapP. exists x2; try done. by rewrite mem_filter cx2. }
Qed.

Lemma cp_prune_gen_inc a N p1 l1 c k: 
  let bc1 := bestChain (t_now N - 1) (tree l1) in
  {subset c <= [seq b <- block_hist_gb N| sl b <= t_now N -1 + a]} ->
  valid_chain c ->
  |bc1| <= |c| ->
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  is_honest p1 ->
  has_state p1 N l1 ->
  prune_time k bc1 ⪯ c
  \/ 
  exists t, t <= k /\
  |super_slots_range (t + 1) (t_now N - 1)|
  <= 2 * | adv_slots_range (t + 1) (t_now N + a)|.
Proof.
  move=> bc1 sub vc leq N0N ff no_coll honest_p1 state_p1.
  set b := head GenesisBlock (lcs bc1 c). 
  move: (leq_total (sl b) k)=> /orP [] b_le_k. 
  - right.
    move: (@cp_lemma_gen_inc a N p1 l1 c sub vc leq N0N ff no_coll honest_p1 state_p1)=> [] t [] tle ?.
    by (exists t; constructor; [apply/(leq_trans tle)|]). 
  - left. apply/(@suffix_trans _ (lcs bc1 c)); last by move/andP: (lcs_suffix bc1 c)=> [].
    move: b_le_k. move/(_ _ vc): (@lcs_vcs_valid bc1 c). 
    apply:instant1; first by apply/best_chain_valid.
    move: (@best_chain_valid _ (tree l1) (t_now N -1)).
    rewrite /b -/bc1. move/andP: (lcs_suffix bc1 c)=> [] + _.
    case: lcs=> // {}b bs H /and3P [] _ _ dec.
    move/suffixP: H dec=> [] bs' <- dec vcbs.
    rewrite /prune_time /head filter_cat=> kleq.
    have ->: [seq b0 <- bs' | sl b0 <= k] = [::]. 
    { move/sorted_max: dec.
      elim: bs'=> //= b' bs' + /andP [] + ?.
      move=> -> //. rewrite /lt_slots=> H.
      move/(_ k (sl b')): anti_leq (H). 
      rewrite (leq_trans kleq) /=; last by rewrite ltnW.
      case: (_ <= _)=> //= /trueI <-.
      move/(leq_ltn_trans kleq).
        by rewrite ltnn. }
    rewrite cat0s. 
    move/and3P: vcbs=> [] _ _ . 
      by apply/prune_time_suffix. 
Qed. 

Lemma cp_prune_gen_inc_r a N p1 l1 c k: 
  let bc1 := bestChain (t_now N - 1) (tree l1) in
  {subset c <= [seq b <- block_hist_gb N| sl b <= t_now N -1 + a]} ->
  valid_chain c ->
  |bc1| <= |c| ->
  N0 ⇓ N ->
  forging_free N ->
  collision_free N ->
  is_honest p1 ->
  has_state p1 N l1 ->
  prune_time k c ⪯ bc1
  \/ 
  exists t, t <= k /\
  |super_slots_range (t + 1) (t_now N - 1)|
  <= 2 * | adv_slots_range (t + 1) (t_now N + a)|.
Proof.
  move=> bc1 sub vc leq N0N ff no_coll honest_p1 state_p1.
  set b := head GenesisBlock (lcs bc1 c). 
  move: (leq_total (sl b) k)=> /orP [] b_le_k. 
  - right.
    move: (@cp_lemma_gen_inc a N p1 l1 c sub vc leq N0N ff no_coll honest_p1 state_p1)=> [] t [] tle ?.
    by (exists t; constructor; [apply/(leq_trans tle)|]). 
  - left.
    apply/(@suffix_trans _ (lcs bc1 c)); last by move/andP: (lcs_suffix bc1 c)=> [].
    move: b_le_k. move/(_ _ vc): (@lcs_vcs_valid bc1 c). 
    apply:instant1; first by apply/best_chain_valid.
    (* move: (@best_chain_valid _ (tree l1) (t_now N -1)). *)
    move: vc. 
    rewrite /b -/bc1. move/andP: (lcs_suffix bc1 c)=> [] _ +.
    case: lcs=> // {}b bs H /and3P [] _ _ dec.
    move/suffixP: H dec=> [] bs' <- dec vcbs.
    rewrite /prune_time /head filter_cat=> kleq.
    have ->: [seq b0 <- bs' | sl b0 <= k] = [::]. 
    { move/sorted_max: dec.
      elim: bs'=> //= b' bs' + /andP [] + ?.
      move=> -> //. rewrite /lt_slots=> H.
      move/(_ k (sl b')): anti_leq (H). 
      rewrite (leq_trans kleq) /=; last by rewrite ltnW.
      case: (_ <= _)=> //= /trueI <-.
      move/(leq_ltn_trans kleq).
        by rewrite ltnn. }
    rewrite cat0s. 
    move/and3P: vcbs=> [] _ _ . 
      by apply/prune_time_suffix. 
Qed. 

Lemma prune_suffix_trans k c1 c2 c3 :
  prune_time k c1 ⪯ c2 ->
  prune_time k c2 ⪯ c3 ->
  prune_time k c1 ⪯ c3.  
Proof.
  move/suffixP=> [] h1 <- /suffixP [] h2 <- /=.
  rewrite filter_cat filter_filter catA. 
  set h := h2 ++ _. apply/suffixP. by exists h. 
Qed. 

Lemma common_prefix_lemma_parties N p1 p2 l1 l2 k:
  let bc1 := bestChain (t_now N - 1) (tree l1) in
  let bc2 := bestChain (t_now N - 1) (tree l2) in
  let b := head GenesisBlock (lcs bc1 bc2) in
  N0 ⇓ N ->
  forging_free N -> 
  collision_free N ->
  is_honest p1 ->
  is_honest p2 ->
  has_state p1 N l1 ->
  has_state p2 N l2 ->
  prune_time k bc1 ⪯ bc2
  \/ 
  exists t, t <= k /\
  |super_slots_range (t + 1) (t_now N - 1)|
  <= 2 * | adv_slots_range (t + 1) (t_now N)|.
Proof.
  move=> bc1 bc2 b N0N ff no_coll honest_p1 honest_p2 state_p1 state_p2.
  move/orP: (leq_total (|bc1|) (|bc2|))=> [] leq. 
  - move: (@cp_prune_gen_inc 0 N p1 l1 bc2 k).
    rewrite !addn0. apply: instant3=> //; last first. 
    move/(_ N0N ff no_coll honest_p1 state_p1)=> [] ?; by [left | right]. 
    + by apply/best_chain_valid.
    + move=> b' b'in. rewrite mem_filter.
      apply/andP; constructor.
      * by move/(_ b' b'in): (@best_chain_time _ (tree l2) (t_now N-1)). 
      * move: b' b'in. apply/subset_trans; first by apply/best_chain_in_all.
        apply/subset_trans; first by apply/filter_subset.
        apply/subset_trans; first by apply (subset_honest_tree N0N honest_p2 state_p2). 
          by apply/honest_tree_gb_history_subset. 
  - move: (@cp_prune_gen_inc_r 0 N p2 l2 bc1 k).
    rewrite !addn0. apply: instant3=> //; last first. 
    move/(_ N0N ff no_coll honest_p2 state_p2)=> [] H; [by left | by right]. 
    + by apply/best_chain_valid.
    + move=> b' b'in. rewrite mem_filter.
      apply/andP; constructor.
      * by move/(_ b' b'in): (@best_chain_time _ (tree l1) (t_now N-1)). 
      * move: b' b'in. apply/subset_trans; first by apply/best_chain_in_all.
        apply/subset_trans; first by apply/filter_subset.
        apply/subset_trans; first by apply (subset_honest_tree N0N honest_p1 state_p1). 
          by apply/honest_tree_gb_history_subset. 
Qed. 

Lemma p_slots_size_leq_addr p a b c: 
  (| p_slots_range p a b | <= | p_slots_range p a (b + c) |). 
Proof. 
  case a_leq_b: (a <= b)=> //=.
  - rewrite (@p_slots_range_split p a b (b + c)).
    + by rewrite size_cat leq_addr.
    + by rewrite a_leq_b leq_addr. 
  - rewrite {1}/p_slots_range /nat_range.
    suff ->: b - a = 0 by done.
    apply/eqP. rewrite subn_eq0. move: (leq_total a b).
    by rewrite a_leq_b. 
Qed. 

Theorem timed_common_prefix k N1 N2 :
  N0 ⇓ N1 ->
  N1 ⇓ N2 ->
  forging_free N2 -> 
  collision_free N2 ->
  forall p1 p2 l1 l2, 
  let bc1 := bestChain (t_now N1 - 1) (tree l1) in
  let bc2 := bestChain (t_now N2 - 1 ) (tree l2) in
  is_honest p1 ->
  is_honest p2 ->
  has_state p1 N1 l1 ->
  has_state p2 N2 l2 ->
  prune_time k bc1 ⪯ bc2
  \/ 
  exists t1 t2,
    [/\ t1 <= k
     , t_now N1 <= t2 <= t_now N2
     & |super_slots_range (t1 + 1) (t2 - 1)| <= 2 * | adv_slots_range (t1 + 1) (t2 +1)| ].
Proof.
  move=> N0N1.
  elim=> //.
  (* BC *)
  { move=> ff no_coll p1 p2 l1 l2 bc1 bc2 honest_p1 honest_p2 state_p1 state_p2.
    move: (@common_prefix_lemma_parties N1 p1 p2 l1 l2 k). 
    apply: instant7 => // [] [H|] ; [by left|].
    case=> t1 [] H1 H2. right.
    exists t1. exists (t_now N1). constructor; try done.
    - by rewrite leqnn.
    - apply/(leq_trans H2). rewrite leq_pmul2l //.  
      by apply/p_slots_size_leq_addr. }
  (* IH *)
  { move=> A B [] {}N2 //.
    (* Delivery  *)
    { move=> prog_N2 N1N2 IH ff /= no_coll p1 p2 l1 l2' honest_p1 honest_p2 state_p1. 
      have ffN2: forging_free N2 by apply/(forging_free_prev _ ff); do 2! econstructor.  
      move: IH. apply:instant2=> //.
      { by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_deliverys. }
      move=> IH. 
      have N0N2: N0 ⇓ N2 by apply/(big_step_trans _ N1N2).
      (* Establish relationship with previous party-state *)
      rewrite/has_state single_party_rcv_step_state // => state_p2'. 
      move/has_exists_state/exists_rcv_step_pres: (state_p2').
      rewrite/exists_state.
      case state_p2: (_.[? _])=> [l2|] //= _. rewrite delivery_preserves_time. 
      move: (@delivery_blocktree p2 N2 l2 l2'). 
      apply: instant3=> // ab_trees. 
      (* Use IH and propagate failure *)
      move: (IH p1 p2 l1 l2). apply: instant4 => //= [] []; last first.
      { move=> [] t1 [] t2 [] H1 H2 H3.
        right. exists t1; exists t2. by constructor. }
      set bc1 := bestChain _ _. 
      set bc2 := bestChain _ _. 
      set bc2' := bestChain _ _.
      move=> bc1p_suff_bc2. 
      (* There must be relationship between bc2 and bc2' *)
      move: (@cp_prune_gen_inc 1 N2 p2 l2 bc2' k). 
      apply: instant7; last first; try done.
      { move/(_ state_p2).
        case; last first.
        - move=> [] t1 [] H1 H2.
          right. exists t1. exists (t_now N2).
          constructor; try done.
          by rewrite monotone_time //=.
        - move=> bc2p_suff. constructor. 
            by apply/(prune_suffix_trans bc1p_suff_bc2). }
      { by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_deliverys. }
      - apply/best_chain_best.
        + by apply/best_chain_valid. 
        + move=> b /best_chain_in_all.
          rewrite 2!mem_filter ab_trees mem_cat => /andP [] slb -> /=.
          rewrite andbT.
            by apply/(leq_trans slb). 
      - by apply/best_chain_valid. 
      - move=> b' b'in. rewrite mem_filter.
        apply/andP; constructor.
        + rewrite subn1 addn1 prednK; last by apply/lt_0_time.
          move: (best_chain_time b'in)=> H. apply/(leq_trans H).
            by rewrite subn1 leq_pred. 
        + move: b' b'in. apply/subset_trans; first by apply/best_chain_in_all.
          apply/subset_trans; first by apply/filter_subset.
          move=> b. rewrite ab_trees mem_cat => /orP [].
          * move: b.
            apply/subset_trans; first by apply (subset_honest_tree (big_step_trans N0N1 N1N2) honest_p2 state_p2). 
              by apply/honest_tree_gb_history_subset/(big_step_trans N0N1).
          * move: b=> /=. apply/subset_trans; last by apply/subset_cons. 
            move=> b. move/mapP => [] m + ->.
            rewrite mem_filter=> /andP [] _ min.
            apply/mapP. exists (msg m); [|done].
            apply/buff_history_subset=> //. 
            by apply/mapP; exists (m). }
    (* Baking *)
    { move=> prog_N2 N1N2 IH ff /= no_coll p1 p2 l1 l2' honest_p1 honest_p2 state_p1. 
      have ffN2: forging_free N2 by apply/(forging_free_prev _ ff); do 2! econstructor.  
      move: IH. apply: instant2=> //.
      {by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_bakes. }
      move=> IH. 
      have N0N2: N0 ⇓ N2 by apply/(big_step_trans _ N1N2).
      (* Establish relationship with previous party-state *)
      rewrite/has_state single_party_bake_step_state // => state_p2'. 
      move/has_exists_state/exists_bake_step_pres: (state_p2').
      rewrite/exists_state.
      case state_p2: (_.[? _])=> [l2|] //= _. rewrite baking_preserves_time. 
      (* Use IH and propagate failure *)
      move: (IH p1 p2 l1 l2). apply: instant4 => //= [] []; last first.
      { move=> [] t1 [] t2 [] H1 H2 H3.
        right. exists t1; exists t2. by constructor. }
      set bc1 := bestChain _ _. 
      set bc2 := bestChain _ _. 
      set bc2' := bestChain _ _.
      move=> bc1p_suff_bc2. 
      move: state_p2'.
      rewrite /party_bake_step_world state_p2 -honest_not_corrupt honest_p2.
      rewrite /honest_bake /=.
      case win_p2: Winner; rewrite fnd_set eq_refl; case; rewrite /bc2'=> <- //; last by left. 
      move=> {bc2'}. 
      set bc2' := bestChain _ _.
      move: (@cp_prune_gen_inc 0 N2 p2  l2 bc2' k). 
      apply: instant7; last first; try done.
      { move/(_ state_p2).  case; last first.
        - move=> [] t1 [] H1 H2.
          right. exists t1. exists (t_now N2).
          constructor; try done.
          + by rewrite monotone_time //=.
          + apply/(leq_trans H2).
            rewrite addn0 leq_pmul2l //.
            by apply/p_slots_size_leq_addr. 
        - move=> bc2p_suff_bc2. constructor. 
            by apply/(prune_suffix_trans bc1p_suff_bc2). }
      { by apply/(in_subset2 _ no_coll)/subset_cons2/map_subset/history_monotone_bakes. } 
      - apply/best_chain_best.
        + by apply/best_chain_valid. 
        + move=> b /best_chain_in_all.
          by rewrite 2!mem_filter all_extend mem_cat=> /andP [] -> ->. 
      - by apply/best_chain_valid.
      -  move=> b' b'in. rewrite mem_filter.
         apply/andP; constructor.
         + by rewrite addn0; move: (best_chain_time b'in).
         + have: b' \in allBlocks (tree l2). 
           { move: (best_chain_in_all b'in). rewrite mem_filter=> /andP [] slb'. 
             rewrite all_extend mem_cat => /orP [] //.
             rewrite mem_seq1=> /eqP b'eq. move: slb'.
             rewrite b'eq /=. rewrite -(leq_add2r 1) !addn1 subn1 prednK; last by apply/lt_0_time.
             by rewrite ltnn. }
         + move=> {b'in}. move: b'. 
           apply/subset_trans; first by apply (subset_honest_tree (big_step_trans N0N1 N1N2) honest_p2 state_p2). 
             by apply/honest_tree_gb_history_subset/(big_step_trans N0N1). }
    (* Incrementing *)
    { move=> prog_N2 N1N2 IH ff /= no_coll p1 p2 l1 l2 honest_p1 honest_p2 state_p1 state_p2.
      have ffN2: forging_free N2 by apply/(forging_free_prev _ ff); do 2! econstructor.  
      move: IH => /(_ ffN2 no_coll) IH.
      move: (IH p1 p2 l1 l2).
      apply: instant4 => //.
      case; last first.
      { move=> [] t1 [] t2 [] H1 /andP [] H2 H3 H4.
        right. exists t1. exists t2. constructor; try done.
          by rewrite H2 /=; apply/(leq_trans H3). }
      set bc1 := bestChain _ _.
      set bc2 := bestChain _ _.
      set bc2' := bestChain _ _.
      move=> bc1p_suff.
      move: (@cp_prune_gen_inc 1 N2 p2  l2 bc2' k). 
      apply: instant7; last first; try done.
      { move/(_ state_p2). case; last first.
        - move=> [] t1 [] H1 H2.
          right. exists t1. exists (t_now N2).
          constructor; try done.
          rewrite monotone_time //=.
        - move=> bc2p_suff. constructor. 
          by apply/(prune_suffix_trans bc1p_suff). }
      - by apply/(big_step_trans N0N1). 
      - apply/best_chain_best.
        + apply/best_chain_valid. 
        + move=> b /best_chain_in_all.
          rewrite 2!mem_filter => /andP [] slb ->.
          rewrite andbT. apply/(leq_trans slb)=> /=.
            by rewrite 2!subn1 /= leq_pred.
      - by apply/best_chain_valid.
      -  move=> b' b'in. rewrite mem_filter.
          apply/andP; constructor.
         + move: b'in. rewrite /bc2' /=.
            rewrite !subn1 !addn1 /= prednK.
            * by move=> b'in; move/(_ b' b'in): (@best_chain_time _ (tree l2) (t_now N2)).
            * by apply/lt_0_time/(big_step_trans N0N1). 
         +  move: b' b'in. apply/subset_trans; first by apply/best_chain_in_all.
            apply/subset_trans; first by apply/filter_subset.
            apply/subset_trans; first by apply (subset_honest_tree (big_step_trans N0N1 N1N2) honest_p2 state_p2). 
              by apply/honest_tree_gb_history_subset/(big_step_trans N0N1). }
    (* Perms *)
    - move=> ??? IH ff ??.
      apply/IH=> //. apply/(forging_free_prev _ ff). 
      by do 2! econstructor. 
    - move=> ??? IH ff ??.
      apply/IH=> //. apply/(forging_free_prev _ ff). 
      by do 2! econstructor. 
  }
Qed. 

(* Slightly rephrased *)
Theorem timed_common_prefix' k N1 N2 :
  N0 ⇓ N1 ->
  N1 ⇓ N2 ->
  (forall t1 t2, t1 <= k ->
            t_now N1 <= t2 <= t_now N2
            -> |super_slots_range (t1 + 1) (t2 - 1)| > 2 * | adv_slots_range (t1 + 1) (t2 +1)|) ->
  forging_free N2 ->
  collision_free N2 ->
  forall p1 p2 l1 l2, 
  let bc1 := bestChain (t_now N1 - 1) (tree l1) in
  let bc2 := bestChain (t_now N2 - 1 ) (tree l2) in
  is_honest p1 ->
  is_honest p2 ->
  has_state p1 N1 l1 ->
  has_state p2 N2 l2 ->
  prune_time k bc1 ⪯ bc2. 
Proof.
  move=> + + adv. 
  move/(timed_common_prefix k).
  do 7! move=> H /H {H} + >. 
  move=> [] // [] ? [] ? [] ??.
  by rewrite leqNgt adv. 
Qed. 

