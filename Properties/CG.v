Require Import
        Relations.

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
     TreeChain.

Open Scope fmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Chain Growth
      This file contains the proof of chain growth. 
**)


(* Simple getter for block from a msg. *)
Definition get_block (msg : Message) : Block :=
  match msg with
  | BlockMsg b => b
  end.

Definition block_history (N : GlobalState) :=
  [seq get_block m | m <- history N].

Arguments block_history !N /. 

Definition honest_block b :=
  is_honest (bid b).

Arguments honest_block _ /.

Definition corrupt_block b :=
  is_corrupt (bid b).

Arguments corrupt_block _ /.

Definition honest_blocks c :=
  [seq b <- c | honest_block b]. 

Arguments honest_blocks _ /. 

Definition honest_subset s1 s2 :=
  {subset honest_blocks s1 <= honest_blocks s2}. 

Arguments honest_subset !s1 _ /. 

(** *Assumption *)
Axiom PartiesUniq : uniq InitParties.
Axiom NonEmptyHonestParties : has is_honest InitParties. 
Axiom HonestGB : is_honest (bid GenesisBlock). 
(* The protocol is parameterized over a tree type *)
Parameter Tree : treeType.


(* A simple extraction of all the honest parties from a world *)
Definition honest_parties (N : GlobalState) : Parties :=
  [seq p <- (exec_order N) | is_honest p].

(* All the blocks in a blocktree of a specific party in a world *)
Definition blocks (p : Party) (N : GlobalState) : BlockPool :=
  if (state_map N).[? p] is Some l then allBlocks (tree l) else [::].

(* The honest tree is defined as the union of all honest parties trees
   at a particular time *)
Definition honest_tree (N : GlobalState) : Tree :=
  let: blocks := [seq blocks p N | p <- honest_parties N] in
  build_tree (flatten blocks).

(* A list of all honest winners for a particular slot *)
Definition honest_winners (N : GlobalState) : Parties :=
  [seq p <- honest_parties N | Winner p (t_now N)].

(* A boolean predicate telling if there is an honest winner for the
   current slot of the world *)
Definition honest_winner (N : GlobalState) : bool :=
  ~~ nilp (honest_winners N).

(** **Relating honest and corrupt **)
Lemma honest_not_corrupt p : is_honest p = ~~(is_corrupt p).
Proof. by rewrite /is_honest /is_corrupt; case: (CorruptionStatus p). Qed.

Lemma not_honest_corrupt p : ~~(is_honest p) = is_corrupt p.
Proof. by rewrite /is_honest /is_corrupt; case: (CorruptionStatus p). Qed.

(** **Presevation of state, time and progress **)
Definition has_state p N l := (state_map N).[? p] = Some l.

(* Arguments has_state _ _ _ /.  *)

Definition exists_state p N : bool := (state_map N).[? p].

(* Arguments has_state _ _ /.  *)
Lemma exists_stateP p N : reflect (exists l, has_state p N l) (exists_state p N). 
Proof.
  rewrite /has_state /exists_state. apply/(iffP idP).
  - by case s: (_.[? _])=> [l|]// _; exists l.  
  - by move=> [] l ->. 
Qed. 

Lemma has_exists_state p N l : has_state p N l -> exists_state p N.
Proof. by rewrite /exists_state=> ->. Qed.

Lemma flood_msgs_preserves_order N:
  forall msgs, exec_order (flood_msgs msgs N) = exec_order N.
Proof. by elim=> [|[ ] ]. Qed.

Lemma broadcast_adv_msgs_preserves_order N : forall msgs,
  exec_order (flood_msgs_adv msgs N) = exec_order N.
Proof. by elim=> [|[ ] ]. Qed.

Lemma bake_preserves_order N p :
  exec_order (party_bake_step_world p N) = exec_order N.
Proof.
  rewrite /party_bake_step_world. case: (_.[? p])=> [?|] //=. case: (~~_).
  - by case: honest_bake => >; rewrite flood_msgs_preserves_order.
  - by case: AdversarialBake=> >//=; rewrite broadcast_adv_msgs_preserves_order.
Qed.

Lemma bakes_preserves_order N ps :
  exec_order (foldr party_bake_step_world N ps) = exec_order N.
Proof. by elim: ps=> > //=; rewrite bake_preserves_order. Qed.


Lemma rcv_preserves_order N p:
  exec_order (party_rcv_step_world p  N) = exec_order N.
Proof.
  rewrite {1}/party_rcv_step_world.
  case: (_.[? _])=> //= ?. case: (~~_)=> //=.
  by case: AdversarialRcv=> >; rewrite broadcast_adv_msgs_preserves_order.
Qed. 

Lemma rcvs_preserves_order N:
  forall ps, exec_order (foldr party_rcv_step_world N ps) = exec_order N.
Proof. by elim=> //= >; rewrite rcv_preserves_order. Qed. 

Lemma adv_rcv_preserves_state p N:
  is_corrupt p ->
  state_map (party_rcv_step_world p N) = state_map N.
Proof.
  rewrite /party_rcv_step_world /fetch_msgs. case: (_.[? p])=> [?|//] ->.
  case: (AdversarialRcv _ _ _). by elim => [| [^ msgs] ].
Qed.

Lemma adv_bake_preserves_state p N:
  is_corrupt p ->
  state_map (party_bake_step_world p N) = state_map N.
Proof.
  rewrite /party_bake_step_world. case: (_.[? p])=> [?|//] ->.
  case: (AdversarialBake _ _ _). by elim => [| [^ msgs] ].
Qed.

Lemma broadcast_adv_msgs_preserves_time N :
  forall msgs, t_now (flood_msgs_adv msgs N) = t_now N.
Proof. by elim=> [|[ ] ]. Qed.

Lemma flood_msg_preserves_time N:
  forall msgs, t_now (flood_msgs msgs N) = t_now N.
Proof. by elim=> [|[ ] ]. Qed.

Lemma delivery_preserves_time N:
  t_now (foldr party_rcv_step_world N (exec_order N)) = t_now N.
Proof.
  elim: (exec_order _) => [| p ps IH] //=.
  rewrite {1}/party_rcv_step_world /=. case: (_.[? _])=> //= l.
  case: (~~ _)=> //=. case: AdversarialRcv => ?? //=.
    by rewrite broadcast_adv_msgs_preserves_time.
Qed.

Lemma baking_preserves_time N:
  forall ps, t_now (foldr party_bake_step_world N ps) = t_now N.
Proof.
  elim  => [| p ps IH] //=. rewrite {1}/party_bake_step_world /=.
  case: (_.[? _])=> //= l. case: (~~ _)=> //=.
  - case: honest_bake=> ?? //=.
      by rewrite flood_msg_preserves_time.
  - case: AdversarialBake=> ?? //=.
      by rewrite broadcast_adv_msgs_preserves_time.
Qed.

Lemma progress_preserves_state N p :
  state_map (N[[progress := p]]) = state_map N.
Proof. done. Qed.

Lemma flood_msgs_preserves_state N:
  forall msgs, state_map (flood_msgs msgs N) = state_map N.
Proof. by elim. Qed.

Lemma broadcast_adv_msgs_preserves_state N :
  forall msgs, state_map (flood_msgs_adv msgs N) = state_map N.
Proof. by elim=> [|[ ] ]. Qed.

(* If a party has a state in one point in the protocol he will also
   have a state in later steps *)
Lemma exists_state_pres_big_step N N' p :
  N ⇓ N' -> exists_state p N = exists_state p N'.
Proof. 
  elim; first by constructor. rewrite /exists_state.
  move=> ?? H _ ->.
  move: H => [] {} N {N'} // _; elim (exec_order _)=> [//| p' ps] /=;
  set N':= (foldr _ _ _); move=> IH; case p'_corrupt: (is_corrupt p').
  - rewrite /party_rcv_step_world /fetch_msgs p'_corrupt.
    case eq: (_.[? p'])=> [l'|//] /=. case: AdversarialRcv=> ?? /=.
      by rewrite broadcast_adv_msgs_preserves_state.
  - rewrite /party_rcv_step_world /fetch_msgs p'_corrupt.
    case eq: (_.[? p'])=> [l'|//] /=. rewrite fnd_set IH /=.
      by case: (_ == _)/eqP=> //; move->; rewrite eq.
  - rewrite /party_bake_step_world. case eq: (_.[? p'])=> [l'|//].
    case honest_bake=> ??. rewrite p'_corrupt /=.
    case: AdversarialBake=> ?? /=.
      by rewrite broadcast_adv_msgs_preserves_state.
  - rewrite /party_bake_step_world. case eq: (_.[? p'])=> [l'|//].
    case honest_bake=> ??. rewrite p'_corrupt /=.
    rewrite flood_msgs_preserves_state fnd_set IH //=.
      by case: (_ == _)/eqP=> //; move->; rewrite eq.
Qed.

(* Having a state is equivalent of being in the initial parties *)
Lemma has_state_initP N p : N0⇓N -> exists_state p N = (p \in InitParties).
Proof.
  move=> H. rewrite -(exists_state_pres_big_step _ H)  /exists_state /N0 /=.
  elim InitParties=> [|?? IH]; [by rewrite fnd_fmap0 | rewrite fnd_set].
  case eq: (_ == _)/eqP=> [->| _]; by [rewrite mem_head | rewrite IH inE eq].
Qed.

Lemma perm_exec_order N N' :
  N ⇓ N' -> perm_eq (exec_order N) (exec_order N').
Proof.
  elim=> // ?? []; clear; move=> {} ??? H2 //.
  - by apply/(perm_trans H2); rewrite rcvs_preserves_order. 
  - by apply/(perm_trans H2); rewrite bakes_preserves_order.
  - by move=> H3; apply/(perm_trans H3).
Qed. 

Lemma exec_order0_ne : exec_order N0 != [::].
Proof.
  move: NonEmptyHonestParties => /=.
  case: InitParties => //=.      
Qed.   

Lemma exec_order_ne_pres N: N0 ⇓ N -> exec_order N != [::]. 
Proof.
  move/perm_exec_order/perm_mem.
  move: exec_order0_ne. case: (exec_order N)=> //=.
  move=> H /mem_eq_sym /mem_eq_nil H'. move: H.
  by rewrite H'. 
Qed. 

Lemma exec_order_honest_pres N: N0 ⇓ N -> has is_honest (exec_order N). 
Proof.
  move/perm_exec_order/perm_mem=> H.
  move: NonEmptyHonestParties. move/hasP => [] p ??.
  apply/hasP. exists p; try done. 
  by rewrite -H. 
Qed. 


(** Permutation of exec order through bigstep **)
Lemma perm_exec_order0 N : N0 ⇓ N -> perm_eq InitParties (exec_order N).
  by move=>/perm_exec_order. 
Qed.

Lemma has_state_in_exec_order N p l :
  N0 ⇓ N -> has_state p N l -> p \in exec_order N. 
Proof. 
  move=> H'. move: (H')=> /perm_exec_order0/perm_mem <- H.
  by rewrite -(@has_state_initP _ _ H') /exists_state H.
Qed. 

Lemma uniq_exec_order N : N0 ⇓ N -> uniq (exec_order N).
Proof. by move/perm_exec_order0/perm_uniq=> <-; rewrite PartiesUniq. Qed.

(** **Transitivity of bigstep semantics **)
Lemma big_step_trans N N' N'' : N ⇓ N' -> N'⇓ N'' -> N ⇓ N''.
Proof.
  move=> /clos_rt_rtn1_iff H1 /clos_rt_rtn1_iff H2.
  by apply/clos_rt_rtn1_iff/(@rt_trans _ _ _ _ _ H1 H2).
Qed.

Lemma big_step_time_trans N N' N'' t t':
  N ⇓[t] N' -> N' ⇓[t'] N'' -> N ⇓[t + t'] N''.
Proof.
  move=> [H1 <-] [H2 <-].
    by constructor; [apply/(big_step_trans H1 H2)| rewrite addnCA addnA].
Qed.

(** Init state and genesis tree *)
Lemma tree_gb_init p l : has_state p N0 l -> tree l = (tree_gb (tT l)).
Proof.
  rewrite /has_state /N0 /=. elim InitParties => //= [| >?].
  - by rewrite fnd_fmap0.
  - by rewrite fnd_set; case: (_ == _)=> [ [<-] |] //.
Qed.

Lemma tree_gb_gb {tT : treeType} (b : Block) :
  (b \in allBlocks (tree_gb tT)) = (b == GenesisBlock).
Proof.
  by rewrite /tree_gb /= all_tree0 inE. 
Qed.

Lemma best_chain_tree_gb {tT : treeType} sl :
  bestChain sl (tree_gb tT) = [:: GenesisBlock]. 
Proof.
  move: (best_chain_valid (tree_gb tT) sl). move: (@best_chain_in_all tT sl (tree_gb tT)).
  case: bestChain=> //= b bs /(_ b).  
  rewrite mem_head=> /trueI. rewrite mem_filter=> /andP [] _.
  rewrite tree_gb_gb=> /eqP -> /andP [] _ /andP [] _ /=.
  move=> /(order_path_min lt_slots_trans). 
  case: bs=> //= b' ? /andP [] /=. 
    by rewrite /lt_slots /= GenesisSlot ltn0. 
Qed. 

(* The tree of an honest party will always be a subset of the honest
   tree *)
Lemma subset_honest_tree N p l:
  N0 ⇓ N -> is_honest p -> has_state p N l ->
  {subset allBlocks (tree l) <= allBlocks (honest_tree N)}.
Proof.
  rewrite /has_state=> H H' H'' b.
  rewrite /honest_tree. 
  rewrite /honest_tree all_build /blocks /honest_parties.
  have: p \in exec_order N.
  { move: (has_state_initP p H). rewrite /exists_state H'' /=.
    by move: (perm_exec_order0 H)=> /perm_mem -> <-. }
  elim: (exec_order N)=> //= p' ps IH.
  rewrite inE=> /orP [/eqP <-| ].
  - rewrite H' /= H''.
    by rewrite inE mem_cat orbC=> ->.     
  - case: (is_honest p') => //=. rewrite inE mem_cat orbC.
    by case: (b \in _)=> //=; rewrite orbC -in_cons.
Qed.

(** *Lemmata about time **)
Lemma monotone_time N N': N ⇓ N' -> t_now N <= t_now N'.
Proof.
  elim=> [| ?? [] ?] //=.
  - by rewrite delivery_preserves_time.
  - by rewrite baking_preserves_time.
  - by move=> _ _ ?; apply/leq_trans.
Qed.

Lemma zero_time_progress_delivered N N':
  N ⇓[0] N' -> N @ Delivered -> ~(N' @ Ready).
Proof.
  case. elim=> [ _ -> | ?? [] N'' ? //= /monotone_time] //.
    by move=> H _ //=; rewrite add0n => H1; move: H1 H=> ->; rewrite ltnn.
Qed.

Lemma zero_time_progress_baked N N': N ⇓[0] N' -> N @ Baked -> N' @ Baked .
Proof.
  case. elim=> [_ -> |] // ?? [] //= ?.
  - move=> + H2 IH H3 ?. rewrite IH=> //=.
      by move: H3; rewrite delivery_preserves_time.
  - rewrite add0n. move=> _ //= /monotone_time H _ H1 _.
      by move: H1 H => -> //=; rewrite ltnn.
Qed.


Lemma honest_tree_preservation N N' s:
  N ⇓ N' -> N @ s -> N' @ s -> t_now N = t_now N' ->
  allBlocks (honest_tree N) =i allBlocks (honest_tree N').
Proof.
  elim=> //= ?? [] //= N'' H1 H2 _.
  - rewrite delivery_preserves_time => <- //= H4. move: (Logic.eq_sym H4) => H5 H3.
      by move: (zero_time_progress_delivered (conj H2 H3) H5 H1).
  - rewrite baking_preserves_time => <- //= H4. move: (Logic.eq_sym H4) => H5 H3.
      by move: (zero_time_progress_baked (conj H2 H3) H5); rewrite H1.
  - move=> _ _ H. move: (monotone_time H2).
      by rewrite H ltnn.
  - do ! move=> IH /IH {IH}. move->. 
    rewrite /honest_tree !all_build /honest_parties.
    apply/mem_eq_cons. 
      by apply/perm_mem/perm_flatten/perm_map/perm_filter. 
Qed.


(* If anything is in the honest tree there is an honest party that has
   it in his state *)
Lemma in_honest_tree N b :
  N0 ⇓ N -> 
  b \in allBlocks (honest_tree N) ->
  exists p l,
    has_state p N l
    /\ b \in allBlocks (tree l)
    /\ is_honest p
    /\ p \in exec_order N.
Proof.
  move=> N0N. 
  rewrite /honest_tree /= all_build /honest_parties.
  rewrite inE => /orP [/eqP ->|].
  - move/hasP: (exec_order_honest_pres N0N)=> [] p pin honest_p.
    move: (has_state_initP p N0N).
    move/perm_mem: (perm_exec_order N0N) ->.
    rewrite pin /exists_state.
    case state_p: (_.[? _]) =>[l|] //= _.
    exists p; exists l. constructor; try constructor; try done. 
    by rewrite gb_in_all. 
  -  elim: (exec_order N) => [|p ? IH] //=. case h: (is_honest _)=> //=. 
     + rewrite mem_cat => /orP [] //. 
       * rewrite /blocks. case s: (_.[? _]) => [l|] //= ?. exists p. exists l.
         do ! constructor; by [|rewrite mem_head]. 
       * move=> /IH [] p' [] l' [] ? [] ? [] ? H . exists p'. exists l'.
         do ! constructor; by [|rewrite inE orbC H]. 
     +  move=> /IH [] p' [] l' [] ? [] ? [] ? H. exists p'. exists l'.
        do ! constructor; by [|rewrite inE orbC H]. 
Qed. 

Lemma init_ht_gb b : b \in allBlocks (honest_tree N0) -> b = GenesisBlock.
Proof.
  move/in_honest_tree. apply:instant1; first by constructor. 
  move=> [] p [] l [] /tree_gb_init ->.
  by rewrite tree_gb_gb => [ [] ] /eqP.
Qed. 

Lemma in_tree_in_honest_tree N b :
  N0 ⇓ N ->
  (exists p l, has_state p N l /\ b \in allBlocks (tree l) /\ is_honest p) ->
  b \in allBlocks (honest_tree N).
Proof. 
  move=> H [] p [] l [state [H2 honesty] ]. 
  rewrite /honest_tree /= all_build.
  rewrite inE. apply/orP. constructor 2.
  apply/flattenP. exists (allBlocks (tree l)); last done. 
  rewrite /blocks. rewrite /honest_parties.
  move: (state) => /(has_state_in_exec_order H). 
  elim: exec_order=> //= p' ps IH. rewrite inE=> /orP [/eqP <- | ]. 
  - by rewrite honesty /= state mem_head. 
  - move/IH. case: (is_honest _)=> //=. 
    by rewrite inE orbC => ->. 
Qed. 

(* Tactics used for fixing Coq bugs *)
Ltac fix_this :=
  match goal with
    |- ?g1.[? ?g2] = ?g3 => change (g1.[? g2] = g3)
  end.

Ltac fix_this' :=
  match goal with
    |- ?g1.[? ?g2] = ?g3.[? ?g4] => change (g1.[? g2] = g3.[? g4])
  end.

Ltac fix_this'' :=
  match goal with
    |- is_true (isSome (?g1.[? ?g2])) => change (is_true (isSome (g1.[? g2])))
  end.

(** State changes when recieving**)
Lemma no_state_change_rcv_different_parties N p ps :
  p \notin ps ->
  (state_map (foldr party_rcv_step_world N ps)).[? p] = (state_map N).[? p].
Proof.
  elim: ps p=> //= p' ? IH p. rewrite inE.
  case: _/eqP=> //=> H1 ?. rewrite {3}/party_rcv_step_world.
  fix_this. 
  case: (_.[? p']) => [?|] //=. case: (~~_)=> //=.
  - by rewrite fnd_set; move: H1=>/eqP; case: (_ == _)=> //= _; rewrite IH.
  - by case: AdversarialRcv=> >; rewrite broadcast_adv_msgs_preserves_state IH.
  - by rewrite IH.
Qed.

Lemma no_state_change_bake_different_parties N p ps :
  p \notin ps ->
  (state_map (foldr party_bake_step_world N ps)).[? p] = (state_map N).[? p].
Proof.
  elim: ps p=> //= p' ? IH p. rewrite inE.
  case: _/eqP=> //=> H1 ?. rewrite {3}/party_bake_step_world.
  fix_this.
  case: (_.[? p']) => [?|] //=. case: (~~_)=> //=.
  - case: honest_bake=> >. rewrite flood_msgs_preserves_state fnd_set.
      by move: H1=>/eqP; case: (_ == _)=> //= _;  rewrite IH.
  - by case: AdversarialBake=> >; rewrite broadcast_adv_msgs_preserves_state IH.
  - by rewrite IH.
Qed.

Lemma no_msg_change_for_different_parties N p ps :
  p \notin ps ->
  (collect_zero_pairs p (foldr party_rcv_step_world N ps)) = collect_zero_pairs p N.
Proof.
  rewrite /collect_zero_pairs. elim: ps p=> //= p' ps' IH p.
  rewrite inE. case: _/eqP=> //=> H1 H2.
  rewrite {1}/party_rcv_step_world.
  case: (_.[? _])=> //= [?|]; last by rewrite IH.
  case: (~~_) => //=.
  - rewrite -IH //=. elim: (msg_buff _)=> //= m ms IH'.
    rewrite negb_and. case eq : (cd m == 0)=> //=.
    + move: H1. case: (rcv m == p')/eqP=> //= [-> /eqP| _ _].
      * by rewrite eq_sym; case: (p' == p)=> //=.
      * by rewrite eq; case: (rcv m == p) => //=; apply/f_equal.
    + by rewrite eq /=.
  - case: AdversarialRcv=> nmsgs ? /=.
    rewrite /rmv_zero_msgs /flood_msgs_adv /=. elim: nmsgs=> [|m ls IH'] //=.
    + rewrite -IH //. elim: (msg_buff _)=> //= m ms IH'.
      move: H1=> /eqP. rewrite andbC negb_and [(cd m == 0) && _]andbC.
      case: (rcv m == p)/eqP=> //= [H|].
      * remember H as H1. move=> {HeqH1}. move: H=> -> -> //=. case (cd m == 0)=> //=.
        rewrite H1 eq_refl. by apply/f_equal.
      * rewrite orbC. case eq: (cd m == 0)=> //=.
        -- case: (rcv m == p')=> //=.
           rewrite eq /==>/eqP. by case (rcv m == p) => //=.
        -- by rewrite eq /= => _ _.
    + case: m=> m dm /=. rewrite filter_cat IH'.
      elim: (exec_order _)=> //= p'' ??. 
      by move: (delay12 (dm p''))=> [-> | ->] //=.
Qed.

Lemma single_party_rcv_step_state N p :
  N0 ⇓ N ->
  (state_map (foldr party_rcv_step_world N (exec_order N))).[? p]
  = (state_map (party_rcv_step_world p N)).[? p].
Proof.
  move=> H. move: (has_state_initP p H). rewrite /exists_state.
  move: (perm_exec_order0 H)=> /perm_mem ->. move: (uniq_exec_order H).
  elim: (exec_order N) => [ _| p' ps IH] //=.
  - by rewrite in_nil /party_rcv_step_world; case s: (_.[? _]).
  - rewrite inE. case: (_ == _)/eqP=> /=.
    + move=> -> /andP [H1 H2] H3. rewrite {3}/party_rcv_step_world.
      fix_this.
      move: H3. rewrite (no_state_change_rcv_different_parties _ H1).
      rewrite {6}/party_rcv_step_world=> H3.
      fix_this'.
      move:H3. case: ((state_map N).[? p'])=> //= l _. case: (~~ _)=> //=.
      * by rewrite !fnd_set eq_refl  /= no_msg_change_for_different_parties //.
      * do 2 !case: AdversarialRcv=> ?? //=.
        rewrite !broadcast_adv_msgs_preserves_state.
        by rewrite no_state_change_rcv_different_parties.
    + move=> H1 /andP [??] ?. rewrite {3}/party_rcv_step_world.
      fix_this.
      case: (_.[? p'])=> [l |] //=; last by apply IH. case: (~~ _) => //=.
      * by rewrite fnd_set; move: H1=> /eqP; case: (_ == _)=> //= _; apply/IH.
      * by case: AdversarialRcv => >; rewrite broadcast_adv_msgs_preserves_state IH.
Qed.

Lemma single_party_bake_step_state N p :
  N0 ⇓ N ->
  (state_map (foldr party_bake_step_world N (exec_order N))).[? p] =
  (state_map (party_bake_step_world p N)).[? p].
Proof.
  move=> H. move: (has_state_initP p H). rewrite /exists_state.
  move: (perm_exec_order0 H)=> /perm_mem ->. move: (uniq_exec_order H).
  elim: (exec_order _) => [ _| p' ps IH] //=.
  - by rewrite in_nil /party_bake_step_world; case s: (_.[? _]).
  - rewrite inE.
    case: (_ == _)/eqP=> /=.
    + move=> <- /andP [H1 H2] H3. rewrite {3 5 6}/party_bake_step_world.
      fix_this.
      move: H3. rewrite !(no_state_change_bake_different_parties _ H1).
      rewrite {18}/party_bake_step_world. move=> H3.
      fix_this'.
      move:H3. case h: ((state_map N).[? p]) =>[l|] //= _.
      rewrite baking_preserves_time. case: (~~ _)=> //=.
      * case honesty: (honest_bake _ _ _) => >;
          by rewrite !flood_msgs_preserves_state !fnd_set eq_refl.
      * do 2! case: AdversarialBake=> > //=.
        rewrite !broadcast_adv_msgs_preserves_state /=.
          by rewrite no_state_change_bake_different_parties.
    + move=> H1 /andP [H2 H3] ?. rewrite {3}/party_bake_step_world.
      fix_this.
      case: (_.[? p'])=> [l |] //=; last by apply IH.
      case: (~~ _) => //=.
      * case: honest_bake=> >. rewrite flood_msgs_preserves_state fnd_set.
        by move: H1=> /eqP; case: (_ == _)=> //= _; apply/IH.
      * case: AdversarialBake => > /=.
        by rewrite broadcast_adv_msgs_preserves_state /= IH.
Qed.

(* To be delived within [n] rounds for party [p] in state [N] *)
Definition tbd (n : nat) (p : Party) (N : GlobalState) : seq Block :=
  [seq get_block (msg mt) | mt <- (msg_buff N) & (cd mt == n) && (rcv mt == p)].

Arguments extend_tree_l _ _/.  

Lemma tree_delivery_extension b msgs l:
  b \in allBlocks (tree (foldr process_msg l msgs))
  = (b \in ((allBlocks (tree l)) ++  [seq get_block msg | msg <- msgs])).
Proof.
  elim: msgs l=> [| m ms IH] l //=.
  - by rewrite mem_cat; case: (_ \in _).
  - rewrite {1}/process_msg. case: m=> b' //=.
    move: (IH l). 
    case: foldr=> > /= {}IH.
    rewrite all_extend mem_cat IH !mem_cat mem_seq1 inE. 
    by case: (_ == _); do 2! case: (_ \in _). 
Qed.

Lemma exists_state_bake p p' N :
  exists_state p N = exists_state p (party_bake_step_world p' N).
Proof.
  rewrite {1}/party_bake_step_world.
  case s: (_.[?_])=> //= >. case: (~~_)=> //=.
  - case: honest_bake=> >.
    rewrite/exists_state flood_msgs_preserves_state fnd_set.
      by case: (_ == _)/eqP=> //= ->; rewrite s. 
  - by case: AdversarialBake=> >; rewrite /exists_state broadcast_adv_msgs_preserves_state. 
Qed. 

Lemma exists_state_bakes p ps N :
  exists_state p N = exists_state p (foldr party_bake_step_world N ps).
Proof. by elim: ps=> //= > ->; rewrite -exists_state_bake. Qed. 

Lemma exists_state_recieve p N :
  exists_state p (party_rcv_step_world p N) = exists_state p N .
Proof. 
  rewrite /exists_state /party_rcv_step_world.
  case eq: ((state_map N).[? _])=> //= [l|]; last by rewrite eq.  
  case: (~~_)=> //=.
  - by rewrite fnd_set eq_refl.  
  - by case: AdversarialRcv=> >; rewrite broadcast_adv_msgs_preserves_state eq.
Qed. 

Lemma exists_state_recieves p ps N :
  exists_state p N -> exists_state p (foldr party_rcv_step_world N ps).
Proof.
  elim: ps N => //= p' ps IH N /IH H.
  rewrite /exists_state {3}/party_rcv_step_world. 
  fix_this''.   
  case: (_.[? p'])=> //= l. case: (~~_)=> //=.
  - by rewrite fnd_set; case: (_ == _).
  - by case: AdversarialRcv=> >; rewrite broadcast_adv_msgs_preserves_state.
Qed.

Lemma only_msgs_for_init N p:
  p \notin InitParties -> N0 ⇓ N -> all (fun mt => rcv mt != p) (msg_buff N).
Proof.
  move=> H. elim=> // N' N'' [] //= {N'} {N''} N' H1 H2 IH.
  - move: (perm_exec_order0 H2) H=>/perm_mem -> H.
    elim: (exec_order _)=> //= p' ps IH' /=.
    rewrite {1}/party_rcv_step_world.
    case: (_.[?_])=> //= l. case: (~~_)=> //=.
    + by rewrite (subset_all _ IH') //=; apply/filter_subset.
    + case: AdversarialRcv=> //= dms ?. 
      rewrite/rmv_zero_msgs //=  /=. elim dms=> //=.
      * rewrite  (subset_all _ IH') //=. by apply: filter_subset.
      * move => [? dm] dms' IH'' /=.
        rewrite broadcast_adv_msgs_preserves_order all_cat.
        apply/andP. constructor; last done.
        move: H. rewrite rcvs_preserves_order. elim: (exec_order _)=> //=.
        clear. move=> p' ps IH. rewrite inE negb_or=> /andP [H1 H2].
        by apply/andP; constructor;[rewrite eq_sym |rewrite IH]. 
  - move: (perm_exec_order0 H2) H=>/perm_mem -> H.
    elim: (exec_order _)=> //= p' ps IH' /=.
    rewrite {1}/party_bake_step_world.
    case: (_.[?_])=> //= l. case: (~~_)=> //=.
    + case: honest_bake=> ms ?. elim: ms=> //= m ms IH''.
      rewrite flood_msgs_preserves_order bakes_preserves_order all_cat. 
      apply/andP; constructor; last done. move: H.
      elim: (exec_order _)=> //=.
      clear. move=> p' ps IH. rewrite inE negb_or=> /andP [H1 H2].
        by apply/andP; constructor;[rewrite eq_sym |rewrite IH]. 
    + case: AdversarialBake=> //= dms ?. 
      rewrite/rmv_zero_msgs //=  /=. elim dms=> //=.
      move => [? dm] dms' IH'' /=. 
      rewrite broadcast_adv_msgs_preserves_order /=. 
      rewrite all_cat. apply/andP. constructor; last done.
      move: H. rewrite bakes_preserves_order. elim: (exec_order _)=> //=.
      clear. move=> p' ps IH. rewrite inE negb_or=> /andP [H1 H2].
        by apply/andP; constructor;[rewrite eq_sym | rewrite IH]. 
  - by move: IH; elim: (msg_buff _)=> //= ?? IH /andP [-> ?]; rewrite IH. 
  - by rewrite (perm_all _ H2).
Qed. 

Lemma all_msgs_delivered N p: N0 ⇓ N -> ~N @ Ready -> tbd 0 p N = [::].
Proof.
  move: (in_or_not_in p InitParties)=> [].
  { move=> /only_msgs_for_init H /H. rewrite /tbd => {} + _. 
    elim: (msg_buff _)=>//= m ms IH /andP [].
      by case: (_ == _)=> // _; rewrite andbC. } 
  move=> + H1; move: H1. elim=> // {} N N' [] //= {} {N'} N.
  (* Deliver step *)
  - move=> H1 H2 H3 /= H4. move: (H4).
    move: (perm_exec_order0 H2)=> /perm_mem -> {H3} H5 _.
    move: H5 (uniq_exec_order H2). rewrite /tbd /=.
    elim (exec_order _)=> //= p' ps' IH.
    rewrite inE=> /orP [/eqP <- /andP [H3 H5] |].
    + rewrite {1}/party_rcv_step_world. move: H4.
      rewrite -(has_state_initP p H2)=> /(exists_state_recieves ps').
      rewrite /exists_state. case: (_.[? _])=> //= l _. case: (~~_)=> //=.
      * elim: (msg_buff _) => //= mt ?. rewrite negb_and.
        case eq: (cd mt == 0) => //=.
        -- by case eq1: (rcv mt == p) => //=; rewrite eq eq1.
        -- by rewrite eq.
      * case: AdversarialRcv=> mds b. rewrite /rmv_zero_msgs /=.
        elim: mds=> /=.
        { elim: (msg_buff _) => //= mt ?. rewrite negb_and.
          case eq: (cd mt == 0) => //=.
          -- by case eq1: (rcv mt == p) => //=; rewrite eq eq1.
          -- by rewrite eq. }
        { move=> [] m d mds' IH' /=. rewrite filter_cat map_cat IH' cats0.
          elim : (exec_order _)=> //= p'' ?.
          move: (delay12 (d p'')). by case=> ->. }
    + move /IH => {H4} H3 /= /andP [H4 /H3 H5].
      rewrite {1}/party_rcv_step_world. case: (_.[? _]) => //= l.
      case: (~~_)=> //=.
      * set p1 := (fun _ => _ && _). set p2 := (fun _ => ~~ _).
        by rewrite -filter_predI (eq_filter (predIC p1 p2)) filter_predI (map_nil H5).
      * case: AdversarialRcv=> msgd b /=. rewrite /rmv_zero_msgs /=.
        elim msgd=> //= [|md msd' IH'].
        -- set p1 := (fun _ => _ && _). set p2 := (fun _ => ~~ _).
             by rewrite -filter_predI (eq_filter (predIC p1 p2)) filter_predI (map_nil H5).
        -- case: md => ? d //=.
           rewrite filter_cat map_cat IH' cats0. elim: (exec_order _)=> //= p'' ??.
           by move: (delay12 (d p'')); case=> ->.
  (* Bake step *)
  - move=> H1 H2 H3 /H3. rewrite H1 //= /tbd => H4 _. 
    elim: (exec_order _)=> //= [|p' ps IH]; first by rewrite H4.
    rewrite {1}/party_bake_step_world. case: (_.[? _])=> // l. case: (~~_)=> /=.
    + case: honest_bake=> ms l' /=.
      elim ms=> //= m ms' IH' /=. rewrite filter_cat map_cat IH' cats0.
        by elim: (exec_order _)=> //=.
    + case: AdversarialBake=> + ?.  
      elim=> //= m ? IH' /=. case: m=> //= ? dm. rewrite filter_cat map_cat IH' cats0.
      elim: (exec_order _) => //= p'' ?.
      by move: (delay12 (dm p'')); case=> ->.
  (* Permutation step *)
  - move=> ? perm_H _. do ! move=> IH /IH {IH}. move=> /perm_nilP H.
    apply/perm_nilP/(perm_trans _ H)/perm_map/perm_filter.
      by rewrite perm_sym.
Qed.

Lemma all_msgs_delayed N:
  N0 ⇓ N -> ~N @ Ready -> all (fun mt => (cd mt) > 0) (msg_buff N).
Proof.
  move=> H1 H2. move: (@all_msgs_delivered N).
  rewrite/tbd. elim: (msg_buff _)=> //= m ms IH H. apply/andP. constructor.
  - case: m H => m p d H. move: (H p H1 H2). rewrite eq_refl.
      by case eq: (_==_)=> //= _;move: eq H; case: d. 
  - apply/IH. move=> p _ _. move: (H p H1 H2).
      by do 2! case: (_==_).
Qed. 

Lemma all_msgs_leq_than_2_delayed N:
  N0 ⇓ N -> all (fun mt => (cd mt) <= 2) (msg_buff N).
Proof.
  elim=> //= ?? []; clear; move=> N // H1 H2 IH.  
  - move=> /=. elim: (exec_order _)=> //= p ps IH'.
    rewrite {1}/party_rcv_step_world. case: (_.[?_])=> //= l.
    case: (~~_)=> //=.
    + apply/subset_all=> //; by [apply/filter_subset|]. 
    + case: AdversarialRcv => + ?. elim=> //=.
      * apply/subset_all=> //; by [apply/filter_subset|]. 
      * move=> [? dm] dms ? //=. rewrite all_cat. apply/andP; constructor; last done. 
        elim: (exec_order _)=> //= p' ??. apply/andP; constructor; last done.
          by move: (delay12 (dm p'))=> [-> | ->].
  - elim: (exec_order _)=> //= p ps IH'. rewrite {1}/party_bake_step_world.
    case: (_.[?_])=> //= l. case: (~~_)=> //=.
    + case: honest_bake=> ms ?. elim ms=> //= ?? IH'' //=.
      rewrite  all_cat. apply/andP; constructor; last done. 
      by elim: (exec_order _).
    + case: AdversarialBake => //= + _. elim=> //=.
      move=> [m dm] dms IH'' //=. rewrite all_cat. apply/andP; constructor; last done. 
      elim: (exec_order _)=> //= p' ??. apply/andP; constructor; last done.
        by move: (delay12 (dm p'))=> [-> | ->].
  - move: IH=> /=. elim: (msg_buff _)=> //= ?? IH' /andP [H3 H4].
    apply/andP; constructor;  [|by apply/IH']. 
    apply/leq_trans; last by exact H3. rewrite subn1. apply/leq_pred. 
  - by rewrite (@perm_all _ _ _ _ H2). 
Qed.

Lemma delivery_blocktree p N l l':
  is_honest p ->
  (has_state p N l) ->
  (has_state p (party_rcv_step_world p N) l') ->
  allBlocks (tree l') =i allBlocks (tree l) ++ tbd 0 p N.
Proof.
  rewrite/has_state /party_rcv_step_world /is_corrupt /tbd => /eqP -> ->.
  rewrite/fetch_msgs /collect_zero_pairs /rmv_zero_msgs /= fnd_set eq_refl => [] [] <-.
  elim: (msg_buff _)=> [|> IH] //=; first by rewrite cats0.
  case: (_ && _)=> //=. rewrite /process_msg /get_block.
  case: (msg _)=> //= >. move: IH.
  case: foldr=> > /= IH. 
  rewrite all_extend mem_cat IH !mem_cat !inE . 
  by case: (_==_); do 2 case: (_ \in _). 
Qed.

Lemma exists_rcv_step_pres N p :
  exists_state p (party_rcv_step_world p N) -> exists_state p N.
Proof.
  rewrite /exists_state /party_rcv_step_world.
  case eq: ((state_map N).[? _])=> //=.
  by rewrite eq.
Qed.

Lemma exists_bake_step_pres N p :
  exists_state p (party_bake_step_world p N) -> exists_state p N.
Proof.
  rewrite /exists_state /party_bake_step_world.
  case eq: ((state_map N).[? _])=> //=.
  by rewrite eq.
Qed.

Lemma pred_1_not_0_eq :
  forall p p', [fun H => (cd H == 1) && (rcv H == p) && ~~ ((cd H == 0) && (rcv H == p'))]
          =1 [fun H => (cd H == 1) && (rcv H == p)]. 
Proof. by move=> ?? h /=; case eq: (cd h == 1)/eqP=> [->|] //=; case: (_ == _). Qed. 

Lemma pred_2_not_0_eq :
  forall p p', [fun H => (cd H == 2) && (rcv H == p) && ~~ ((cd H == 0) && (rcv H == p'))]
          =1 [fun H => (cd H == 2) && (rcv H == p)]. 
Proof. by move=> ?? h /=; case eq: (cd h == 2)/eqP=> [->|] //=; case: (_ == _). Qed. 

Lemma one_message_each (dm : DelayMap) m p:
  forall ps, p \in ps -> uniq ps ->
              [seq get_block (msg H)
              | H <- [seq mkMessageTuple m r (dm r) | r <- ps]
                & (cd H == 1) && (rcv H == p)]
                ++ [seq get_block (msg H)
                   | H <- [seq mkMessageTuple m r (dm r) | r <- ps]
                     & (cd H == 2) && (rcv H == p)]
              =i [:: get_block m]. 
Proof.
  elim => //= p' ps IH.
  rewrite inE. move=> /orP [/eqP e| H] /andP [H1 H2].
  - rewrite e eq_refl. move: (delay12 (dm p')) => [-> | ->] //= b.
    + rewrite inE inE. case: (_ == _) => //=.
      move: H1. clear. elim: ps=> //= p'' ps' IH.
      rewrite inE negb_or=> /andP [H1 H2]. move: H1.
      rewrite eq_sym. case: (p'' == p') => //= _.
        by rewrite andbC /= andbC /= IH.
    + rewrite mem_cat. rewrite inE inE orbC. case: (_ == _) => //=.
      move: H1. clear. elim: ps=> //= p'' ps IH.
      rewrite inE negb_or=> /andP [H1 H2]. move: H1.
      rewrite eq_sym. case: (p'' == p') => //= _.
        by rewrite andbC /= andbC /= IH.
  - move: (in_not_in H H1). rewrite eq_sym. case: (_ == _)=> //= _.
    rewrite andbC /= andbC /=. by apply: IH. 
Qed. 

Lemma delivery_tbd_eqaulity N p1 p2:
  let N' := (foldr party_rcv_step_world N (exec_order N)) in 
  uniq (exec_order N) ->
  p1 \in (exec_order N) ->
  p2 \in (exec_order N) ->
  exists X, (tbd 1 p1 N' ++ tbd 2 p1 N' =i tbd 1 p1 N ++ tbd 2 p1 N ++ X) /\
       (tbd 1 p2 N' ++ tbd 2 p2 N' =i tbd 1 p2 N ++ tbd 2 p2 N ++ X).
Proof.
  move=> N'. rewrite /N' => {N'}. move => u_order p1_in p2_in. 
  elim: (exec_order _) => /=; first by (exists [::]; constructor; rewrite cats0).
  move=> p' ps [X]. set N' := foldr _ _ _. move=> IH. rewrite /party_rcv_step_world.
  case: (_.[? _]); last by (exists X; apply: IH). move=> l. case: (~~_)=> //=.
  + exists X. rewrite /tbd /= -4!filter_predI 4!/predI 4!/[pred _ | _] //=.
    move: (pred_1_not_0_eq p1 p') (pred_2_not_0_eq p1 p').
    move: (pred_1_not_0_eq p2 p') (pred_2_not_0_eq p2 p').
    by do 4! move=> /eq_filter ->. 
  + case: AdversarialRcv=> + ?. rewrite /tbd. elim=> //=.
    * exists X. rewrite /= -4!filter_predI 4!/predI 4!/[pred _ | _] //=.
      move: (pred_1_not_0_eq p1 p') (pred_2_not_0_eq p1 p').
      move: (pred_1_not_0_eq p2 p') (pred_2_not_0_eq p2 p').
        by do 4! move=> /eq_filter ->. 
    * move=> m mdm [X1]. case: m=> m dm.
      set broad_rest := (flood_msgs_adv _ _).
      have H6: perm_eq (exec_order N) (exec_order broad_rest).
      { rewrite /broad_rest. clear. elim: mdm=> //=.
        - rewrite /N'. clear. elim: ps=> //= p ps IH.
          rewrite {1}/party_rcv_step_world.
          case: (_.[? _]). rewrite /fetch_msgs /=. case: (~~ is_corrupt _) => //= _.
          case: AdversarialRcv => //= H _.
          suff: forall N', exec_order (flood_msgs_adv H (rmv_zero_msgs p N'))
                      = exec_order N' by move->.
          elim H=> // m ? IH' /=.
          + by move=> N'; case: m=> //=.
          + by rewrite IH.
        - by move=> [] b c; elim => //=. }
      rewrite -!/(tbd _ _ _) //=. move=> [IH1 IH1'].
      set N'' := flood_msg_adv _ _ _. 
      have: tbd 1 p1 N'' ++ tbd 2 p1 N'' =i tbd 1 p1 N ++ tbd 2 p1 N ++ (get_block m :: X1).
      { rewrite /N'' /flood_msg_adv /tbd /= !filter_cat !map_cat -!/(tbd _ _ _).
        set ab1 := [seq _ | _ <- _]. set ab2 := [seq _ | _ <- _].
        suff : ab1 ++ ab2  =i [:: get_block m].
        { move=> H8 b. move: (H8 b) (IH1 b). rewrite !mem_cat inE !inE.
            by do 7! case: (_ \in _); case (_ == _). }
        rewrite one_message_each //.
        - by rewrite -(perm_mem H6). 
        - by rewrite -(perm_uniq H6). }
      have: tbd 1 p2 N'' ++ tbd 2 p2 N'' =i tbd 1 p2 N ++ tbd 2 p2 N ++ (get_block m :: X1).
      { rewrite /N'' /flood_msg_adv /tbd /= !filter_cat !map_cat -!/(tbd _ _ _).
        set ab1 := [seq _ | _ <- _]. set ab2 := [seq _ | _ <- _]. 
        suff : ab1 ++ ab2 =i [:: get_block m].
        { move=> H8 b. move: (H8 b) (IH1' b). rewrite !mem_cat inE !inE.
            by do 7! case: (_ \in _); case (_ == _). }
        rewrite one_message_each //.
        - by rewrite -(perm_mem H6). 
        - by rewrite -(perm_uniq H6). }
        by exists (get_block m :: X1); constructor.
Qed.

Lemma bake_tbd_eqaulity N p1 p2:
  let N' := foldr party_bake_step_world N (exec_order N) in 
  uniq (exec_order N) ->
  p1 \in (exec_order N) ->
  p2 \in (exec_order N) ->
  exists X, (tbd 1 p1 N' ++ tbd 2 p1 N' =i tbd 1 p1 N ++ tbd 2 p1 N ++ X) /\
       (tbd 1 p2 N' ++ tbd 2 p2 N' =i tbd 1 p2 N ++ tbd 2 p2 N ++ X).
Proof.
  move=> N' H H1 H2. rewrite /N'=> {N'}. 
  elim: (exec_order _) => /=; first by (exists [::]; constructor; rewrite cats0).
  move=> p' ps [X]. set N' := foldr _ _ _. move=> IH.
  rewrite /party_bake_step_world. case: (_.[? _]); last (by exists X; apply: IH).
  have u: uniq (exec_order N') by move: H; rewrite bakes_preserves_order.
  case: (~~_)=> l //=.
  - rewrite /honest_bake /=. case: Winner=> //=.
    + set nbm := BlockMsg _.
      set N'' := upd_local _ _ _. 
      rewrite /flood_msg /= /tbd /= !filter_cat !map_cat. 
      have H6: [seq get_block (msg mt)
               | mt <- [seq {| msg := nbm; rcv := r; cd := 1 |} | r <- _]
                 & (cd mt == 2) && (rcv mt == _)] = [::]. 
      { by move=> ?; elim=> //=. }
      rewrite 2!H6 2!cat0s. move: IH => [IH1 IH2].
      have H7:  forall r, r \in (exec_order N') ->
                           [seq get_block (msg mt)
                           | mt <- [seq {| msg := nbm; rcv := r; cd := 1 |}
                                  | r <- exec_order N']
                             & (cd mt == 1) && (rcv mt == r)]
                          = [:: get_block nbm].
      { move: u. clear. elim: (exec_order _)=> //=.
        move=> p ps' IH /andP [H /IH {} IH] p''.
        rewrite inE. case: (_ == _)/eqP => [-> _|] //=.
        - rewrite eq_refl //=.
          suff: [seq get_block (msg mt)
                | mt <- [seq {| msg := nbm; rcv := r; cd := 1 |} | r <- ps']
                  & (cd mt == 1) && (rcv mt == p)] = [::] by move->.
          move: H. clear. elim: ps'=> //= p'' ps' IH.
            by rewrite inE negb_or eq_sym; case: (_ == _).
        - by move/eqP; rewrite eq_sym; case: (_ == _)=> //= _ H1; apply/IH. }
      do 2 (rewrite H7; last by rewrite bakes_preserves_order).
      exists (get_block nbm :: X). rewrite -[_ :: X]cat1s -2!catA.
      constructor; move=> b; rewrite mem_cat; [rewrite IH1 | rewrite IH2];
      rewrite !mem_cat; by (do! case: (_ \in _)).
    + by (exists X).
  - case: AdversarialBake => + ?. rewrite /tbd /=.
    elim=> //=; first by (exists X). move=> m mdm [X1].
    case: m=> m dm. set broad_rest := (flood_msgs_adv _ _).
    have H6: perm_eq (exec_order N) (exec_order broad_rest)
      by rewrite broadcast_adv_msgs_preserves_order /N' bakes_preserves_order.
    rewrite -!/(tbd _ _ _) //=.  move=> [IH1 IH1'].
    set N'' := flood_msg_adv _ _ _.
    have: tbd 1 p1 N'' ++ tbd 2 p1 N'' =i tbd 1 p1 N ++ tbd 2 p1 N ++ (get_block m :: X1).
    { rewrite /flood_msg_adv  /tbd /= !filter_cat !map_cat -!/(tbd _ _ _).
      set ab1 := [seq _ | _ <- _]. set ab2 := [seq _ | _ <- _].
      suff : ab1 ++ ab2  =i [:: get_block m].
      { move=> + b. move: (IH1 b)=> + /(_ b). 
        rewrite !mem_cat inE !inE.
          by do 7! case: (_ \in _); case (_ == _). }
      rewrite one_message_each //.
      - by rewrite -(perm_mem H6). 
      - by rewrite -(perm_uniq H6). }
    have: tbd 1 p2 N'' ++ tbd 2 p2 N'' =i tbd 1 p2 N ++ tbd 2 p2 N ++ (get_block m :: X1).
    { rewrite /N'' /flood_msg_adv /tbd /= !filter_cat !map_cat -!/(tbd _ _ _).
      set ab1 := [seq _ | _ <- _]. set ab2 := [seq _ | _ <- _].
      suff : ab1 ++ ab2  =i [:: get_block m].
      { move=> + b. move: (IH1' b)=> + /(_ b).
        rewrite !mem_cat inE !inE.
          by do 7! case: (_ \in _); case (_ == _). }
      rewrite one_message_each //.
      - by rewrite -(perm_mem H6). 
      - by rewrite -(perm_uniq H6). }
      by move=> H7 H8 ; exists (get_block m :: X1); constructor.
Qed.

Lemma tbd_mem_eq N n nmb p :
  (msg_buff N) =i nmb ->
  tbd n p N =i tbd n p (N[[msg_buff := nmb]]). 
Proof. by rewrite/tbd  /= => ?; apply/map_mem_eq/filter_mem_eq. Qed. 


Lemma inc_tbd_dec p N n:
  n > 0 -> all (fun mt => (cd mt) > 0) (msg_buff N) ->
  tbd (n-1) p (inc_round (round_tick N) [[progress := Ready]]) = tbd n p N.
Proof.
  move=> ? /=. rewrite/tbd /=.
  elim: (msg_buff _)=> //= mt mts IH /andP [??].
  rewrite andbC [(cd mt == _) && _]andbC.
  by case: (_==_)=>//=; [rewrite -sub1 //=|]; [case: (_==_)=> //=|]; rewrite IH.
Qed. 

Lemma inc_tbd2_is_nil p N :
  N0 ⇓ N ->
  tbd 2 p (inc_round (round_tick N) [[progress := Ready]]) = [::].
Proof. 
  move/all_msgs_leq_than_2_delayed=> /=. rewrite/tbd /=.
  elim: (msg_buff N)=> //= m ms IH /andP [H1 H2].
  suff: (cd m -1 == 2) = false by move->; rewrite IH . 
  by move: H1; case: (cd m)=> //=; do 2! case=> //=. 
Qed.

Lemma tbd2_at_ready_is_nil p N :
  N0 ⇓ N -> N @ Ready  -> tbd 2 p N = [::].
Proof.
  elim=> //= {} ?? [] // {} N.
  - by move=> _ /inc_tbd2_is_nil ->. 
  - move=> > ?? H /H H1. apply/perm_nilP. rewrite -H1 perm_sym /tbd .
    by apply/perm_map/perm_filter. 
Qed.
 
Lemma tbd_rcv_subset p p' N :
  {subset tbd 1 p N <= tbd 1 p (party_rcv_step_world p' N)}.
Proof.
  rewrite /party_rcv_step_world. case: (_.[?_])=> //=. case: (~~_)=> //= [?|? ].
  - rewrite /tbd /= => b /mapP [m + ->].
    rewrite mem_filter=> /andP [/andP [/eqP H1 /eqP H2] ].
    elim: msg_buff=> //= m' ms IH.
    rewrite inE=> /orP [/eqP <-| /IH]; last first. 
    + by case: (~~_)=> //=; case: (_ && _)=> //=; rewrite inE orbC=> ->. 
    + by rewrite negb_and H1 //= H1 H2 2!eq_refl //= mem_head.
  - case: AdversarialRcv=> //= ms ?. rewrite/tbd /=.
    move=> b /mapP [m + ->]. rewrite mem_filter=> /andP [/andP [/eqP H1 /eqP H2] ].
    elim: ms=> //=.
    + elim: msg_buff=> //= m' ms IH.
      rewrite inE=> /orP [/eqP <-|/IH ]; last first. 
      * by case: (~~_)=> //=; case: (_ && _)=> //=; rewrite inE orbC=> ->. 
      * by rewrite negb_and H1 //= H1 H2 2!eq_refl //= mem_head.
    + case=> > IH /IH {} IH.
      by rewrite /flood_msg_adv /= !filter_cat !map_cat mem_cat orbC IH. 
Qed. 

Lemma tbd_rcvs_subset p ps N :
  {subset tbd 1 p N <= tbd 1 p (foldr party_rcv_step_world N ps)}.
Proof. by elim: ps => // > IH ; apply/(subset_trans IH)/tbd_rcv_subset. Qed.

Lemma tbd_bake_subset n p p' N :
  {subset tbd n p N <= tbd n p (party_bake_step_world p' N)}.
Proof.
  rewrite /party_bake_step_world.
  case: (_.[?_])=> //=. case: (~~_)=> //= [?|? ].
  - rewrite/honest_bake/=. case: Winner=> > //=. rewrite /tbd=> H /=.
    rewrite filter_cat map_cat mem_cat. apply/orP.
      by constructor 2. 
  - case: AdversarialBake=> //= ms ?. rewrite/tbd /=.
    elim ms=> //= [ [] mt mt'] mts //=. rewrite filter_cat map_cat=> H1 b H2.
    rewrite mem_cat broadcast_adv_msgs_preserves_order. 
    apply/orP. constructor 2.
      by apply H1. 
Qed. 

Lemma tbd_bakes_subset n p N ps :
  {subset tbd n p N <= tbd n p (foldr party_bake_step_world N ps)}.
Proof. by elim: ps => // > IH ; apply/(subset_trans IH)/tbd_bake_subset. Qed.

Lemma tbd_bakes_in_subset p p' N n :
  N0 ⇓ N ->
  is_honest p ->
  p \in exec_order N ->
        {subset tbd n p' (party_bake_step_world p N)
         <= tbd n p' (foldr party_bake_step_world N (exec_order N)) }.
Proof.
  rewrite honest_not_corrupt. move/uniq_exec_order=> + A. 
  elim exec_order=> //= p'' ps IH /andP [/no_state_change_bake_different_parties H1 /IH H2].
  rewrite inE => /orP [/eqP K |]; last first.
  - move/H2 => H3. apply/subset_trans.
    + exact H3.
    + by apply/tbd_bake_subset. 
  - move: A. rewrite K=> A ?. rewrite {1 2}/party_bake_step_world H1.
    case: (_.[?_])=> //=; last by apply/tbd_bakes_subset.
    move=> ?. rewrite A.  
    + rewrite/honest_bake  /= baking_preserves_time.
      case: Winner=> > //=; last first.
      * by rewrite /tbd //= => /(tbd_bakes_subset ps).  
      * rewrite /tbd //= !filter_cat !map_cat.
        rewrite !mem_cat bakes_preserves_order=> /orP [-> |] //=.
        by rewrite -!/(tbd _ _ _) orbC=> /tbd_bakes_subset ->.
Qed. 

Lemma honest_bake_send p l1 l2 N:
  N0 ⇓ N -> 
  is_honest p ->
  has_state p N l1 ->
  has_state p (party_bake_step_world p N) l2 ->
  exists Y, allBlocks (tree l2) =i allBlocks (tree l1) ++ Y /\
       forall p', p' \in (exec_order N) ->
             {subset Y <= tbd 1 p' (foldr party_bake_step_world N (exec_order N))}. 
Proof.
  move=> A H1 H3.
  have H2: p \in exec_order N.
  { move: (perm_exec_order0 A)=> /perm_mem <-.
      by rewrite -(has_state_initP p A) /exists_state H3. }
  rewrite {1}/party_bake_step_world H3. move: H1.
  rewrite honest_not_corrupt/honest_bake/has_state => H1. rewrite H1 //=. 
  case w: Winner=> //=; rewrite fnd_set eq_refl ;
  [|by case=> ->; exists [::]; constructor; [rewrite cats0|] ]. 
  set nb := MkBlock _ _ _ _. case=> <-. 
  exists [:: nb]. rewrite /nb. case: l1 H3 w nb => > H3 w nb. constructor; first by move => >; rewrite all_extend.
  move=> p' H. apply/subset_trans; last first.
  - apply/(tbd_bakes_in_subset A). rewrite honest_not_corrupt.
    + exact H1.
    + exact H2.
  - move=> ?. rewrite inE=> /eqP ->.
    rewrite {1}/party_bake_step_world/honest_bake H3 H1 /= w /tbd /=.
    rewrite filter_cat map_cat mem_cat. apply/orP. constructor. 
    set nb' := MkBlock _ _ _.  
    move: H. elim: exec_order=> //= p'' ps IH. 
    rewrite inE=> /orP [/eqP ->| ]. 
    + by rewrite eq_refl /= mem_head.  
    + by move=> /IH; case: (_ == _)=> //=; rewrite mem_head. 
Qed. 

(* Important lemma that describes the flow of messages in the system.
   This has the implications that if there is just one round of no
   winners then there will actually be consensus. *)   
Lemma block_equality_inv N p p' :
  N0 ⇓ N -> forall l l',
    is_honest p -> is_honest p' -> has_state p N l -> has_state p' N l' ->
    allBlocks (tree l) ++ tbd 0 p N ++ tbd 1 p N ++ tbd 2 p N
    =i allBlocks (tree l') ++ tbd 0 p' N ++ tbd 1 p' N ++ tbd 2 p' N.
Proof.
  move=> H1. move: H1 (H1).
  elim=> [????? |] //.
  { move=> /tree_gb_init -> /tree_gb_init -> ?. by rewrite !mem_cat !tree_gb_gb. }
  move=> {} N N' [] //.
  (* Delivery step *)
  - move=> N'' H1 H2 H3 H4 l1 l2 H5 H6 H7 H8.
    set N''' := (foldr party_rcv_step_world N'' _ [[progress := _]]).
    set tdb_p := tbd 0 _ _. set tdb_p' := tbd 0 _ _.
    have: tdb_p = [::] by apply/all_msgs_delivered=> //=.
    have: tdb_p' = [::] by apply/all_msgs_delivered=> //=. 
    move=> ->->. rewrite !cat0s /N''' => {tdb_p' tdb_p}.
    move: H7 H8. rewrite /has_state !single_party_rcv_step_state // => s1 s2.
    move: (s1) => /has_exists_state /exists_rcv_step_pres.
    rewrite /exists_state. case s3: (_.[?_])=> [l3 |] // _.
    move: (s2) => /has_exists_state /exists_rcv_step_pres.
    rewrite /exists_state. case s4: (_.[?_])=> [l4 |] // _.
    move: (H3 H2 l3 l4 H5 H6 s3 s4). move: (delivery_blocktree H5 s3 s1).
    move: (delivery_blocktree H6 s4 s2). move=> H7 H8 H9.
    have: allBlocks (tree l1) ++ tbd 1 p N'' ++ tbd 2 p N''
          =i allBlocks (tree l2) ++ tbd 1 p' N'' ++ tbd 2 p' N''
      by move=> b; rewrite !mem_cat H7 H8 -!mem_cat -!catA.
    rewrite //= /tbd /= -!/(tbd _ _ _) => H. move: (uniq_exec_order H2).
    move: (has_state_initP p H2) (has_state_initP p' H2).
    rewrite /exists_state s3 s4 /=.
    move: (perm_exec_order0 H2)=> /perm_mem H10. rewrite !(H10 _).
    move: H. clear. move=> H /true_is_true A1 /true_is_true A2 A3.
    move: (delivery_tbd_eqaulity A3 A1 A2) => [X [H1 H2] ].
    move=> b. rewrite mem_cat H1. symmetry.
    rewrite mem_cat H2 -!mem_cat. move: H=> /(cat_mem_eq_r X).
      by rewrite -!catA.
  (* Bake step *)
  - clear. move=>N H1 H2 H3 H4 l1 l2 H5 H6.
    set N' := ((foldr _ _ _)[[progress := _]]).
    move=> H7  H8. set tdb_p := tbd 0 _ _. set tdb_p' := tbd 0 _ _.
    have: tdb_p = [::] by apply/all_msgs_delivered. 
    have: tdb_p' = [::] by apply/all_msgs_delivered. 
    move=> ->->. rewrite !cat0s=> {tdb_p tdb_p'}. move: H7 H8.
    rewrite /has_state !single_party_bake_step_state // => s1 s2.
    move: (s1) => /has_exists_state /exists_bake_step_pres.
    rewrite /exists_state. case s3: (_.[?_])=> [l3 |] // _.
    move: (s2) => /has_exists_state /exists_bake_step_pres.
    rewrite /exists_state. case s4: (_.[?_])=> [l4 |] // _.
    move: (H3 H2 l3 l4 H5 H6 s3 s4).
    set tdb_p := tbd 0 _ _. set tdb_p' := tbd 0 _ _.
    have: tdb_p = [::] by apply/all_msgs_delivered ; [| rewrite H1].
    have: tdb_p' = [::] by apply/all_msgs_delivered; [| rewrite H1]. 
    move=> ->->. rewrite !cat0s=> {tdb_p tdb_p'}.
    rewrite /tbd //= -!/(tbd _ _ _). move: s1 s2.
    rewrite -!/(has_state _ _ _)=> {N'}. set N' := foldr _ _ _.
    have H7: uniq (exec_order N) by rewrite uniq_exec_order.
    have H8: p \in (exec_order N). 
    { move: (perm_exec_order0 H2) (has_state_initP p H2)=> /perm_mem <-  <-.
        by rewrite /exists_state s3. } 
    have H9: p' \in (exec_order N). 
    { move: (perm_exec_order0 H2) (has_state_initP p' H2)=> /perm_mem <-  <-.
        by rewrite /exists_state s4. }
    move: (bake_tbd_eqaulity H7 H8 H9). rewrite -/N' => [] [X [A1 A2] ].
    move=> s1 s2. move/(cat_mem_eq_r X). rewrite -4!catA=> H10.
    move: (honest_bake_send H2 H5 s3 s1)=> [Y [B1 B2] ]. move: (B2 _ H9) => B3. 
    move: (honest_bake_send H2 H6 s4 s2)=> [Y' [C1 C2] ]. move: (C2 _ H8) => C3.
    move: B1 C1. rewrite -!/(mem_eq _ _)=> -> ->. rewrite /mem_eq=> b.
    rewrite 2!mem_cat -orbA orbC -2!mem_cat -!catA. move: b. rewrite -/(_ =i _). 
    apply/subset_mem_eq; first by  move=> ? /B3; rewrite !mem_cat=> ->; do 3! case: (_\in _). 
    apply/eq_mem_sym=> b.
    rewrite !mem_cat orbC -!mem_cat -!catA. move: b. rewrite -/(_ =i _). 
    apply/subset_mem_eq; first by move=> ? /C3; rewrite !mem_cat=> ->; do 2! case: (_\in _). 
    apply/eq_mem_sym. rewrite catA. apply/eq_mem_sym. rewrite catA. 
    move: A1 A2. rewrite -!/(mem_eq _ _)=> -> ->. rewrite /mem_eq=> b. 
    move: (H10 b). rewrite !mem_cat. by do ! case: (_ \in _). 
  (* Inc step *)
  -  move=> N'' H2 H3 IH H4 l l' H5 H6.
     have H7: all (fun mt : MessageTuple => 0 < cd mt) (msg_buff N'').
     { by rewrite all_msgs_delayed // H2. } 
     move: (@inc_tbd_dec p' N'' 1) (@inc_tbd_dec p N'' 1).
     change (1-1) with 0. move=> -> // ->//.  
     move: (@inc_tbd_dec p' N'' 2) (@inc_tbd_dec p N'' 2).
     change (2-1) with 1. move=> -> // ->//.  
     rewrite 2!(@inc_tbd2_is_nil _ _ H3) 2!cats0.
     rewrite /has_state /= -2!/(has_state _ _ _) /tbd /= => s1 s2.
     move: (@IH H3 _ _ H5 H6 s1 s2).
     set tdb_p := tbd 0 _ _. set tdb_p' := tbd 0 _ _.
     have: tdb_p = [::]. by apply/all_msgs_delivered; [| rewrite H2].
     have: tdb_p' = [::]. by apply/all_msgs_delivered; [| rewrite H2].
     by move=> ->->; rewrite !cat0s. 
  (* Perm parties step *)
  - move=>???? IH ???????. by apply: IH.
  (* Perm mb step  *)
  - clear. move=> N nmb /perm_mem H2 H3 IH H4 l l' H5 H6 s1 s2 b.
    move: (@IH H3 _ _ H5 H6 s1 s2 b). 
    by rewrite 6!mem_cat 6!(@tbd_mem_eq _ _ _ _ H2) -!mem_cat.
Qed. 

Lemma tbd_collect_msgs_eq p N :
  [seq get_block msg | msg <- [seq msg mt | mt <- collect_zero_pairs p N] ]
  = tbd 0 p N. 
Proof. by rewrite map_map. Qed. 

Lemma at_delivered_subset N p p' l1 l1':
  N0 ⇓ N -> is_honest p -> is_honest p' ->
  N @ Delivered -> has_state p N l1 ->
  has_state p' N l1' ->
  {subset allBlocks (tree l1) <= allBlocks (tree l1') ++ tbd 1 p' N}.
Proof. 
  move=> + honesty_p honesty_p'.
  elim=> // {} N N' [] // {N'} N; last first. 
  - move=> ???. do !move=> IH /IH {IH}.
    set s1 := _ ++ _. set s2 := _ ++ _.
    move=> H1 ? /H1 {H1}. suff: s1 =i s2 by move ->.
    by apply/perm_mem/perm_cat=> //; apply/perm_map/perm_filter.
  - move=> progress_N H IH _.
    rewrite /has_state /= -!/(has_state _ _ _) /tbd /= -/(tbd _ _ _). 
    set N' := foldr _ _ _. 
    rewrite /has_state !single_party_rcv_step_state // -!/(has_state _ _ _).
    move=> state_p1 state_p1'.
    have: exists_state p N.
    { by apply/exists_rcv_step_pres; rewrite /exists_state state_p1. }
    rewrite /exists_state. case state_p0: (_.[? _])=> [l0|] // _. 
    have: exists_state p' N.
    { by apply/exists_rcv_step_pres; rewrite /exists_state state_p1'. }
    rewrite /exists_state. case state_p0': (_.[? _])=> [l0'|] // _.
    have p_in: p \in exec_order N.
    { move: (perm_exec_order0 H)=> /perm_mem <-.
      by rewrite -(has_state_initP p H) /exists_state state_p0. }
    have p_in': p' \in exec_order N.
    { move: (perm_exec_order0 H)=> /perm_mem <-.
      by rewrite -(has_state_initP p' H) /exists_state state_p0'. }
    move=> b. 
    move: (delivery_blocktree honesty_p' state_p0' state_p1').
    rewrite mem_cat=> ->. rewrite -mem_cat -catA. 
    move: (delivery_blocktree honesty_p state_p0 state_p1).
    move->. move: b. rewrite -/({subset _ <= _}).
    have H': {subset tbd 1 p' N <= tbd 1 p' N'}. 
    apply/tbd_rcvs_subset. 
    move: (block_equality_inv H honesty_p honesty_p' state_p0 state_p0').
    rewrite tbd2_at_ready_is_nil // tbd2_at_ready_is_nil // 2!cats0=> H''. 
    move=> b H'''. move: (H'' b).
    rewrite catA mem_cat H''' /= catA mem_cat catA=> A. 
    rewrite mem_cat. move: A. case: (_\in _)=> //= A. 
      by apply H'.
Qed. 

Lemma at_bake_subset N p p' l l':
  N0 ⇓ N -> is_honest p -> is_honest p' -> N @ Baked ->
  has_state p N l -> has_state p' N l' ->
  {subset allBlocks (tree l) <= allBlocks (tree l') ++ tbd 1 p' N}.
Proof.
  move=> + honesty_p honesty_p'. elim=> // {} N N' [] // {N'} N; last first. 
  - move=> ???. do !move=> IH /IH {IH}. set s1 := _ ++ _. set s2 := _ ++ _.
    move=> H1 ? /H1 {H1}. suff: s1 =i s2 by move ->.
    by apply/perm_mem/perm_cat=> //; apply/perm_map/perm_filter.
  - move=> progress_N H IH _.
    rewrite /has_state /= -!/(has_state _ _ _) /tbd /= -/(tbd _ _ _). 
    set N' := foldr _ _ _. 
    rewrite /has_state !single_party_bake_step_state // -!/(has_state _ _ _).
    move=> state_p1 state_p1'.
    have: exists_state p N.
    { by apply/exists_bake_step_pres; rewrite /exists_state state_p1. }  
    rewrite /exists_state. case state_p0: (_.[? _])=> [l0|] // _. 
    have: exists_state p' N.
    { by apply/exists_bake_step_pres; rewrite /exists_state state_p1'. } 
    rewrite /exists_state. case state_p0': (_.[? _])=> [l0'|] // _.
    have p_in: p \in exec_order N.
    { move: (perm_exec_order0 H)=> /perm_mem <-.
      by rewrite -(has_state_initP p H) /exists_state state_p0. }
    have p_in': p' \in exec_order N.
    { move: (perm_exec_order0 H)=> /perm_mem <-.
      by rewrite -(has_state_initP p' H) /exists_state state_p0'. }
    move: (@honest_bake_send p l0 l N H honesty_p state_p0 state_p1).
    move=> [bs [l_eq_l0 H1] ]. move: (H1 p' p_in')=> {H1} bs_subset. 
    move: (@honest_bake_send p' l0' l' N H honesty_p' state_p0' state_p1').
    move=> [bs' [l'_eq_l0' _] ] b.
    rewrite l_eq_l0 !mem_cat l'_eq_l0' !mem_cat=> /orP [| /bs_subset ->];
                                                   last by rewrite orbC.
    rewrite -orbA orbC. case: (_ \in bs') => //=. rewrite orbC. 
    rewrite -!mem_cat. move: b.  rewrite -/({subset _ <= _}). apply/subset_trans.
    + by apply/(at_delivered_subset H honesty_p honesty_p' progress_N state_p0 state_p0'). 
    + by move=> ?; rewrite !mem_cat; case: (_ \in _)=> //= /tbd_bakes_subset ->. 
Qed.             

Lemma at_ready_subset N p p' l l':
  N0 ⇓ N -> is_honest p -> is_honest p' -> N @ Ready ->
  has_state p N l -> has_state p' N l' ->
  {subset allBlocks (tree l) <= allBlocks (tree l') ++ tbd 0 p' N}.
Proof.
  move=> + honesty_p honesty_p'.
  elim=> [_ /tree_gb_init -> /tree_gb_init -> ?|].
  - by rewrite mem_cat !tree_gb_gb=> ->.  
  - move=> {} N N' [] {N N'} //; last first. 
    + move=> ????. do !move=> IH /IH {IH}. 
      set s1 := _ ++ _. set s2 := _ ++ _. move=> H b /H.
      suff: s1 =i s2 by move ->.
        by apply/perm_mem/perm_cat=> //; apply/perm_map/perm_filter.  
    + move=> N progress_N H1 IH2.
      rewrite /has_state /= -!/(has_state _ _ _)=> _ state_p' state_p=> ? in_l'.
    change 0 with (1 - 1). 
    rewrite inc_tbd_dec //; last by apply/all_msgs_delayed=> //; rewrite progress_N. 
      by apply/(@at_bake_subset _ _ _ _ _ H1 honesty_p honesty_p' progress_N state_p' state_p).
Qed. 

(** *Main lemma needed for chain growth **)
(* The honest tree at the start of round a round will be a subset of
   any honest partys tree at the start of the next round this is the
   important lemma for proving that CG*)
Lemma honest_tree_subset N N' p l:
  N0 ⇓ N -> is_honest p -> N @ Ready -> N' @ Delivered ->
  N ⇓[0] N' -> has_state p N' l ->
  {subset allBlocks (honest_tree N) <= allBlocks (tree l)}.
Proof.
  move=> H honesty_p R D [d]. move: d D l H R. rewrite add0n.
  elim=> [-> //|]. move=> {} N' _ [] //=.
  (* All other cases than [Deliver] are immediately closed
     (contradiction for Bake and NextRound, and by the induction
     hypothesis for the remaining). *)
  move=> {} N' ps H2 IH1 _ l H3 H4 H5 IMP.
  have H6: N0 ⇓ N' by apply/(big_step_trans H3 H2).
  move: H5=> /=. rewrite delivery_preserves_time.
  move=> H7 b. move: (@honest_tree_preservation N N' Ready H2 H4 ps H7)=> -> //.
  move: IMP H6 ps=> {H2 H3 H7 H4} => H1 H2 H3 H4. move: H1.
  rewrite /has_state /=.
  move=> H1. 
  move: H4 H1=> /(in_honest_tree H2) [p' [l' [H4 [H5 [honesty_p' _] ] ] ] ] //=.
  rewrite single_party_rcv_step_state //=. rewrite /party_rcv_step_world.
  case eq: ((state_map N').[? _])=> //= [l''|]; last by rewrite eq.
  move: (honesty_p). rewrite honest_not_corrupt=> -> /=. rewrite fnd_set eq_refl.
  case. move<-. rewrite tree_delivery_extension. rewrite tbd_collect_msgs_eq. 
  by apply/(@at_ready_subset _ _ _ _ _ H2 honesty_p' honesty_p H3 H4 eq). 
Qed. 

(** *Preliminaries for CG **)

Definition lucky_slot_gen ps sl : bool :=
  has (fun p => Winner p sl && is_honest p) ps. 

Definition lucky_slot sl : bool :=
  lucky_slot_gen InitParties sl. 

Definition lucky_slot_w N :=
  lucky_slot_gen InitParties (t_now N). 

(** Node a subtlety here: The honest tree for round N is defined to be
    all chains that has been produced until round N. This is important
    as this is what we consider the best chain for now. **)
Definition honest_tree_chain N :=
  bestChain (t_now N - 1) (honest_tree N). 

Lemma leq_time_leq_chains {T : treeType} (t : T) sl sl' :
  sl <= sl' -> | bestChain sl t | <= |bestChain sl' t|. 
Proof. 
  move=> ?. apply/best_chain_best/subset_trans.
  - by apply/best_chain_valid. 
  - by apply/best_chain_in_all.
  - move=> ?.
    rewrite 2!mem_filter=> /andP [H1 ->]. rewrite andbC /=.
    by apply/leq_trans; [exact H1|].
Qed. 

Lemma subset_leq_chains {T T' : treeType} (t : T) (t' : T') sl :
  {subset allBlocks t <= allBlocks t'} ->
|bestChain sl t| <= |bestChain sl t'|.  
Proof.
  move=> H. apply/best_chain_best/subset_trans.
  - by apply/best_chain_valid. 
  - by apply/best_chain_in_all. 
  - by move=> ?; rewrite 2!mem_filter => /andP [-> /H ->]. 
Qed. 

Lemma subset_leq_time_leq_chains {T T' : treeType} (t : T) (t' : T') sl sl' :
  {subset allBlocks t <= allBlocks t'} -> sl <= sl' ->
|bestChain sl t| <= |bestChain sl' t'|.  
Proof. 
  move=> H H'. apply/best_chain_best/subset_trans.
  - by apply/best_chain_valid. 
  - by apply/best_chain_in_all. 
  - move=> ?.
    rewrite 2!mem_filter=> /andP [H'' /H ->]. rewrite andbC /=. 
    by apply/leq_trans; [exact H''|].
Qed. 

Lemma monotone_tree N N' p :
  N0 ⇓ N -> N ⇓ N' -> is_honest p -> forall l l',
  has_state p N l -> has_state p N' l' ->
  {subset allBlocks (tree l) <= allBlocks (tree l')}. 
Proof.
  move=> H + honesty_p.
  elim=> //= ; first by move=> ??; rewrite /has_state => -> [ ] ->.
  move=> N1 N2 [] //= {}N' progress_N H' IH l l'.
  - rewrite /has_state /= -/(has_state _ _ _).
    move: (big_step_trans H H')=> H''. 
    move=> state_p; move: (state_p)=> /IH =>{}IH.
    rewrite /has_state (single_party_rcv_step_state _ H'').
    rewrite -/(has_state _ _ _)=> state_p'.
    have: exists_state p (party_rcv_step_world p N').
    { by rewrite /exists_state state_p'. }
    rewrite exists_state_recieve /exists_state.
    case state_p'': (_.[?_])=> [l''|] //= _. 
    move: (delivery_blocktree honesty_p state_p'' state_p'). 
    move=> tree_diff. apply/subset_trans=> [|?]. 
    + by apply/(IH)/state_p''.
    + by rewrite tree_diff mem_cat => ->.
  - rewrite /has_state /=. move: (big_step_trans H H')=> H''. 
    rewrite (single_party_bake_step_state _ H'') -2!/(has_state _ _ _). 
    move=> state_p state_p'.
    move: (state_p')=> /has_exists_state /exists_bake_step_pres.
    rewrite/exists_state. case state_p'': (_.[?_])=> [l''|] //= _. 
    move: (honest_bake_send H'' honesty_p state_p'' state_p')=> [Y [tree_diff _] ].
    apply/subset_trans. apply/IH=> //. apply/state_p''. move=>?.
    by rewrite tree_diff mem_cat => ->.
Qed. 

Lemma monotone_honest_tree N N':
  N0 ⇓ N -> N ⇓ N' ->
  {subset allBlocks (honest_tree N) <= allBlocks (honest_tree N')}.
Proof. 
  
  move=> H' H b.
  move=> /(in_honest_tree H')=> [ [p] ] [l] [state_p [b_in [honesty_p p_in] ] ].
  rewrite /honest_tree all_build. rewrite inE. apply/orP; constructor 2. 
  apply/flattenP. rewrite /honest_parties.
  have: p \in exec_order N' by move: (perm_exec_order H)=> /perm_mem <-.
  elim: exec_order=> //= p' ps IH.
  rewrite inE=> /orP [/eqP <-|]; last first.
  - move=> /IH [bs ] H1 H2.
      by exists bs; case: is_honest=> //=; rewrite inE orbC H1.
  - rewrite honesty_p /= {1}/blocks.
    have: exists_state p N'.
    { by rewrite -(@exists_state_pres_big_step _ _ _ H) /exists_state state_p. }
    rewrite /exists_state. case state_p': (_.[?_])=> [l'|] //= _.
    exists (allBlocks (tree l')); first by rewrite mem_head.
    move=> {IH}. move: b b_in. apply/monotone_tree.
    + by apply/H'.
    + by apply/H.
    + by apply/honesty_p.
    all: done.
Qed.

Lemma monotone_growth_honest_chain N N':
  N0 ⇓ N -> N ⇓ N' -> |honest_tree_chain N| <= |honest_tree_chain N'|.
Proof.
  move=> ??. apply/subset_leq_time_leq_chains. 
  - by apply/monotone_honest_tree.
  - by apply/leq_sub2r/monotone_time.
Qed. 

Lemma perm_order_pres_honest_chain N ps sl :
  perm_eq (exec_order N) ps ->  
  |bestChain sl (honest_tree (N [[exec_order := ps]]))|
  = |bestChain sl (honest_tree N)|. 
Proof.
  move=> ?. 
  have H1:
    [seq b <- allBlocks (honest_tree (N [[exec_order := ps]])) | Blocks.sl b <= sl]
    =i [seq b <- allBlocks (honest_tree N) | Blocks.sl b <= sl]. 
  { move=> ?. rewrite /honest_tree 2!mem_filter 2!all_build. 
    case: (_ <= _)=> //=. apply/mem_eq_cons/perm_mem/perm_flatten => /=.  
    apply/perm_map/perm_filter. by rewrite perm_sym. }
  apply/anti_leq/andP; constructor. 
  all: apply/best_chain_best=> [|?];
  by [apply/best_chain_valid | move/best_chain_in_all; rewrite H1]. 
Qed. 

Lemma lt_0_time N : N0 ⇓ N -> 0 < t_now N.
Proof.
  elim=> //= ?? [] //=; clear; move=> ? _ _;
  by [rewrite delivery_preserves_time |rewrite baking_preserves_time].
Qed. 

Lemma extending_own_chain N l l' p :
  let sl := (t_now N) in 
  N0 ⇓ N -> Winner p sl -> is_honest p -> pk l = p ->
  has_state p N l -> has_state p (party_bake_step_world p N) l'  ->
  |bestChain (sl -1) (tree l)| < |bestChain sl (tree l')|. 
Proof.
  move=> sl H W honesty_p pk_l state_p.
  rewrite/party_bake_step_world state_p -honest_not_corrupt honesty_p.
  rewrite /honest_bake /=. rewrite pk_l W /=. 
  rewrite /has_state fnd_set eq_refl=> [] [] <- /=. 
  set nb := MkBlock _ _ _ _.
  set c := bestChain (sl - 1) _. 
  apply/(@ltn_leq_trans (| nb :: c |))=> //. 
  apply/best_chain_best.
  - rewrite/c /nb. move: (best_chain_valid (tree l) (sl - 1)).
    case bc : (bestChain _ _)=> [// |/= b {} c] . 
    rewrite valid_chain_ext /= W eq_refl /= andbC => -> /=.
    move: (@best_chain_in_all _ (sl - 1) (tree l)).
    move=> /(_ b). rewrite bc mem_head=> /trueI.
    rewrite mem_filter /sl => /andP [H' _]. apply/(leq_ltn_trans H')=> //=.
      by rewrite subn1 ltn_predL; apply/lt_0_time.
  - move=> b. rewrite inE=> /orP [/eqP ->|].
    + rewrite /nb. clear. case: l=> >.
        by rewrite mem_filter all_extend mem_cat orbC mem_head andbC /=.
    + move/best_chain_in_all.
      rewrite /nb. clear. case: l=> >.
      rewrite !mem_filter all_extend mem_cat => /andP [] H1 -> /=.
      rewrite andbC /=.
        by apply/(leq_trans H1)/leq_subr.
Qed.

Lemma pk_preserved N p : N0 ⇓ N -> forall l, has_state p N l -> pk l = p.
Proof.
  elim=> //=.
  - move=> l H.
    have H1: N0 ⇓ N0 by constructor. 
    move: (has_state_in_exec_order H1 H)=> /= H2. move: H2 H. 
    rewrite /has_state /N0 /=.
    elim: InitParties=> //= > IH. rewrite inE fnd_set.
    by case eq: (_ == _)/eqP=> [->|] //= _ [] <-. 
  - move=> > [] //=; clear; move=> N progress_N H IH l.
    + rewrite /has_state //= single_party_rcv_step_state //.
      rewrite /party_rcv_step_world.
      case state_p : ((state_map N).[?_])=> //=; last by rewrite state_p.
      case: (~~_)=> //=. 
      * rewrite fnd_set eq_refl. case=> <-. 
        elim: collect_zero_pairs=> //= ; first by apply/IH.
        move=> > /=. rewrite {2}/process_msg //=. 
        case: foldr => >. 
        by case: (msg _) => //=. 
      * case: AdversarialRcv=> //= > _.
        by rewrite broadcast_adv_msgs_preserves_state /= => /IH.  
    + rewrite /has_state /= single_party_bake_step_state //. 
      rewrite /party_bake_step_world.
      case state_p : ((state_map N).[?_])=> [l'|]//=; last by rewrite state_p.      
      case: (~~_)=> //=. 
      * rewrite/honest_bake /=.
        case: Winner=> >; 
        rewrite flood_msgs_preserves_state fnd_set eq_refl; case=> <- /=; 
           by move/IH: state_p; case: l'=> > ? /=. 
      * case: AdversarialBake=> //= > _.
        by rewrite broadcast_adv_msgs_preserves_state=> /IH.
Qed. 

Lemma bakes_preserves_pk ps p N:
  N0 ⇓ N -> forall l,
    has_state p (foldr party_bake_step_world N ps) l -> pk l = p.
Proof.
  move=> N0N. elim: ps=> [l /(pk_preserved N0N)|]//=. 
  move=> p' ps. set N' := foldr _ _ _. move=> IH l.
  rewrite /party_bake_step_world.
  case state_p': (_.[?_])=> [l'|] //=; last by move/IH.
  case: (~~_)=> //=.
  - rewrite /honest_bake /=.
    case: Winner=> //=; rewrite /has_state /= fnd_set; move: state_p';
    case: (_ == _)/eqP=> [<-|]//=; do ? try by (move/IH <-; case=> <- /=).
    all: do ? by move=> _ _ /IH.
  - case: AdversarialBake => >.
      by rewrite /has_state broadcast_adv_msgs_preserves_state /= => /IH.
Qed. 


(** *Chain Growth **)
Lemma chain_growth_lucky_slot_ready_baked  N_R N_B :
  N0 ⇓ N_R -> N_R ⇓[0] N_B ->
  N_R @ Ready -> N_B @ Baked -> 
  lucky_slot_w N_R ->
  |bestChain (t_now N_R - 1) (honest_tree N_R)| <
  |bestChain (t_now N_B) (honest_tree N_B)|. 
Proof.
  move=> H1 []. rewrite add0n.
  elim=> [_ -> //|] => N N' [] // {N N'} N_D; last first. 
  - move=> ??? IH ????. 
    rewrite perm_order_pres_honest_chain //.
    by apply/IH. 
  - rewrite baking_preserves_time => progress_N_D H2 _ sl_N_D progress_N_R _ /hasP.
    move=> [] p. move: (big_step_trans H1 H2) => H3 p_in. move: (p_in). 
    rewrite -(has_state_initP _ H3) /exists_state.
    case state_p: (_.[?_])=> [l|] // _ => /andP [] W honesty_p.
    have chain_leq: |bestChain (t_now N_R -1) (honest_tree N_R)|
    <= |bestChain (t_now N_R -1) (tree l)|. 
    { apply/subset_leq_chains/honest_tree_subset=> //.
      - exact honesty_p. 
      - exact progress_N_D.
      - constructor; by [|rewrite add0n].
      - exact state_p. } 
    apply/(leq_ltn_trans chain_leq). move: (p_in).
    rewrite -(has_state_initP _ H3).
    rewrite (exists_state_bakes _ (exec_order N_D) N_D) /exists_state.
    case state_p': (_.[?_])=> [l'|] // _. 
    move: (state_p'). rewrite single_party_bake_step_state // => state_p''.
    move: (pk_preserved H3 state_p)=> pk_l. 
    have chain_lt:
    |bestChain (t_now N_R -1) (tree l)| < |bestChain (t_now N_D ) (tree l')|.
    { move: W. rewrite sl_N_D => W.  
      apply/extending_own_chain ; by [exact W|]. }
    apply/(ltn_leq_trans chain_lt)/subset_leq_chains.
    move: state_p'. set N_B' := foldr _ _ _. move=> state_p' b b_in.
    rewrite /honest_tree all_build. rewrite inE. apply/orP. constructor 2. apply/flattenP.
    exists (allBlocks (tree l')); last done.
    apply/mapP. exists p.
    + rewrite /honest_parties mem_filter honesty_p /= bakes_preserves_order.
      by move: (perm_exec_order0 H3)=> /perm_mem <-.
    + by rewrite /blocks /= state_p'.
Qed. 

Lemma chain_growth_lucky_slot N_R N_R' :
  N0 ⇓ N_R -> N_R ⇓[1] N_R' ->
  N_R @ Ready -> N_R' @ Ready -> 
  lucky_slot_w N_R ->
  |honest_tree_chain N_R| < |honest_tree_chain N_R'|. 
Proof.
  move=> H1 [] + + progress_NR. elim=>//=.
  - by rewrite add1n=> + + _; elim: (t_now _)=> //= ?? []. 
  - move=> N1 N2 [] {N1 N2 N_R'} //= N'; last first. 
    + by move=> ??? IH ??? /=; rewrite !perm_order_pres_honest_chain //=; apply/IH. 
    + move=> progress_N' H2 _. rewrite add1n=> [ [] ]time _ luck.
      rewrite /honest_tree_chain /honest_tree /blocks /honest_parties /=.
      rewrite -2!/(honest_tree _) !subn1 /= -subn1.
      by apply/chain_growth_lucky_slot_ready_baked. 
Qed. 

(** nat_range a b = {a, a + 1, ... a + b - 1} , 
    i.e., the range excluding the last element. **)
Definition nat_range a b := iota a (b - a). 

Definition p_slots_range p a b :=
  [seq s <- nat_range a b | p s].

Definition lucky_slots_range a b :=
  p_slots_range lucky_slot a b.

Arguments lucky_slots_range _ _ /.

Definition lucky_slots_worlds N N' :=
  lucky_slots_range (t_now N) (t_now N').

Arguments lucky_slots_worlds _ _ /.

Lemma lucky_slots_NN0 N : |lucky_slots_worlds N N| = 0.
Proof.
  rewrite /= size_filter. apply/eqP.
  rewrite -leqn0. apply/leq_trans. 
  - by apply/count_size.
  - by rewrite size_iota subnn.
Qed. 

Definition unlucky_slot sl := ~~ lucky_slot sl. 

Definition first_lucky_slot N N' := ohead (lucky_slots_worlds N N'). 

Arguments first_lucky_slot _ _ /. 

Lemma some_lucky_slot N N' : N0 ⇓ N ->
  N ⇓ N' -> 1 <= |lucky_slots_worlds N N'| -> exists sl,
  first_lucky_slot N N' = Some sl. 
Proof. 
  rewrite /= /p_slots_range /nat_range => H.
  elim=> //=; first by rewrite lucky_slots_NN0.
  move=> ?? [] //=; move: H; clear; move=> H1 N' progress_N' H2 IH. 
  - by rewrite delivery_preserves_time=> /IH [] sl H'; (exists sl). 
  - by rewrite baking_preserves_time=> /IH [] sl H'; (exists sl). 
  - have Ht : ((t_now N').+1 - t_now N) = (t_now N' - t_now N) + 1. 
    { rewrite subSn.
      - by rewrite -add1n addnC. 
      - by apply/monotone_time/H2. } 
    rewrite Ht iota_add filter_cat size_cat /=.  
    set sl' := (t_now N + (t_now N' - t_now N)). 
    set NN' := |_|. case IHH: (0 < NN'); last first.
    + move: IHH. rewrite lt0n /(_ != _).
      case none: (_ == _)/eqP=> [h|]//= _. rewrite h add0n=> H. 
      exists sl'. move: none. rewrite size_eq0=> /eqP ->/=.  
      by move: H; case: (lucky_slot _) => //=. 
    + move: (IH IHH)=> [] sl H _.
        by exists sl; move: H; case: [seq _ <- _ | _ ] => //=. 
Qed.

Lemma first_lucky_slot_is_lucky N N' sl :
  first_lucky_slot N N' = Some sl -> lucky_slot sl. 
Proof.
  rewrite /= /p_slots_range. elim: (nat_range _ _) => //= s?.
  by case eq: (lucky_slot s)=> //= _ [] <-.
Qed. 

Lemma lucky_slot_in_between N N' sl:
  first_lucky_slot N N' = Some sl -> t_now N <= sl < t_now N'. 
Proof.
  rewrite /= /p_slots_range /nat_range=> H. 
  have: sl \in iota (t_now N) (t_now N' - t_now N). 
  { move: H. elim: (iota _ _)=> //= sl' sls IH.
    case: (lucky_slot _)=> //= [ [ ->] | /IH];
    by [rewrite mem_head |rewrite inE orbC=> ->]. }
  rewrite mem_iota=> /andP [] H1 H2. apply/andP. 
  constructor; try done. move: H2.  rewrite subnKC //= ltnW // -subn_gt0.
  by move: H; case: (_ - _)=> //. 
Qed. 

Lemma slot_in_between N N' sl :
  N @ Ready -> N ⇓ N' -> t_now N <= sl <= t_now N' ->
  exists N'', N'' @ Ready /\ t_now N'' = sl /\ N ⇓ N'' /\ N'' ⇓ N'. 
Proof. 
  move=> progress_N. elim=> //= [/anti_leq ?|]; first by (exists N; do ! constructor).
  move=> N1 N2 [] {N1 N2} N'' //= progress_N''.
  - move=> H IH. 
    rewrite delivery_preserves_time=> /IH [] N''' []?[]?[]??.
    exists N'''. do ! constructor; try done. 
      by econstructor; [constructor|]. 
  - move=> ? IH. 
    rewrite baking_preserves_time=> /IH [] N''' []?[]?[]??.
    exists N'''. do ! constructor; try done. 
      by econstructor; [constructor|]. 
  - rewrite /(_ [[_ := _]]). 
    set N''' := mkGlobalState _ _ _ _ _ _ _. 
    move=> H IH=> /andP [] le1. rewrite leq_eqVlt => /orP [/eqP ->|].
    + exists N'''. do ! constructor; try done. apply/(big_step_trans H).
        by econstructor; constructor. 
    + move=> /=. rewrite ltnS=> le2.
      move: (conj le1 le2) => /andP /IH [] N'''' []?[]?[]? H1.
      exists N''''. do ! constructor; try done. apply/(big_step_trans). apply/H1.
        by econstructor; constructor. 
  all: move=> ? ? IH => /IH [] N''' []?[]?[]??;
    exists N'''; do ! constructor; try done;
      by econstructor; [constructor|]. 
Qed.       

Lemma honest_tree_subset_ext_RR N N' p :
  N0 ⇓ N -> is_honest p -> N @ Ready -> N ⇓[1] N' ->
  N' @ Ready -> forall l', has_state p N' l' ->
  {subset allBlocks (honest_tree N) <= allBlocks (tree l')}.
Proof.
  move=> N0N honest_p prog_N []. elim=> //=.
  - by rewrite addnC addn1=> /esym/n_Sn. 
  - move=> N1 N2 [] // {N1 N2} N' prog_N' NN' _ [] t _ l' /=.
    rewrite /has_state /= -/(has_state _ _ _).
    move: NN' t prog_N' l'. elim=> //=; first by rewrite prog_N.
    move=> N1 N2 [] // {N1 N2} N' prog_N' NN' _.
    move: (big_step_trans N0N NN') => N0N'. 
    rewrite baking_preserves_time /has_state=> t _ l'.
    rewrite single_party_bake_step_state // => state'.
    move: (exists_state_bake p p N').
    rewrite /exists_state state'=> /exists_stateP /= [] l'' state''.
    apply/(@subset_trans _ _ (allBlocks (tree l''))); last first.
    + move=> ?.
      move: (honest_bake_send N0N' honest_p state'' state') => [] ? [] -> _.
        by rewrite mem_cat => ->.
    + apply/honest_tree_subset=> //.
      * exact honest_p.
      * exact prog_N'.
      * by constructor.
      * done. 
Qed. 

Lemma honest_tree_subset_ext N N' p l:
  N0 ⇓ N -> is_honest p -> N @ Ready -> 
  N ⇓^+ N' -> has_state p N' l ->
  {subset allBlocks (honest_tree N) <= allBlocks (tree l)}.
Proof.
  move=> N0N honest_p prog_N [] NN' t state'. 
  have tleqleq: t_now N <= t_now N + 1 <= t_now N'. 
  { apply/andP. constructor; by rewrite addn1. } 
  move: (slot_in_between prog_N NN' tleqleq) => [] N'' [] prog_N'' [] t' [] NN'' N''N'.
  move: (state') (exists_state_pres_big_step p N''N').
  move=> /has_exists_state -> /exists_stateP [] l'' state''.
  move: (big_step_trans N0N NN'') => N0N''. 
  move: (monotone_tree N0N'' N''N' honest_p state'' state') => sub. 
  apply/(subset_trans _ sub).
  apply/honest_tree_subset_ext_RR=> //.
  - exact honest_p.
  - constructor.
    + exact NN''.
    + by rewrite t' addnC. 
  - done.
  - done. 
Qed. 

Lemma nat_range_split a b c :
  a <= b <= c ->
  nat_range a c = nat_range a b ++ nat_range b c.
Proof. 
  rewrite /nat_range =>/andP [] H1 H2. 
  have: c - a = (b - a) + (c - b).
  { by rewrite addnBA // addnC addnBA // subnAC -addnBA // subnn addn0. }
  move->. rewrite iota_add.  
  suff: (a + (b - a)) = b by move->. 
  by rewrite addnC subnK. 
Qed. 

Lemma p_slots_range_split p a b c :
  a <= b <= c ->
  p_slots_range p a c = p_slots_range p a b ++ p_slots_range p b c. 
Proof. by move=> ?; rewrite -filter_cat -nat_range_split. Qed. 

Lemma world_in_between N N' w:
  N0 ⇓ N -> N ⇓ N' -> N @ Ready ->
  w + 1 <= | lucky_slots_worlds N N' | ->
  exists N'',
    N'' @ Ready
    /\ N0 ⇓ N''
    /\ N'' ⇓ N'
    /\ | honest_tree_chain N | + 1 <= | honest_tree_chain N'' |
    /\ w <= |lucky_slots_worlds N'' N'|.
Proof.
  move=> H1 H2 progress_N gew1. 
  have ge1: 1 <= | lucky_slots_worlds N N' |. 
  { by apply/(leq_trans _ gew1); rewrite addn1. }
  move: (some_lucky_slot H1 H2 ge1)=> [] sl ls. 
  move: (lucky_slot_in_between ls)=> /andP [] geN ltN'.
  move: (ltN')=> /leqW leN'. move: (conj geN leN')=> /andP beNN'. 
  move: (slot_in_between progress_N H2 beNN').
  move=> [] luckyN [] progress_lN [] t_lN [] H1' H2'.
  have A1: t_now luckyN <= sl.+1 <= t_now N'. 
  { by apply/andP; constructor; [rewrite t_lN|]. }
  move: (slot_in_between progress_lN H2' A1).
  move=> [] N'' [] progress_N'' [] t_N'' [] H1'' H2''.
  exists N''. do ! constructor; try done.
  - by apply/(big_step_trans H1)/(big_step_trans H1'). 
  - rewrite addn1. apply/leq_ltn_trans.
    + by apply/(monotone_growth_honest_chain H1 H1').
    + apply/chain_growth_lucky_slot=> //=. 
      * by apply/(big_step_trans H1). 
      * constructor; first done. by rewrite t_lN t_N'' add1n. 
      * apply/first_lucky_slot_is_lucky. rewrite t_lN. exact ls. 
  - move: gew1 => /=.
    rewrite (@p_slots_range_split _ (t_now N) (t_now N'') (t_now N')).
    + rewrite size_cat.
      have : | lucky_slots_range (t_now N) (t_now N'') | = 1.
      { move: (ls)=> /=.
        rewrite (@p_slots_range_split _ (t_now N) (t_now N'') (t_now N')). 
        + set a := p_slots_range _ _ _. set b := p_slots_range _ _ _.
          move=> some_cat. move: (some_cat). 
          rewrite -(@ohead_cat_some _ a b sl); last first.
          { move: some_cat. rewrite /a /= /p_slots_range /nat_range.
            have: sl \in iota (t_now N) (t_now N'' - t_now N).
            { rewrite mem_iota. apply/andP. constructor.
              - rewrite -t_lN. by apply/monotone_time.
              - rewrite subnKC.
                + by rewrite t_N''.
                + by apply/monotone_time/(big_step_trans H1'). }
            elim: (iota _ _) => //= sl' sls IH.
            rewrite inE=> /orP [/eqP <-|]. 
            - by move: ls => /first_lucky_slot_is_lucky ->.  
            - by case: (lucky_slot sl'). }
          rewrite /a /= /p_slots_range /nat_range.
          rewrite t_N'' subSn // -addn1 iota_add filter_cat size_cat.
          move=> /=. rewrite subnKC //. move: ls => /first_lucky_slot_is_lucky -> /=.
          rewrite addn1=> H. apply/eqP. rewrite eqSS. apply/eqP.
          have mem_i: all (fun sl' => sl' < sl)
                          [seq s <- iota (t_now N) (sl - t_now N) | lucky_slot s]. 
          { apply/allP=> sl'. rewrite mem_filter=> /andP [] _.
            rewrite mem_iota=> /andP [] _. by rewrite subnKC //. }
          move: mem_i H. elim: [seq _ <- _ | _] => //= sl' sls IH /andP [] H _ [] H'.
            by move: H' H => ->; rewrite ltnn. 
        + apply/andP; constructor.
          * by apply/monotone_time/(big_step_trans H1').
          * by apply/monotone_time. }
        by move->; rewrite addnC leq_add2l. 
    + apply/andP; constructor.
      * by apply/monotone_time/(big_step_trans H1').
      * by apply/monotone_time.
Qed. 

(** *Chain Growth ***)
Lemma chain_growth :
  forall w N N', 
  N0 ⇓ N -> N ⇓ N' -> N @ Ready ->
  w <= |lucky_slots_worlds N N'| -> 
  |honest_tree_chain N| + w <= |honest_tree_chain N'|. 
Proof.
  elim=> [|w IH] N N' H1 H2 progress_N.
  - by rewrite addn0=> _; apply/monotone_growth_honest_chain.
  - rewrite -addn1 => size_le.
    move: (world_in_between H1 H2 progress_N size_le).
    move=> [] N'' [] ? [] ? [] ? [] ??.
    apply/(@leq_trans (w + (|honest_tree_chain N''|))).
    + by rewrite addnC -addnA leq_add2l addnC. 
    + by rewrite addnC; apply/IH. 
Qed.

(** Chain growth phrased in terms of actual parties rather than the
    honest tree. **)
Lemma chain_growth_parties :
  forall w N N' p1 p2 l1 l2, 
    N0 ⇓ N -> N ⇓^+ N' -> N @ Ready ->
    is_honest p1 -> is_honest p2 ->
    has_state p1 N l1 -> has_state p2 N' l2 -> 
    w <= |lucky_slots_range (t_now N) (t_now N' - 1)| -> 
  |bestChain (t_now N - 1) (tree l1)| + w <= |bestChain (t_now N' - 1) (tree l2)|. 
Proof.
  move=> w N1 N3 p1 p2 l1 l2 H01 [] H13 ti1 prog_N1.
  move=> honest_p1 honest_p2 state_p1 state_p2 leqw.
  have in_between: t_now N1 <= t_now N3 -1 <= t_now N3. 
  { apply/andP. constructor; last first.
    - by rewrite subn1 leq_pred. 
    - rewrite subn1. move: ti1.
        by case: (t_now N3) =>//=. } 
  move:(slot_in_between prog_N1 H13 in_between)=> [] N2 [] prog_N2 [] ti2 [] H12 H23.
  move: leqw. rewrite -{1}ti2=> leqw. 
  apply/(@leq_trans (|honest_tree_chain N2|) _ _ ).
  - apply/(@leq_trans (|honest_tree_chain N1| + w) _ _ ).
    + rewrite leq_add2r /honest_tree_chain.
      by apply/subset_leq_chains/(subset_honest_tree _ honest_p1). 
    + by apply/chain_growth. 
  - rewrite /honest_tree_chain. apply/subset_leq_time_leq_chains; last first.  
    + by apply/leq_sub2r; rewrite ti2 subn1 leq_pred.
    + apply/honest_tree_subset_ext.
      * exact (big_step_trans H01 H12).
      * exact honest_p2. 
      * done.
      * constructor.
        -- exact H23. 
        -- rewrite ti2 subn1 ltn_predL.
             by apply/(@leq_ltn_trans (t_now N1)).
      * done. 
Qed.


