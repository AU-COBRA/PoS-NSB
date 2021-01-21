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
     CG.

Open Scope fmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Chain Quality
      This file contains the proof of chain quality. 
**)


(** Assumption is that a dishonest party can not forge the signature
    of a honest party. This is modelled as any dishonest party
    can only send out blocks that is a subset of all of the blocks
    communicated previously. *)

Inductive DeliverySteps : GlobalState -> GlobalState -> Prop :=
| RefineStepR : forall N1 N2, N1 ⇓ N2 -> DeliverySteps N1 N2
| ProgressR : forall N1 N2, 
    DeliverySteps (N1 [[progress := Delivered]]) N2 ->
    DeliverySteps N1 N2
| RcvStep : forall N1 N2 p, 
    DeliverySteps (party_rcv_step_world p N1) N2 ->
    DeliverySteps N1 N2.

Inductive BakingSteps : GlobalState -> GlobalState -> Prop :=
| RefineStepB : forall N1 N2, N1 ⇓ N2 -> BakingSteps N1 N2
| ProgressB : forall N1 N2, 
    BakingSteps (N1 [[progress := Baked]]) N2 ->
    BakingSteps N1 N2
| BakeStep : forall N1 N2 p, 
    BakingSteps (party_bake_step_world p N1) N2 ->
    BakingSteps N1 N2.
    
Lemma delivery_steps_refl N: DeliverySteps N N.
Proof. by do 2!constructor. Qed. 

Lemma baking_steps_refl N: BakingSteps N N.
Proof. by do 2!constructor. Qed. 

Definition baking_free N2 :=
  forall N1, BakingSteps N1 N2 ->  
        let nbs := [seq get_block (fst mp)
                   | mp <- fst (AdversarialBake
                                 (t_now N1)
                                 (history N1)
                                 (msg_buff N1)
                                 (adv_state N1))]
        in honest_subset nbs (block_history N1).

Arguments baking_free _ /. 

Definition delivery_free N2 :=
  forall N1, DeliverySteps N1 N2 -> forall p, 
       let '(msgs, N1') := fetch_msgs p N1 in
       let nbs := [seq get_block (fst mp)
                  | mp <- fst (AdversarialRcv
                                msgs
                                (t_now N1')
                                (history N1')
                                (msg_buff N1')
                                (adv_state N1'))]
       in honest_subset nbs (block_history N1'). 
Arguments delivery_free _ /. 

Lemma baking_free_prev: forall N1 N2, N1 ⇓ N2 -> baking_free N2 -> baking_free N1. 
  move=> N1 N2 N1N2 bfN2 /= N' H. apply/bfN2.
  move: H N1N2.
  elim=> N3 N4.
  - by move=> H1 H2; constructor; apply/(big_step_trans H1). 
  - by move=> H1 H2 /H2 /ProgressB.
  - by move=> p H1 H2 /H2 /BakeStep. 
Qed. 

Lemma delivery_free_prev: forall N1 N2, N1 ⇓ N2 -> delivery_free N2 -> delivery_free N1. 
  move=> N1 N2 N1N2 bfN2 /= N' H. apply/bfN2.
  move: H N1N2.
  elim=> N3 N4.
  - by move=> H1 H2; constructor; apply/(big_step_trans H1). 
  - by move=> H1 H2 /H2 /ProgressR.
  - by move=> p H1 H2 /H2 /RcvStep. 
Qed. 

Definition forging_free N := delivery_free N /\ baking_free N.
Arguments forging_free _ /. 

Lemma forging_free_prev: forall N1 N2, N1 ⇓ N2 -> forging_free N2 -> forging_free N1. 
  move=> N1 N2 N1N2 [] df bf. constructor.
  - by apply/(delivery_free_prev N1N2). 
  - by apply/(baking_free_prev N1N2). 
Qed. 

(** *Preliminaries for CQ *)

(** [s2] is a fragment of [s] if there exists [s1] and [s3] s.t. 
    [s1 ++ s2 ++ s3 = s]. **)
Definition fragment {T : Type} (s2 s : seq T) :=
  exists s1 s3, s1 ++ s2 ++ s3 = s. 

(** Adversarial slots: Slots where there are at least one adversarial
    winner. **)
Definition adv_slot_gen ps sl : bool :=
  has (fun p => Winner p sl && is_corrupt p) ps. 

Definition adv_slot sl : bool :=
  adv_slot_gen (enum [finType of Party]) sl. 

Definition adv_slot_w N :=
  adv_slot_gen InitParties (t_now N).

Definition adv_slots_range a b :=
  p_slots_range adv_slot a b.

Arguments adv_slots_range _ _ /.

Definition adv_slots_worlds N N' :=
  adv_slots_range (t_now N) (t_now N').

Arguments lucky_slots_worlds _ _ /.

Definition honest_advantage_range w a b :=
  |adv_slots_range a b| + w <= |lucky_slots_range a b|. 

Definition honest_advantage_ranges_gt w d :=
  forall a b, d <= b - a ->  honest_advantage_range w a b. 
 
Lemma N0N0 : N0 ⇓ N0. 
Proof. by constructor. Qed. 

Definition honest_block_hist N :=
  [seq b <- block_history N | honest_block b]. 

Arguments honest_block_hist _ /. 

Lemma no_premature_honest_blocks N :
  N0 ⇓ N ->
  forging_free N -> 
  all (fun b => sl b <= t_now N) (honest_block_hist N). 
Proof. 
  elim=> // N1 N2 [] // {N1 N2} N prog_N. 
  - set N2 := _[[_ := _]]. 
    move=> N0N + H. apply: instant1.
    { apply: (forging_free_prev _ H). 
        by do 2! econstructor. }
    move=> IH.
    move: (delivery_steps_refl N2).
    rewrite {1 4}/N2. 
    rewrite delivery_preserves_time.
    move/ProgressR. 
    elim: exec_order=> //= p ps.
    set N' := foldr _ _ _.
    move=> + /RcvStep fs.
    apply: instant1; first by apply/(fs). 
    move=> IH'. 
    rewrite {1}/party_rcv_step_world.
    case state_p: (_.[?_])=> [l|] //=.
    case honest_p: (~~_)=> //=.
    case: H=> /(_ _ fs p) /= + _. 
    case: AdversarialRcv=> //= nbs _.
    elim: nbs => //= [ [ [ ] ] ] b ? nbs //=.
      rewrite /honest_subset /=. 
      case honest_b: (is_honest _) => //= IH'' sub.
      rewrite IH''.
      * rewrite andbC /=. move/allP: IH' -> => //=. apply/sub.
          by rewrite mem_head.
      * by apply/(subset_trans _ sub)/subset_cons. 
  - set N2 := _[[_ := _]]. 
    move=> N0N + H. apply: instant1. 
    { apply: (forging_free_prev _ H). 
        by do 2! econstructor. }
    move=> IH.
    move: (baking_steps_refl N2).
    rewrite {1 4}/N2. 
    rewrite baking_preserves_time.
    move/ProgressB. 
    elim: exec_order=> //= p ps.
    set N' := foldr _ _ _.
    move=> + /BakeStep fs.
    apply: instant1; first by apply/(fs). 
    move=> IH'. 
    rewrite {1}/party_bake_step_world.
    case state_p: (_.[?_])=> [l|] //=.
    case honest_p: (~~_)=> //=. 
    + rewrite /honest_bake //=. case: Winner => //=. 
      case : is_honest => //=.
      by rewrite IH' andbC /= /N' baking_preserves_time.  
    + case: H=> _/=  /(_ _ fs). 
      case: AdversarialBake=> //= nbs _. 
      elim: nbs => //= [ [ [ ] ] ] b ? nbs //=.
      rewrite /honest_subset /=. 
      case honest_b: (is_honest _) => //= IH'' sub.
      rewrite IH''.
      * rewrite andbC /=. move/allP: IH' -> => //=. apply/sub.
          by rewrite mem_head.
      * by apply/(subset_trans _ sub)/subset_cons. 
  - move=> N0N + H. apply: instant1. 
    { apply: (forging_free_prev _ H). 
        by do 2! econstructor. }
    move=> /=. 
    elim: [seq _ <- _ | _] => //= b bs IH /andP [] H' /IH ->.
    by rewrite andbC /=; apply/(leq_trans H')/leq_pred. 
  - move=> perm N0N IH H. apply/IH/(forging_free_prev _ H).
      by do 2!econstructor.
  - move=> perm N0N IH H. apply/IH/(forging_free_prev _ H).
      by do 2!econstructor. 
Qed. 

Lemma no_premature_honest_blocks_R N :
  N0 ⇓ N -> forging_free N -> N @ Ready -> all (fun b => sl b < t_now N) (honest_block_hist N). 
Proof.
  elim=> // {} N N' [] {N'} N //.
  - move=> prog_N N0N _ ff _. 
    move: (no_premature_honest_blocks N0N).
    apply: instant1. 
    { apply: (forging_free_prev _ ff). 
        by do 2! econstructor. }
  rewrite /= /honest_block_hist /block_history.
  by elim: [seq _ <- _ | _ ].
  - move=> ? perm N0N IH H progN /=. apply/IH=> //.
    + apply/(forging_free_prev _ H).
      by do 2!econstructor.
  - move=> ? perm N0N IH H progN /=. apply/IH=> //.
    + apply/(forging_free_prev _ H).
      by do 2!econstructor.
Qed. 

Lemma no_premature_honest_blocks_D N :
  N0 ⇓ N -> forging_free N -> N @ Delivered -> all (fun b => sl b < t_now N) (honest_block_hist N). 
Proof.
  elim=> // {} N N' [] {N'} N //.
  - move=> prog_N N0N _ ff _. 
    move/(_ _ prog_N): (no_premature_honest_blocks_R N0N). 
    apply: instant1. 
    { apply: (forging_free_prev _ ff). 
        by do 2! econstructor. }
    move=> H. 
    rewrite delivery_preserves_time.
    set N2 := _[[_ := _]].
    move: (delivery_steps_refl N2). 
    rewrite {1 3}/N2=> /ProgressR. 
    elim: exec_order => //= p ps IH /RcvStep H'.
    move: (IH H') => {} IH. 
    rewrite {1}/party_rcv_step_world.
    case state_p: (_.[?_])=> [l|] //=.
    case honest_p: (~~_)=> //=.
    case: ff=> /(_ _ H' p) /= + _ .
    case: AdversarialRcv=> //= nbs _.
    elim: nbs => //= [ [ [ ] ] ] b ? nbs //=.
    rewrite /honest_subset /=.
    case honest_b: (is_honest _) => //= IH'' sub.
    rewrite IH''.
    * rewrite andbC /=. move/allP: IH -> => //=. apply/sub.
        by rewrite mem_head.
    * by apply/(subset_trans _ sub)/subset_cons.
  - move=> ? perm N0N IH H progN /=. apply/IH=> //.
    + apply/(forging_free_prev _ H).
      by do 2!econstructor.
  - move=> ? perm N0N IH H progN /=. apply/IH=> //.
    + apply/(forging_free_prev _ H).
      by do 2!econstructor.
Qed.

Lemma delivery_preserves_honest_block_hist N :
  N0 ⇓ N ->
  forging_free (foldr party_rcv_step_world N (exec_order N) [[progress := Delivered]]) ->
  N @  Ready -> 
  honest_block_hist N
  =i honest_block_hist (foldr party_rcv_step_world N (exec_order N)). 
Proof.
  move=> N0N. set N2 := _[[_ := _]]. move=> ff prog_N.
  move/ProgressR: (delivery_steps_refl N2). 
  elim: exec_order => //= p ps IH {} /RcvStep H.
  move: (IH H)=> {}IH. 
  rewrite {1}/party_rcv_step_world.
  case state_p: (_.[?_])=> [l|] //=. case honest_p: (~~_)=> //=.
  case: ff=> /(_ _ H p) /= + _. 
  case: AdversarialRcv=> //= nbs _.
  rewrite IH. elim: nbs => //= [ [ [ ] ] ] b ? nbs //=.
  rewrite /honest_subset /=. 
  case honest_b: (is_honest _) => //= IH'' sub.
  move: (sub)=> /(_ b). rewrite mem_head=> /trueI sub'. 
  move=>b'. rewrite inE. 
  case: (_ == _)/eqP=>[->|] //= _. move: b'. rewrite -/(_ =i _). 
  rewrite IH'' //. 
  by apply/(subset_trans _ sub)/subset_cons.     
Qed. 

Lemma honest_blocks_below_slot_preserved N N' :
  N0 ⇓ N -> N ⇓ N' -> forging_free N' -> 
  [seq b <- honest_block_hist N | sl b < t_now N]
  =i [seq b <- honest_block_hist N' | sl b < t_now N]. 
Proof.
  move=> N0N. elim=> // N1 N2 [] // {N1 N2} N'.
  - move => prog_N' NN' H ff. 
    rewrite H; last first.
    { apply: (forging_free_prev _ ff). 
        by do 2! econstructor. }
    apply/filter_mem_eq/delivery_preserves_honest_block_hist=> //.
      by apply/(big_step_trans N0N). 
  - move=> prog_N' NN' + ff. 
    apply: instant1=> [|IH].
    { apply: (forging_free_prev _ ff). 
        by do 2! econstructor. }
    move: (big_step_trans N0N NN') => N0N'.
    set N2 := _[[ _:= _]]. 
    move/(ProgressB): (baking_steps_refl N2). 
    rewrite {2}/N2. 
    elim: exec_order=> //= p ps.
    set N'' := foldr _ _ _.
    rewrite -/(honest_block) -!/(honest_block_hist _ ). 
    move=> IH' /BakeStep H.
    move: (IH' H)=> ->. 
    rewrite {1}/party_bake_step_world.
    case state_p: (_.[?_])=> [l|] //=.
    case honest_p: (~~_)=> //=. 
    + rewrite /honest_bake //=. case: Winner => //=. 
      case : is_honest => //=.
      by rewrite baking_preserves_time ltnNge monotone_time //. 
    + case: ff => _ /(_ _ H) /=. 
      rewrite /N'' -/N''.
      case: AdversarialBake=> //= nbs _. 
      elim: nbs => //= [ [ [ ] ] ] b ? nbs //=.
      rewrite /honest_subset /=. 
      case honest_b: (is_honest _) => //= IH'' sub.
      case b_lt: (_ < _)=> //=; last first. 
      * by rewrite IH'' //; apply/(subset_trans _ sub)/subset_cons. 
      * move=> b'. rewrite inE.
        case: (_ == _)/eqP=>[->|] //=.
        -- by rewrite mem_filter b_lt /=; apply/sub; rewrite mem_head. 
        -- by rewrite IH'' //; apply/(subset_trans _ sub)/subset_cons. 
  - move=> progN NN' + ff. move->=> //. 
    apply: (forging_free_prev _ ff).
      by do 2! econstructor.
  - move=> ? perm NN' IH H progN /=. apply/IH=> //.
    + apply/(forging_free_prev _ H).
      by do 2!econstructor.
  - move=> ? perm NN' IH H progN /=. apply/IH=> //.
    + apply/(forging_free_prev _ H).
      by do 2!econstructor.
Qed. 

Lemma history_monotone_delivery N p :
  {subset history N <= history (party_rcv_step_world p N )}.
Proof.
  rewrite /party_rcv_step_world. case: (_.[? _]) => //= l.
  case: (~~_)=> //=. case: AdversarialRcv=> //= + _.
  elim=> //= [] [] ??? /subset_trans IH. apply/IH => {IH}.
  by apply/subset_cons. 
Qed. 

Lemma history_monotone_deliverys N ps :
  {subset history N <= history (foldr party_rcv_step_world N ps)}.
Proof.
  by elim: ps => //= p ps /subset_trans IH; apply/IH/history_monotone_delivery.  
Qed. 

Lemma history_monotone_bake N p :
  {subset history N <= history (party_bake_step_world p N)}.
Proof.
  rewrite /party_bake_step_world.
  case: (_.[? _]) => //= l. case: (~~_)=> //=.
  - case: honest_bake=> //= + ?. elim=> //= ?? /subset_trans IH.
      by apply/IH/subset_cons.  
  - case: AdversarialBake=> //= + _.
  elim=> //= [] [] ??? /subset_trans IH. apply/IH => {IH}.
  by apply/subset_cons. 
Qed. 

Lemma history_monotone_bakes N ps:
  {subset history N <= history (foldr party_bake_step_world N ps)}.
Proof. 
  elim: ps => //= p ps.
  set N' := foldr _ _ _. move=> /subset_trans IH.
    by apply/IH/history_monotone_bake.  
Qed. 

Lemma history_monotone N N' :
  N ⇓ N' ->  {subset history N <= history N'}. 
Proof.
  elim=> // {} N1 N2 [] {N1 N2} N' //= prog_N NN' IH.
  - by apply/(subset_trans IH)/history_monotone_deliverys. 
  - by apply/(subset_trans IH)/history_monotone_bakes. 
Qed. 

Lemma block_history_monotone N N' :
  N ⇓ N' -> {subset block_history N <= block_history N'}.
Proof. by move=> /history_monotone H; apply/map_subset. Qed. 

Lemma buff_history_subset N :
  N0 ⇓ N ->
  {subset [seq msg mt | mt <- msg_buff N]  <= history N}. 
Proof. 
  elim=> //= {} N N' [] //= {N'} N.
  (* Delivery step  *)
  - move=> prog_N N0N IH. elim: exec_order=> //= p ps.
    set N' := foldr _ _ _. move=> {} IH.
    rewrite /party_rcv_step_world. 
    case: (_.[? _]) => //= l. case: (~~_)=> //=.
    + by apply/(subset_trans _ IH)/map_subset/filter_subset. 
    + case: AdversarialRcv=> //= + _.
      elim=> //= [|[] [] m ??].
      * by apply/(subset_trans _ IH)/map_subset/filter_subset.
      * set N'' := flood_msgs_adv _ _.
        rewrite /flood_msg_adv /= map_cat => IH' m'.
        rewrite mem_cat=> /orP [].
        -- move=>/mapP [] ? /mapP [] ? _ -> ->.
           by rewrite mem_head. 
        -- by rewrite inE orbC => /IH' ->. 
  (* Bake step *)
  - move=> prog_N N0N IH. elim: exec_order=> //= p ps.
    set N' := foldr _ _ _. move=> {} IH.
    rewrite /party_bake_step_world. 
    case: (_.[? _]) => //= l. case: (~~_)=> //=.
    + case: honest_bake => //= + ?.
      elim=> //= m ms. set N'' := flood_msgs _ _.
      rewrite map_cat=> IH' ?. rewrite mem_cat=> /orP [].
      * move=>/mapP [] ? /mapP [] ? _ -> ->.
          by rewrite mem_head. 
      * by rewrite inE orbC => /IH' ->. 
    + case: AdversarialBake=> //= + _.
      elim=> //= [] [] m ??.
      * set N'' := flood_msgs_adv _ _.
        rewrite /flood_msg_adv /= map_cat => IH' m'.
        rewrite mem_cat=> /orP [].
        -- move=>/mapP [] ? /mapP [] ? _ -> ->.
           by rewrite mem_head. 
        -- by rewrite inE orbC => /IH' ->. 
  (* Increment step *)
  - move=> prog_N N0N IH. apply/(subset_trans _ IH); clear.
    elim: msg_buff=> //= m ms IH m'. rewrite 2!inE.
    by case: (_ ==_)=> //= /IH . 
  - move=> ? /perm_mem H _ IH.
    by apply/(subset_trans _ IH)/map_subset=> m; rewrite H. 
Qed.     

Lemma all_tree0_not_gb {tT :treeType} : [seq b <- allBlocks (@tree0 tT) | b != GenesisBlock] = [::]. 
Proof.
  move: (all_tree0 tT) =>H.
  have: forall b, b \in allBlocks (@tree0 tT) -> b = GenesisBlock.
  by move=> >; rewrite H inE=> /eqP. 
  move=> {H}. 
  elim: allBlocks => //= b bs IH H. 
  rewrite (H b).
  - rewrite eq_refl /=. apply/IH=> > ?. apply/H.
    by rewrite inE; case: (_ ==_). 
  - by rewrite inE eq_refl. 
Qed. 

Lemma not_gb_honest_tree_history_subset N :
  N0 ⇓ N ->
  {subset [seq b <- allBlocks (honest_tree N) | predC1 GenesisBlock b] <=
   block_history N}. 
Proof. 
  elim=> //=.
  - move=> b. rewrite mem_filter in_nil andbC.
    case eq: (_ \in _)=>//=. move/(init_ht_gb): eq ->.
    by rewrite eq_refl. 
  - move=> {} N N' [] // {N'} N.
    (* Delivery *)
    + move=> prog_N N0N IH.
      move: (@history_monotone_deliverys N (exec_order N))=> /(@map_subset _ _ _ _ get_block). 
      rewrite -2!/(block_history _)=> H. 
      apply/(subset_trans _ H)=> {H} b. rewrite mem_filter=> /andP [] b_not_gb. 
      move/(in_honest_tree).
      apply: instant1; first by apply/(big_step_trans N0N); do 2! econstructor. 
      move=> [] p [] l.
      rewrite /has_state single_party_rcv_step_state //. 
      move=> [] state_p [] b_in_l [] honest_p p_in. 
      move: state_p. rewrite /party_rcv_step_world.
      case state_pN : ((state_map N).[?_])=> [l' |]//=; last by rewrite state_pN. 
      move: (honest_p). rewrite honest_not_corrupt=> ->. 
      rewrite fnd_set eq_refl. case=> H. move: b_in_l. 
      rewrite -H => {H}. set nms := [seq _ | _ <- _].
      have: {subset nms <= history N}.
      { rewrite /nms /collect_zero_pairs.
        apply/(subset_trans _ (buff_history_subset N0N)).
          by apply/map_subset/filter_subset. }
      elim: nms=> //= [_| m ms].
      * move=>/(subset_honest_tree N0N honest_p state_pN)=> H. apply/IH.
          by rewrite mem_filter b_not_gb H.
      * move=> {} IH.  rewrite {1}/process_msg /=. case: m=> //= b' /=.
        move: IH. case: foldr=> > IH. 
        rewrite all_extend mem_cat => sub /orP [] H.
        -- by apply/(IH _ H)/(subset_trans _ sub)/subset_cons. 
        -- apply/mapP. exists (BlockMsg b').
           ++ by apply/sub; rewrite mem_head.
           ++ by move: H; rewrite inE=> /eqP ->. 
    (* Bake *)
    + move=> prog_N N0N IH.
      elim: exec_order=> //= p ps.  
      rewrite /honest_tree /honest_parties /blocks /=.
      set N' := foldr _ _ _.
      move=> {} IH. rewrite bake_preserves_order.
      rewrite /party_bake_step_world.
      case state_p: (_.[?_]) => [l |] //=. 
      case honest_p: (~~_)=> //=; last first.
      * case: AdversarialBake=> //= ms _. 
        rewrite broadcast_adv_msgs_preserves_state. 
        apply/(subset_trans IH). apply/map_subset.
        elim: ms=> //= [] [] ??? /subset_trans {} IH. apply/IH => {IH}.
          by apply/subset_cons. 
      * rewrite /honest_bake /=. 
        case: Winner => //=; last first.
        -- apply/(subset_trans _ IH). move=> b. rewrite 2!mem_filter=> /andP [] -> /=. 
           elim: exec_order=> //= p' ps' {} IH.
           case: is_honest=> //=. rewrite fnd_set. 
           rewrite !allBlocks_build_cat 2!mem_cat => /orP [| /IH ->]; [|by rewrite orbC].
           by case: (_ == _)/eqP => [ -> | _ ->] //=; rewrite state_p=> ->. 
        -- set nb:= MkBlock _ _ _. (* set l' := @mkLocalState _ _ _.  *)
           move: IH. elim: exec_order=> //= [| p' ps'].
           ++ by rewrite all_tree0_not_gb=> _. 
           ++ case: is_honest=> //=. set rest := flatten _.  set rest' := flatten _.  
              rewrite !fnd_set. move=> IH H b. 
              case pp': (_ == _)/eqP=> [pp''|]; last first. 
              ** rewrite mem_filter=> /andP [] H1.
                 rewrite allBlocks_build_cat.  
                 rewrite mem_cat=> /orP [].
                 --- rewrite inE=> H2. apply/orP. constructor 2. apply/H.
                       by rewrite mem_filter H1 /= allBlocks_build_cat mem_cat H2. 
                 --- move=> H2. apply/IH; last by rewrite mem_filter H1 H2. 
                     apply/(subset_trans _ H)=> {H1 H2} b.
                     rewrite 2!mem_filter=> /andP [] -> /=.
                       by rewrite allBlocks_build_cat mem_cat orbC => ->.
              ** rewrite mem_filter=> /andP [] H1. case: l state_p nb rest' IH => > state_p nb rest' IH. 
                 rewrite allBlocks_build_cat mem_cat=> //= /orP []. 
                 --- rewrite all_build. move: (H1). rewrite inE.
                     case: (_==_) => //= _. 
                     rewrite all_extend inE mem_cat orbC.
                     move=>/orP [|]; first by rewrite inE=> ->.
                     move=> H2. apply/orP. constructor 2. apply/H. 
                     rewrite pp'' state_p mem_filter H1 /= allBlocks_build_cat mem_cat.
                     by rewrite all_build inE orbC H2 orbA orbC.
                 --- move=> H2. apply/IH; last by rewrite mem_filter H1 H2. 
                     apply/(subset_trans _ H)=> {H1 H2} b.
                     rewrite 2!mem_filter=> /andP [] -> /=.
                       by rewrite allBlocks_build_cat mem_cat orbC => ->.
    + move=> ps H _ IH. apply/(subset_trans _ IH)=> {IH} //=.
      apply/subset_mem_eqW/filter_mem_eq. 
      rewrite !all_build.
      apply/mem_eq_cons/perm_mem/perm_flatten/perm_map/perm_filter => /=.
      by rewrite perm_sym.
Qed.

Lemma honest_tree_gb_history_subset N :
  N0 ⇓ N ->
  {subset allBlocks (honest_tree N) <= GenesisBlock :: block_history N}. 
Proof. 
  move/not_gb_honest_tree_history_subset=> + b bin.
  move/(_ b). rewrite mem_filter /= inE bin andbC.
  by case: (_==_)=> //= /trueI. 
Qed.   

Lemma honest_block_honest_party N :
  N0 ⇓ N -> forging_free N -> forall b, b \in honest_block_hist N -> bid b \in exec_order N. 
Proof. 
  elim => // {} N N' [] // {N'} N.
  - move=> prog_N N0N + ff b.
    apply: instant1=> [|IH].
    { apply: (forging_free_prev _ ff). 
        by do 2! econstructor. }
    rewrite -(delivery_preserves_honest_block_hist N0N ff prog_N)=> /IH.
      by rewrite rcvs_preserves_order. 
  - move=> prog_N N0N + ff b.
    apply: instant1=> [|IH].
    { apply: (forging_free_prev _ ff). 
        by do 2! econstructor. }
    rewrite bakes_preserves_order=> H.
    move/perm_mem: (perm_exec_order0 N0N) <-.
    rewrite -(has_state_initP _ N0N).
    move: ff. set N2 := _[[_ := _]]. move=> ff. 
    move/ProgressB: (baking_steps_refl N2).
    elim: exec_order H=> [/IH // | /= p ps].
    + move/perm_mem: (perm_exec_order0 N0N) <-.
        by rewrite -(has_state_initP _ N0N).
    + set N' := foldr _ _ _. move=> {} IH + /BakeStep bs.
      move/(_ _ bs): IH => {}IH. 
      rewrite /party_bake_step_world.
      case state_p: (_.[?_])=> [l|]//=.
      case honest_p: (~~_)=> //=.
      * rewrite /honest_bake //=. case: Winner => //=. 
        set nb := MkBlock _ _ _ _. 
        rewrite (@bakes_preserves_pk _ p N N0N l state_p). 
        rewrite honest_not_corrupt honest_p inE => /orP [/eqP -> /=|].
        -- rewrite (@bakes_preserves_pk _ p N N0N l state_p).
           by move/has_exists_state: state_p; rewrite -exists_state_bakes. 
        -- by move/IH. 
      * case: ff=> _ /(_ _ bs) /=. 
        rewrite -/N'. 
        case: AdversarialBake=> ms ?.
        elim: ms => //= [ [] ] m dm ms //= IH'.
        case: is_honest=> //= H.
        rewrite inE=> /orP [/eqP H' |].
        -- apply/IH. move: H' ->. apply/H.
             by rewrite mem_head.
        -- apply/IH'. rewrite /honest_subset.
           by apply/(subset_trans _ H)/subset_cons.
  - move=> progN N0N IH ff /= b. apply/IH/(forging_free_prev _ ff). 
      by do 2! econstructor. 
  - move=> ? p N0N IH ff b ? /=. move/perm_mem: (p) <- . apply/IH=> //. 
    apply/(forging_free_prev _ ff). by do 2!econstructor. 
  - move=> ? p N0N IH ff b ? /=. apply/IH=> //. 
    apply/(forging_free_prev _ ff). by do 2!econstructor. 
Qed. 

Definition block_hist_gb N := GenesisBlock :: block_history N. 

Arguments block_hist_gb _ /. 

Definition collision_free N := {in block_hist_gb N &, injective HashB}.
Arguments collision_free _ /. 

Lemma eq_head_eq_chains N c c' b :
  N0 ⇓ N ->
  collision_free N ->
  (valid_chain (b :: c)) ->
  (valid_chain (b :: c')) ->
  {subset c <= block_hist_gb N} ->
  {subset c' <= block_hist_gb N} ->
  c = c'. 
Proof. 
  move=> N0N no_coll. move: b c'. elim: c => //=.
  - move=> b' [] // b'' bs /valid_chain_block_gb ->.
    move=> /andP [] _ /andP [] _ /(order_path_min lt_slots_trans).
    by rewrite /lt_slots GenesisSlot=> /andP []. 
  - move=> b bs IH h [].
    + move=> + H; move/valid_chain_block_gb : H ->.
      move=> /andP [] _ /andP [] _ /(order_path_min lt_slots_trans).
        by rewrite /lt_slots GenesisSlot=> /andP []. 
    + move => b' bs'.
      rewrite 2!valid_chain_ext /linked.
      move=> /andP [] _ /andP [] /eqP -> /andP [] _ vbbs.
      move=> /andP [] _ /andP [] /eqP hbhb' /andP [] _ vb'bs' s1 s2.
      have bb': b = b'. 
      { move: hbhb' => /no_coll -> //. 
        - by apply/s1; rewrite mem_head. 
        - by apply/s2; rewrite mem_head. }
      rewrite bb' (@IH b bs') //. 
      * by rewrite bb'. 
      * by apply/(subset_trans _ s1)/subset_cons. 
      * by apply/(subset_trans _ s2)/subset_cons .
Qed. 

Lemma honest_tree_hist_gb_subset N :
  N0 ⇓ N ->
  {subset allBlocks (honest_tree N) <= block_hist_gb N}. 
Proof.
  move=> N0N b. move: (@not_gb_honest_tree_history_subset _ N0N b).
  rewrite mem_filter /=.
  case: (_==_)/eqP=> [-> _| _ H /H]//=; first by rewrite mem_head.
  by rewrite inE orbC => ->. 
Qed. 
  
Lemma block_hist_gb_montone N N' :
  N ⇓ N' ->
  {subset block_hist_gb N <= block_hist_gb N'}. 
Proof. 
  move=> /block_history_monotone H b /=. rewrite 2!inE.
  by case: (_==_)=> //= /H. 
Qed. 

Lemma bc_ext_max_increase {tT : treeType} (tree : tT) t b:
  sl b = t -> 
  | bestChain t (extendTree tree b) | <= | bestChain (t - 1) tree |.+1.
Proof.
  rewrite subn1=> slb. 
  move /valid_chain_cons: (best_chain_valid (extendTree tree b) t) => [] b' [].
  move=> [<- //=| b'' bs H]. rewrite -H.
  suff: |(b'' :: bs)| <= (| bestChain t.-1 tree |) by done. 
  apply/best_chain_best. 
  - move: (best_chain_valid (extendTree tree b) t).
    by rewrite -H valid_chain_ext=> /andP [] _ /andP [] _ /andP [] _.    
  - move=> b'''. 
    rewrite mem_filter.
    move: (best_chain_valid (extendTree tree b) t).
    rewrite -H => /andP [] H1 /andP [] H2 /(order_path_min lt_slots_trans).
    move/allP=> H' memb'''. move/H': (memb''').  rewrite /lt_slots. 
    have slb'ltt: sl b' <= t. 
    { move: (@best_chain_in_all _ t (extendTree tree b)). rewrite -H=> /(_ b').
      by rewrite mem_filter mem_head=> /trueI /andP []. }
    move=> b'''ltb'. apply/andP. constructor.
    - rewrite -ltnS (@ltn_predK (sl b''')); by apply/(ltn_leq_trans b'''ltb'). 
    - move: (@best_chain_in_all _ t (extendTree tree b)). rewrite -H=> /(_ b'''). 
      rewrite inE orbC memb''' /= => /trueI.
      rewrite mem_filter all_extend mem_cat inE=> /andP [] _.
      case: (_\in _) => //= /eqP beq. rewrite -(ltnn t).
      apply/(ltn_leq_trans _ slb'ltt). 
      by rewrite -slb -beq. 
Qed. 

Lemma honest_block_state N p l bsH b bsT :
  N0 ⇓ N ->
  forging_free N -> 
  collision_free N ->
  is_honest p ->
  has_state p N l ->
  honest_block b ->
  bsH ++ (b :: bsT) =  bestChain (t_now N-1) (tree l) ->
  exists N' p',
    N0 ⇓ N'
    /\ N' ⇓ N
    /\ t_now N' = sl b + 1
    /\ N' @ Ready
    /\ is_honest p'
    /\ exists l', has_state p' N' l'
    /\ |(bestChain (t_now N' -1) (tree l'))| = |b :: bsT|.
(** Note that the theorem is stated with equality as it is important
    that the best chain is not longer either.  **)
Proof.
  (** We start out noting a couple of usefull facts**)
  move=> N0N ff no_coll honest_p state_pN honest_b /esym bc_layout.
  have: exists s' s'' , bestChain (t_now N-1) (tree l) = s' ++ (b :: s''). 
  { by exists bsH; exists bsT. }
  move/inP => mem_bc.
  have bbsT_valid : valid_chain (b :: bsT).
  { move: (best_chain_valid (tree l) (t_now N -1)). 
    by rewrite bc_layout=> /valid_chain_short_l. }
  (** Case split if b is the GenesisBlock**)
  case eq_gb: (b == GenesisBlock).
  (** If the block is the GenesisBlock.**)
  - exists N0. move/has_exists_state: state_pN. rewrite has_state_initP //. 
    rewrite -(@has_state_initP N0); last by constructor.
    move/exists_stateP => [] l' state_pN0. 
    exists p.  do ! constructor; try done.
    + by move/eqP : eq_gb=> ->; rewrite GenesisSlot addn1. 
    + exists l'. move: bc_layout; move/tree_gb_init: (state_pN0) ->. 
      do ! constructor; try done.
      rewrite best_chain_tree_gb. 
      suff: bsT = [::] by move->. 
      move: (best_chain_valid (tree l) (t_now N -1)). 
      rewrite bc_layout=> /valid_chain_short_l. move/eqP: eq_gb ->.
      clear. move=> /andP [] _ /andP [] _ /=.  
      move/(order_path_min lt_slots_trans)=> //=.
      rewrite /lt_slots GenesisSlot. 
        by elim: bsT=> //=. 
  (** If the block is different from GB it must have been mined by
      sonme honest party, and we know that the first time this can
      happen is in round [t_now N0]. **)
  have le_sl_lt: t_now N0 <= sl b <= (t_now N -1 ). 
  { apply/andP. constructor.
    - move=> /=. move: mem_bc (best_chain_valid (tree l) (t_now N -1)). 
      move: (best_chain_starts_gb (tree l) (t_now N -1))=> [] bc <-.
      rewrite mem_cat inE eq_gb orbC /=. elim: bc=> //= b' bc IH.
      rewrite inE=> /orP [/eqP ->|].
      + move=> /andP [] _ /andP [] _ /= /(order_path_min lt_slots_trans). 
        rewrite all_cat=>/andP [] _ /=.
        by rewrite andbC /= /lt_slots GenesisSlot. 
      + move: IH. case: bc=> // b'' bc IH H.
        rewrite -[b'' :: _]cat1s -catA cat1s valid_chain_ext.
        do 3! move=> /andP [] _.
        by rewrite -cat1s catA cat1s=> /(IH H). 
    - by move: mem_bc => /best_chain_in_all; rewrite mem_filter => /andP [] ->. }
  have in_b: t_now N0 <= sl b + 1 <= t_now N.
  { move: le_sl_lt =>/andP [] H1 H2; apply/andP; constructor.
    - by apply/(leq_trans H1); rewrite addn1.
    - move: H2. rewrite subn1. 
      rewrite -(leq_add2r 1) 2!addn1=> H2. 
      apply/(ltn_leq_trans H2). rewrite ltn_predL.
      by apply/(ltn_leq_trans (monotone_time N0N)). }
  have in_b': t_now N0 <= sl b <= sl b +1 .
  { move: le_sl_lt => /andP [] ??.  apply/andP; constructor; try done. 
    by rewrite addn1. }
  have prog_N0 : N0 @ Ready by done.
  move: (slot_in_between prog_N0 N0N in_b)=> [] N2 [] prog_N2 [] t_N2 [] N0N2 N2N. 
  move: (in_b'). rewrite -t_N2.
  move/(slot_in_between prog_N0 N0N2) => [] N1 [] prog_N1 [] t_N1 [] N0N1 N1N2.
  have b_in_hist_N : b \in (block_history N). 
  { move: mem_bc=> /best_chain_in_all.
    move/filter_subset /(subset_honest_tree N0N honest_p state_pN) => b_in_ht. 
    apply/not_gb_honest_tree_history_subset=> //.
      by rewrite mem_filter /= eq_gb b_in_ht. }
  have lt_b_N2 : sl b < t_now N2 by rewrite t_N2 addn1 . 
  have b_in_hist_N2: b \in block_history N2.
  { move: (honest_blocks_below_slot_preserved N0N2 N2N ff b).
      by rewrite !mem_filter honest_b lt_b_N2 /= => ->. }
  exists N2. exists (bid b). do ! constructor; try done.
  move: N1N2 N2N t_N1 t_N2 prog_N1 prog_N2 b_in_hist_N2. 
  (** We reason backwards starting from [N2]. Everything but last step
      being an increment or permutation step is a contradiction.
      Permutation steps follows by IH, but a little bookkeeping needs
      to be done. **)
  elim=> // ; first by move => _ ->; rewrite addn1=> /n_Sn. 
  move=> A B [] {A B} //; last first. 
  (** PermMsgs **)
  { move=> N2_B perm prog_N2_B N1N2_B IH N'N ?????.
    apply/IH=> //. apply/big_step_trans.
    - econstructor 2.
      + by apply/(@PermMsgs N2_B perm).  
      + by constructor. 
    - done. }
  (** PermParties **)
  { move=> N2_B perm prog_N2_B N1N2_B IH N'N ?????.
    apply/IH=> //. apply/big_step_trans.
    - econstructor 2.
      + by apply/(@PermParties N2_B perm).  
      + by constructor. 
    - done. }
  (** Increment case **)
  move=>/= N2_B prog_N2_B N1N2_B _.
  rewrite /(_ [[_ := _]]). 
  set N2_I := mkGlobalState _ _ _ _ _ _ _. move=> N2_IN.
  rewrite addn1=> t_N1. case=> t_N2_B prog_N1 _.
  rewrite -/(block_history _) /has_state //=. 
  have N2_BN: N2_B ⇓ N.
  { apply/(big_step_trans _ N2_IN).
    by econstructor 2; constructor. }
  move: N2_BN t_N1 t_N2_B prog_N1 prog_N2_B=> {N2_IN N2_I}. 
  (** We reason backwards reasoning starting from [N2_B]. Everything
      but last step being a baking or permutation step is a contradiction. **)
  elim: N1N2_B => // ; first by move => _ _ _ ->. 
  move=> A B [] {A B} //=; last first.
  (** PermParties **)
  { move=> N1_D perm prog_N1_D N1N1_D IH N'N ?????.
    apply/IH=> //. apply/big_step_trans.
    - econstructor 2.
      + by apply/(@PermMsgs N1_D perm).  
      + by constructor. 
    - done. }
  (** Baking case **)
  { move=> N1_D perm prog_N1_D N1N1_D IH N'N ?????.
    apply/IH=> //. apply/big_step_trans.
    - econstructor 2.
      + by apply/(@PermParties N1_D perm).  
      + by constructor. 
    - done. }
  (** Baking case **)
  move => N1_D prog_N1_D N1N1_D _.
  rewrite /(_ [[_ := _]]). 
  set N1_B := mkGlobalState _ _ _ _ _ _ _.
  move=> N1_BN t_N1.
  have N1_DN: N1_D ⇓ N.
  { apply/(big_step_trans _ N1_BN).
    by econstructor 2; constructor. }
  rewrite baking_preserves_time=> t_N1_D prog_N1 _.
  (* move=> {N1_BN N1_B}. *)
  have N0N1_D : N0 ⇓ N1_D by apply/(big_step_trans N0N1).
  have ff_ND : forging_free N1_D.
  { by apply/(forging_free_prev _ ff). }
  have : b \notin block_history N1_D. 
  { move: (no_premature_honest_blocks_D
             (big_step_trans N0N1 N1N1_D)
             ff_ND
             prog_N1_D)=> /allP /(_ b).
    rewrite mem_filter honest_b t_N1_D ltnn /=.
      by case: (_ \in _) => //= /trueI. }
  rewrite single_party_bake_step_state; last by apply/(big_step_trans N0N1 N1N1_D). 
  move=> b_not_in.
  have : uniq (exec_order N1_D).
  { by apply/(uniq_exec_order (big_step_trans N0N1 N1N1_D)). }
  move: (baking_steps_refl N1_B). 
  move/ProgressB. 
  elim: exec_order=> //=.
  - by move: b_not_in; case: (_ \in _) => //= /trueI. 
  - move=> p' ps. 
    have ff_NB : forging_free N1_B.
    { by apply/(forging_free_prev _ ff). }
    move=> + /BakeStep. set N' := foldr _ _ _.
    move=> IH bs /andP [] p'notin /IH. move/(_ bs) => {} IH.
    rewrite {1}/party_bake_step_world.
    case state_p': (_.[? _])=> [l'|]//=. 
    case honest_p': (~~_)=> //=. 
    + rewrite /honest_bake /=. case winner: Winner=> //.
      have pkp'eq: pk l' = p'. 
      { by apply/(bakes_preserves_pk (big_step_trans N0N1 N1N1_D))/state_p'. }
      case: l' state_p' winner pkp'eq => tT pk t. set l'' := (@mkLocalState _ _ (extendTree _ _)).
      move=> /= state_p' winner pkp'eq. 
      set nb := MkBlock _ _ _.
      rewrite inE=> /orP [/eqP beq| //].
      exists l''.  constructor. 
      * rewrite beq. rewrite /l'' /= pkp'eq. move: state_p'. 
        rewrite no_state_change_bake_different_parties // => state_p'.
        rewrite /party_bake_step_world state_p' honest_p' /honest_bake /=.
        move: winner. rewrite baking_preserves_time=> -> /=.
        by rewrite fnd_set eq_refl pkp'eq. 
      * rewrite subn1 /= -/nb.
        move /valid_chain_cons: (best_chain_valid t (t_now N' - 1)).  
        move=> [] b' [] bsT'. set bc := b'  :: bsT'. move=> bceq. 
        rewrite /nb.
        have bbc_valid : valid_chain (b :: bc).
        { rewrite valid_chain_ext -/bc bceq best_chain_valid beq.
          apply/andP; constructor; [|apply/andP; constructor]. 
          - by rewrite /= winner. 
          - by rewrite /= -bceq. 
          - rewrite andbC /=. apply/(@leq_ltn_trans (t_now N' -1)). 
            + move: (@best_chain_in_all _ (t_now N' - 1) t b').
              rewrite -bceq mem_head=> /trueI. 
              by rewrite mem_filter=> /andP []. 
            + rewrite subn1 ltn_predL baking_preserves_time.
              by apply/lt_0_time/(big_step_trans N0N1). }
        have bcbsT: (bestChain (t_now N' - 1) t) = bsT. 
        { rewrite -bceq.
          apply/(@eq_head_eq_chains N _ _ b)=> //; last first. 
          - apply/(subset_trans _ (honest_tree_hist_gb_subset N0N)).
            apply/(subset_trans _ (subset_honest_tree N0N honest_p state_pN)). 
            apply/(@subset_trans _ _ (bestChain (t_now N - 1) (tree l))).
            + by rewrite bc_layout -cat1s catA; apply/subset_catl. 
            + apply/(subset_trans (@best_chain_in_all _ (t_now N - 1) (tree l))).
              by apply/filter_subset. 
          (** We need that [N1_D ⇓ N] in order to use monotonicity of blockhistories. **)
          - apply/(subset_trans _ (block_hist_gb_montone N1_DN)). move: state_p'.
            rewrite no_state_change_bake_different_parties // => state_p'.
            apply/(subset_trans _ (honest_tree_hist_gb_subset N0N1_D)).
            move: honest_p' (honest_not_corrupt p') -> => honest_p'.
            apply/(subset_trans _ (subset_honest_tree N0N1_D honest_p' state_p')). 
            apply/(@subset_trans _ _ (bestChain (t_now N' - 1) t)) => //.
            - by rewrite bceq. 
            - apply/(subset_trans (@best_chain_in_all _ (t_now N' - 1) t)).
              apply/filter_subset. }
        rewrite -/nb. apply/anti_leq/andP. constructor.  
        -- rewrite -bcbsT baking_preserves_time.
           by apply/bc_ext_max_increase; rewrite /nb baking_preserves_time. 
        -- apply/(@ltn_leq_trans (|b :: bsT|))=> //. 
           apply/best_chain_best=> //. 
           rewrite beq /= -/nb=> b''.
           rewrite mem_filter all_extend mem_cat orbC inE inE andbC. 
           case: (_==_)/eqP=> [->|_] //=; first by rewrite baking_preserves_time.
           rewrite -bcbsT=> /best_chain_in_all.
           rewrite mem_filter andbC => /andP [] -> /= /leq_trans -> //.
           by rewrite subn1 baking_preserves_time leq_pred. 
    + case: ff_NB=> _ /(_ _ bs) /=. 
      case: AdversarialBake=> + ? /=. elim => //= [ [] ] m ? ms IH' /= H.
      rewrite inE => /orP [/eqP beqm |]. 
      * apply/IH. move: honest_b (H b). rewrite -beqm /honest_block => ->.
        rewrite mem_head => /trueI. 
          by rewrite mem_filter=> /andP [] _ ->. 
      * move/IH' => H'. apply/H'=> /=. 
        apply/(subset_trans _ H). case: is_honest=> //. 
          by apply/subset_cons. 
Qed.

Lemma honest_block_state_ext N' N p l bsH b bsT :
  N0 ⇓ N' ->
  N' ⇓ N ->
  forging_free N ->
  collision_free N ->
  N' @ Ready ->
  is_honest p ->
  has_state p N l ->
  honest_block b ->
  t_now N' <= sl b ->
  bsH ++ (b :: bsT) = bestChain (t_now N-1) (tree l) ->
  exists N2 p',
    N' ⇓ N2
    /\ N2 ⇓ N
    /\ t_now N2 = sl b + 1
    /\ N2 @ Ready
    /\ is_honest p'
    /\ exists l', has_state p' N2 l'
    /\ |(bestChain (t_now N2 -1) (tree l'))| = |b :: bsT|.
Proof.
  (** We start out noting a couple of usefull facts**)
  move=> N0N' N'N ffN no_coll prog_N' honest_p state_pN honest_b slb /esym bc_layout.
  have: exists s' s'' , bestChain (t_now N-1) (tree l) = s' ++ (b :: s''). 
  { by exists bsH; exists bsT. }
  move/inP => mem_bc.
  have bbsT_valid : valid_chain (b :: bsT).
  { move: (best_chain_valid (tree l) (t_now N -1)). 
    by rewrite bc_layout=> /valid_chain_short_l. }
  (** We note b is the GenesisBlock, as it has a slot number higher
      than one. **)
  have eq_gb: (b == GenesisBlock) = false. 
  { move: slb. case : (_ == _)/eqP => [->|] //.
    rewrite GenesisSlot.
      by move/ltn_leq_trans: (lt_0_time N0N') => H /H. }
  (** If the block is different from GB it must have been mined by
      sonme honest party, and we know that the first time this can
      happen is in round [sl b]. **)
  have le_sl_lt: t_now N' <= sl b <= (t_now N -1 ). 
  { apply/andP. constructor; [done|].
    by move: (@best_chain_time _ (tree l) (t_now N -1))=> /(_ b) -> //. }
  have N0N : N0 ⇓ N by apply/(big_step_trans N0N' N'N). 
  have in_b: t_now N' <= sl b + 1 <= t_now N.
  {
    move: le_sl_lt =>/andP [] H1 H2; apply/andP; constructor.
    - by apply/(leq_trans H1); rewrite addn1.
    - move: H2. rewrite subn1.
      rewrite -(leq_add2r 1) 2!addn1=> H2.
      apply/(ltn_leq_trans H2). rewrite ltn_predL.
      by apply/lt_0_time. }
  have in_b': t_now N' <= sl b <= sl b +1 .
  { move: le_sl_lt => /andP [] ??.  apply/andP; constructor; try done. 
    by rewrite addn1. }
  (** We find the slot just after b has been baked. **)
  move: (slot_in_between prog_N' N'N in_b)=> [] N2 [] prog_N2 [] t_N2 [] N'N2 N2N. 
  move: (in_b'). rewrite -t_N2.
  (** And the slot that b is baked in. **)
  move/(slot_in_between prog_N' N'N2) => [] N1 [] prog_N1 [] t_N1 [] N'N1 N1N2.

  have b_in_hist_N : b \in (block_history N). 
  { move: mem_bc=> /best_chain_in_all.
    move/filter_subset /(subset_honest_tree N0N honest_p state_pN) => b_in_ht. 
    apply/not_gb_honest_tree_history_subset=> //.
      by rewrite mem_filter /= eq_gb b_in_ht. }
  have lt_b_N2 : sl b < t_now N2 by rewrite t_N2 addn1 . 
  have N0N2: N0 ⇓ N2 by apply/(big_step_trans N0N' N'N2).
  have b_in_hist_N2: b \in block_history N2.
  { move: (honest_blocks_below_slot_preserved N0N2 N2N ffN b).
      by rewrite !mem_filter honest_b lt_b_N2 /= => ->. }
  exists N2. exists (bid b). do ! constructor; try done.
  move: N1N2 N2N t_N1 t_N2 prog_N1 prog_N2 b_in_hist_N2. 
  (** We reason backwards starting from [N2]. Everything but last step
      being an increment or permutation step is a contradiction.
      Permutation steps follows by IH, but a little bookkeeping needs
      to be done. **)
  elim=> //= ; first by move => _ ->; rewrite addn1=> /n_Sn. 
  move=> A B [] {A B} //=; last first. 
  (** PermMsgs **)
  { move=> N2_B perm prog_N2_B N1N2_B IH N''N ?????.
    apply/IH=> //. apply/big_step_trans.
    - econstructor 2.
      + by apply/(@PermMsgs N2_B perm).  
      + by constructor. 
    - done. }
  (** PermParties **)
  { move=> N2_B perm prog_N2_B N1N2_B IH N''N ?????.
    apply/IH=> //. apply/big_step_trans.
    - econstructor 2.
      + by apply/(@PermParties N2_B perm).  
      + by constructor. 
    - done. }
  (** Increment case **)
  move=> N2_B prog_N2_B N1N2_B _.
  rewrite /(_ [[_ := _]]). 
  set N2_I := mkGlobalState _ _ _ _ _ _ _. move=> N2_IN.
  rewrite addn1=> t_N1. case=> t_N2_B prog_N1 _.
  rewrite -/(block_history _) /has_state //=. 
  have N2_BN: N2_B ⇓ N.
  { apply/(big_step_trans _ N2_IN).
    by econstructor 2; constructor. }
  move: N2_BN t_N1 t_N2_B prog_N1 prog_N2_B=> {N2_IN N2_I}. 
  (** We reason backwards reasoning starting from [N2_B]. Everything
      but last step being a baking or permutation step is a contradiction. **)
  elim: N1N2_B => //= ; first by move => _ _ _ ->. 
  move=> A B [] {A B} //=; last first.
  (** PermParties **)
  { move=> N1_D perm prog_N1_D N1N1_D IH N''N ?????.
    apply/IH=> //. apply/big_step_trans.
    - econstructor 2.
      + by apply/(@PermMsgs N1_D perm).  
      + by constructor. 
    - done. }
  (** Baking case **)
  { move=> N1_D perm prog_N1_D N1N1_D IH N''N ?????.
    apply/IH=> //. apply/big_step_trans.
    - econstructor 2.
      + by apply/(@PermParties N1_D perm).  
      + by constructor. 
    - done. }
  (** Baking case **)
  move => N1_D prog_N1_D N1N1_D _.
  rewrite /(_ [[_ := _]]). 
set N1_B := mkGlobalState _ _ _ _ _ _ _.
  move=> N1_BN t_N1.
  have N1_DN: N1_D ⇓ N.
  { apply/(big_step_trans _ N1_BN).
    by econstructor 2; constructor. }
  rewrite baking_preserves_time=> t_N1_D prog_N1 _.
  have ff_NB : forging_free N1_B.
  { by apply/(forging_free_prev _ ffN). }
  have N0N1_D : N0 ⇓ N1_D. 
  { by apply/(big_step_trans N0N')/(big_step_trans N'N1). }
  have ff_ND : forging_free N1_D.
  { by apply/(forging_free_prev _ ffN). }
  have : b \notin block_history N1_D. 
  { move: (no_premature_honest_blocks_D
             N0N1_D
             ff_ND
             prog_N1_D)=> /allP /(_ b).
    rewrite mem_filter honest_b t_N1_D ltnn /=.
      by case: (_ \in _) => //= /trueI. }
  rewrite single_party_bake_step_state //. 
  move=> b_not_in. move: (uniq_exec_order N0N1_D). 
  move/ProgressB: (baking_steps_refl N1_B). 
  elim: exec_order=> //=.
  - by move: b_not_in; case: (_ \in _) => //= /trueI. 
  - move=> p' ps. 
    move=> + /BakeStep. set N'' := foldr _ _ _.
    move=> IH bs /andP [] p'notin /IH. move/(_ bs) => {} IH.
    rewrite {1}/party_bake_step_world.
    case state_p': (_.[? _])=> [l'|]//=. 
    case honest_p': (~~_)=> //=. 
    + rewrite /honest_bake /=. case winner: Winner=> //.
      have pkp'eq: pk l' = p'. 
      { by apply/(bakes_preserves_pk N0N1_D)/state_p'. }

      case: l' state_p' winner pkp'eq => tT pk t. set l'' := (@mkLocalState _ _ (extendTree _ _)).
      move=> /= state_p' winner pkp'eq. 
      set nb := MkBlock _ _ _. rewrite inE=> /orP [/eqP beq| //].
      exists l''.  constructor. 
      * rewrite beq /= pkp'eq. move: state_p'.
        rewrite no_state_change_bake_different_parties // => state_p'.
        rewrite /party_bake_step_world state_p' honest_p' /honest_bake /=.
        move: winner. rewrite baking_preserves_time=> ->.
        by rewrite /= fnd_set eq_refl /l'' baking_preserves_time. 
      * rewrite subn1 /= -/nb.
        move /valid_chain_cons: (best_chain_valid t (t_now N'' - 1)).  
        move=> [] b' [] bsT'. set bc := b'  :: bsT'. move=> bceq. 
        rewrite /nb.
        have bbc_valid : valid_chain (b :: bc).
        { rewrite valid_chain_ext -/bc bceq best_chain_valid beq.
          apply/andP; constructor; [|apply/andP; constructor]. 
          - by rewrite /= winner. 
          - by rewrite /= -bceq. 
          - rewrite andbC /=. apply/(@leq_ltn_trans (t_now N'' -1)). 
            + move: (@best_chain_in_all _ (t_now N'' - 1) t b').
              rewrite -bceq mem_head=> /trueI. 
              by rewrite mem_filter=> /andP []. 
            + rewrite subn1 ltn_predL baking_preserves_time.
              by apply/lt_0_time. }
        have bcbsT: (bestChain (t_now N'' - 1) t) = bsT. 
        { rewrite -bceq.
          apply/(@eq_head_eq_chains N _ _ b)=> //; last first. 
          - apply/(subset_trans _ (honest_tree_hist_gb_subset N0N)).
            apply/(subset_trans _ (subset_honest_tree N0N honest_p state_pN)). 
            apply/(@subset_trans _ _ (bestChain (t_now N - 1) (tree l))).
            + by rewrite bc_layout -cat1s catA; apply/subset_catl. 
            + apply/(subset_trans (@best_chain_in_all _ (t_now N - 1) (tree l))).
              by apply/filter_subset. 
          (** We need that [N1_D ⇓ N] in order to use monotonicity of blockhistories. **)
          - apply/(subset_trans _ (block_hist_gb_montone N1_DN)). move: state_p'.
            rewrite no_state_change_bake_different_parties // => state_p'.
            apply/(subset_trans _ (honest_tree_hist_gb_subset N0N1_D)).
            move: honest_p' (honest_not_corrupt p') -> => honest_p'.
            apply/(subset_trans _ (subset_honest_tree N0N1_D honest_p' state_p')). 
            apply/(@subset_trans _ _ (bestChain (t_now N'' - 1) t)) => //.
            - by rewrite bceq. 
            - apply/(subset_trans (@best_chain_in_all _ (t_now N'' - 1) t)).
              apply/filter_subset. }
        rewrite -/nb. apply/anti_leq/andP. constructor.  
        -- rewrite -bcbsT baking_preserves_time.
           by apply/bc_ext_max_increase; rewrite /nb baking_preserves_time. 
        -- apply/(@ltn_leq_trans (|b :: bsT|))=> //. 
           apply/best_chain_best=> //. 
           rewrite beq /= -/nb=> b''.
           rewrite mem_filter all_extend mem_cat orbC inE inE andbC. 
           case: (_==_)/eqP=> [->|_] //=; first by rewrite baking_preserves_time.
           rewrite -bcbsT=> /best_chain_in_all.
           rewrite mem_filter andbC => /andP [] -> /= /leq_trans -> //.
           by rewrite subn1 baking_preserves_time leq_pred. 
    + case: ff_NB=> _ /(_ _ bs) /=.
      case: AdversarialBake=> + ? /=. elim => //= [ [] ] m ? ms IH' /= H.
      rewrite inE => /orP [/eqP beqm |]. 
      * apply/IH. move: honest_b (H b). rewrite -beqm /honest_block => ->.
        rewrite mem_head => /trueI. 
          by rewrite mem_filter=> /andP [] _ ->. 
      * move/IH' => H'. apply/H'=> /=. 
        apply/(subset_trans _ H). case: is_honest=> //. 
          by apply/subset_cons. 
Qed. 

Lemma party_party : forall (p : Party), p \in enum [finType of Party].
  by move=> p; rewrite mem_enum.
Qed.

Lemma limit_adv_bp s e bs:
  all (fun b => s <= sl b < e) bs ->
  correct_blocks bs ->
  decreasing_slots bs ->
  |[seq x <- bs | predC honest_block x]| <= |adv_slots_range s e|.
Proof.
  case seleq: (s < e); last first. 
  { elim: bs=> //= b bs IH /andP [] /andP [] H1 H2.
    by move: (leq_ltn_trans H1 H2); rewrite seleq. }
  have se : s + (e - s) = e by apply/subnKC/ltnW. 
  rewrite /adv_slots_range /p_slots_range. 
  rewrite /nat_range.
  move=> range cr dec. 
  have sub: {subset [seq sl b | b <- bs] <= iota s (e - s)}. 
  { move=> n /mapP [] b + ->.
      by rewrite mem_iota se; move/allP: range=> H /H. }
  rewrite -(size_map sl). 
  apply/uniq_leq_size.
  - move: dec=> /= /(sorted_filter lt_slots_trans (predC honest_block)).
    rewrite sorted_blocks_slots => /(sorted_uniq _ ltnn) -> //.
    + by apply/gtn_trans.
  - move: sub range cr. rewrite /correct_blocks=> {dec}.
    elim: bs=> //= b bs IH sub /andP [] leq range /andP [] c cbs.
    case honest_b: (~~_)=> //=; last first.
    + by apply/IH=> //; apply/(subset_trans _ sub)/subset_cons.
    + move=> b'. rewrite inE=> /orP [/eqP ->|]; last first.
      * by move: b'; apply/IH=> //; apply/(subset_trans _ sub)/subset_cons.
      * rewrite mem_filter /adv_slot /adv_slot_gen.
        apply/andP. constructor; last by rewrite mem_iota se. 
        apply/hasP. exists (bid b); last first.
        -- move: c. rewrite /correct_block=> -> /=.
             by move: honest_b; rewrite honest_not_corrupt=> /negbNE.
        -- apply/party_party.   
Qed. 

Lemma limit_adv_bp_imply_honesty s e bs w:
  all (fun b => s <= sl b < e) bs ->
  correct_blocks bs ->
  decreasing_slots bs -> 
  |adv_slots_range s e| + w <= |bs| -> w <= |honest_blocks bs|. 
Proof.
  move=> range cr dec.  rewrite -(count_predC honest_block).
  rewrite -2!size_filter addnC -/(honest_blocks _).
  set advs := |_|.
  move: (limit_adv_bp range cr dec)=> H1 H2. 
  rewrite -(leq_add2r advs). 
  by apply/(leq_trans H2); rewrite leq_add2l. 
Qed. 

(** *Chain Quality*)

Lemma chain_quality :
  forall N p l b_j b_i c w,
    let bc := bestChain ((t_now N)-1) (tree l) in 
    let f := [:: b_j] ++ c ++ [:: b_i] in 
    N0 ⇓ N ->
    forging_free N ->
    collision_free N ->
    has_state p N l -> is_honest p ->
    fragment f bc ->
    honest_advantage_ranges_gt w (sl b_j - (sl b_i +1)) ->
    (w -1) <= |honest_blocks f|.
Proof.
  move=> N p l b_j b_i c w bc f N0N ffN no_coll state_p honest_p frag.
  move: frag=> [] c1 [] c2. rewrite /f -2!catA=> {f} c_layout1.
  (** We make a quick check that w is larger than 0. **)
  case weq0: (w == 0)/eqP=> [-> //| _].
  move/neq0_lt0n: weq0 => wgt0. 
  (** We start out by defining the previous honest block in the chain. *)
  have c_layout2: exists c2', c2' ++ [:: GenesisBlock] = [:: b_i] ++ c2. 
  { move: (best_chain_starts_gb (tree l) ((t_now N) -1 )) c_layout1 => [] bc'. 
    rewrite /bc => <-. set A := _ ++ c2.  
    rewrite 2!catA. set B := _ ++ c. move=> H'. 
    have H'': exists bc'', bc' = B ++ bc''.
    { move: H'. rewrite/A; clear. move: b_i B bc'.  
      elim: c2=> //=  [|b bs IH] b' B bc. 
      - rewrite 2!cats1=>/rcons_inj [] -> _.
          by (exists [::]; rewrite cats0).
      - rewrite -cat1s catA=>/IH [] bc'' ->.
          by (rewrite -catA cat1s; exists (b' :: bc'')). }
    move: H'' H'=> [] bc'' ->. 
    by (rewrite -catA=>/cat_injr ->;exists bc''). }
  have: findo honest_block ([:: b_i] ++ c2). 
  { move: c_layout2 => [] c2' <-. rewrite findo_has. apply/hasP.
      by exists GenesisBlock; [rewrite mem_cat orbC mem_head | rewrite /= HonestGB]. }
  move/findoP=> [] c21 [] c22 [] b_i' [] c_layout3 [] honest_b_i' honesty_c21.
  have b_i'_le_b_i : sl b_i' <= sl b_i.
  { move: (best_chain_valid (tree l) (t_now N-1)). 
    rewrite -/bc -c_layout1 [ [::b_i] ++ _]cat1s !catA=> /valid_chain_short_l.
    move: c_layout3. clear. case: c21=> [ [] ->| ]//=.
    move=> b bs [] <- <- /andP [] _ /andP [] _ /(order_path_min lt_slots_trans).
    rewrite /lt_slots=> /allP /(_ b_i').
      by rewrite mem_cat orbC mem_head /= => /trueI /ltnW. }
  move=> advantH.
  apply/(@leq_trans (| honest_blocks ([:: b_j] ++ c ++ c21)|)); last first. 
  { rewrite /honest_blocks !filter_cat !size_cat 2!leq_add2l.  
    apply/(@leq_trans 0)=> //.
    rewrite leqn0 size_eq0. apply/eqP. move: honesty_c21; clear.
    elim: c21=> //= > + /andP [] + ?. move->=> //=.
      by rewrite -eqbF_neg=> /eqP ->. }
  have c_layout4: (c1 ++ [:: b_j] ++ c ++ c21) ++ (b_i' :: c22)
                  = bestChain (t_now N - 1) (tree l). 
  { by rewrite -/bc -c_layout1 -c_layout3 !catA. }
  move: (honest_block_state N0N ffN no_coll honest_p state_p honest_b_i' c_layout4). 
  move=> [] N_i' [] p_i' [] N0N_i' [] N_i'N [] t_N_i' [] prog_N_i' [] honest_p_i'.
  move=> [] l_i' [] state_p_i' bc_p_i'.
  (** Next we make two cases based on if there are any
      honest blocks in the front of the chain.  **)
  case hb_front: ((rfindo honest_block (c1 ++ [:: b_j])) :bool); last first. 
  (** No honest block in front of chain.**)
  { move: hb_front. rewrite rfindo_has=> /negbT.
    rewrite -all_predC=> dishonestH.
    have -> : honest_blocks ([:: b_j] ++ c ++ c21)
             = honest_blocks (c1 ++ [:: b_j] ++ c ++ c21). 
    { rewrite /honest_blocks. symmetry. rewrite filter_cat.
      suff: [seq b <- c1 | honest_block b] = [::] by move->.
      move: dishonestH. rewrite all_cat=> /andP [] + _. clear. 
      by elim: c1=> //= b bs IH /andP [] /negbTE ->. }
    have N_i'_Ns: N_i' ⇓^+ N.
    { constructor; [done|]. 
      rewrite t_N_i' addn1.
      apply/(@leq_ltn_trans (t_now N -1)); last first. 
      - by rewrite subn1 ltn_predL; apply/lt_0_time. 
      - apply/(@leq_trans (sl b_j)); last first. 
        + move: (@best_chain_in_all _ (t_now N -1) (tree l)).
          rewrite -c_layout4 => /(_ b_j).
          rewrite mem_filter -catA mem_cat orbC !mem_cat inE eq_refl /=.
            by move=> /trueI /andP []. 
        + move: (best_chain_valid (tree l) (t_now N -1)).
          rewrite -c_layout4 /= -!catA=> /valid_chain_short_l.
          rewrite -/cat=> /andP [] _ /andP [] _ /(order_path_min lt_slots_trans).
          move/allP=> /(_ b_i').
            by rewrite mem_cat orbC mem_head /= => /trueI. }
    move: advantH. rewrite /honest_advantage_ranges_gt.
    move=> /(_ (sl b_i').+1). move=> /(_ (t_now N-1)). 
    have H: sl b_j- (sl b_i+1) <= t_now N -1 - ((sl b_i').+1).
    { apply/leq_sub=> //.
      move: (@best_chain_time _ (tree l) (t_now N -1))=> /(_ b_j).
        by rewrite -/bc -c_layout1 mem_cat orbC mem_head /= => /trueI.
        rewrite addn1. by apply/(leq_ltn_trans b_i'_le_b_i). }
    move=> /(_ H) {H}. rewrite -addn1 -t_N_i' /honest_advantage_range => advant.
    move: (@chain_growth_parties
             (| adv_slots_range (t_now N_i') (t_now N - 1) | + w)
             N_i' N
             p_i' p
             l_i' l
             N0N_i' N_i'_Ns
             prog_N_i'
             honest_p_i' honest_p
             state_p_i' state_p
             advant).
    rewrite -c_layout4 size_cat bc_p_i' addnC leq_add2r. move=> H.
    move: (best_chain_valid (tree l) (t_now N -1)). rewrite -c_layout4=> vc.
    have: | adv_slots_range (t_now N_i') (t_now N) | + (w -1) <= | c1 ++ [:: b_j] ++ c ++ c21 |. 
    { apply/(leq_trans _ H).
      rewrite /adv_slots_range /p_slots_range /nat_range.
      have ->: (t_now N - t_now N_i') = (t_now N - 1 - t_now N_i') + 1.
      { apply/esym. rewrite -subnDA. rewrite [1 + _]addnC.
        rewrite subnDA subn1 addn1 prednK // subn_gt0.
        rewrite t_N_i' addn1. apply/(@leq_ltn_trans (t_now N -1)); last first.
        - by rewrite subn1 ltn_predL lt_0_time. 
        - apply/(@ltn_leq_trans (sl b_j)); last first.
          + apply/(@best_chain_time _ (tree l)). rewrite -c_layout4.
            by rewrite 2!mem_cat mem_head -orbA orbC.
          + move: vc. rewrite cat1s -!catA => /valid_chain_short_l /andP [] _ /andP [] _.
            move/(order_path_min lt_slots_trans)/allP.
            rewrite -/(cat _ _)=> /(_ b_i').
            by rewrite mem_cat orbC mem_head => /trueI. }
      rewrite iota_add filter_cat size_cat -addnA leq_add2l => /=.
      case: (adv_slot) => //=.
      - by rewrite addnBA // addnC addn1 subn1 /= leqnn. 
      - by rewrite add0n subn1 leq_pred. }
    apply/limit_adv_bp_imply_honesty.
    - apply/allP. move=> b b_in. 
      apply/andP. constructor.
      + rewrite t_N_i' addn1. move:vc=> /andP [] _ /andP [] _ /=. move: b_in.
        elim: (_ ++ _ )=> //= b' bs IH. rewrite inE=> /orP [/eqP ->| /IH].
        * move/(order_path_min lt_slots_trans)/allP/(_ b_i').
          by rewrite mem_cat mem_head orbC /= => /trueI. 
        * by move=> {} IH path; apply/IH; move/path_sorted: path.
      + move:(@best_chain_time _ (tree l) (t_now N -1))=> /(_ b).
        rewrite -c_layout4 mem_cat b_in /= => /trueI le.
        apply/(leq_ltn_trans le). rewrite subn1 ltn_predL.
        by apply/lt_0_time. 
    - by move/andP: vc =>[] /=; rewrite /correct_blocks all_cat => /andP []. 
    - by move/andP :vc=> [] _ /andP [] _ /= /sorted_cat /andP []. }
  (** Case where there is an honest block in front of the chain. **)
  { move/rfindoP: hb_front => [] c11 [] c12 [] b_j'.
    move=> [] c_layout5 [] honest_b_j' honest_c12.
    apply/(@leq_trans (| honest_blocks (c12 ++ c ++ c21)|)); last first. 
    { rewrite /honest_blocks filter_cat size_cat /=. 
      apply/(@leq_trans (| [seq b <- c ++ c21 | is_honest (bid b)] |)). 
      - set bs := | _ |. suff: bs = 0 by move->.
        apply/eqP/nilP/eqP. 
        move: honest_c12. rewrite all_predC. 
        move/negbTE. rewrite has_filter /= /honest_block. 
          by case (_ ==_ ).
      - by case: (is_honest _)=> //=. } 
    have c_layout6: (c11 ++ b_j' :: (c12 ++ c ++ c21 ++ b_i' :: c22))
                  = bestChain (t_now N - 1) (tree l). 
    { rewrite -/bc -c_layout1.
        by apply/esym; rewrite catA -c_layout5 -!catA cat1s c_layout3. }
    have lt_N_i'b_j': t_now N_i' <= sl b_j'.
    { rewrite t_N_i' addn1.
      move: (best_chain_valid (tree l) (t_now N-1)).
      rewrite -c_layout6. move/valid_chain_short_l.
      move=> /andP [] _ /andP [] _ /(order_path_min lt_slots_trans)/allP/(_ b_i').
        by rewrite !catA mem_cat orbC mem_head => /trueI. }
    move: (honest_block_state_ext N0N_i' N_i'N ffN no_coll prog_N_i' honest_p state_p honest_b_j' lt_N_i'b_j' c_layout6). 
    move=> [] N_j' [] p_j' [] N_i'N_j' [] N_j'N [] t_N_j' [] prog_N_j' [] honest_p_j'.
    move=> [] l_j' [] state_p_j' bc_p_j'.
    move: advantH. rewrite /honest_advantage_ranges_gt.
    move=> /(_ (sl b_i' + 1)) /(_ (sl b_j')).
    have H: sl b_j - (sl b_i + 1) <= sl b_j' - (sl b_i' + 1). 
    { apply/leq_sub.
      - move: (best_chain_valid (tree l) (t_now N-1)).
        rewrite -c_layout6. move/valid_chain_short_l.
        have : b_j \in b_j' :: c12. 
        {  move: c_layout5. clear. move: c11 c1 b_j'. elim: c12. 
          - move=> c1 c2 b_j'. rewrite 2!cats1=> /rcons_inj [] _ ->.
              by rewrite mem_head. 
          - move=> b bs IH c1 c2 b'. rewrite catA -[b ::_]cat1s=> /IH.
            by rewrite cat1s [_ \in b' :: _]inE orbC => ->.  }
        rewrite inE=> /orP [/eqP ->|] // H1 H2. apply/ltnW.
        move/andP: H2 => [] _ /andP [] _ /(order_path_min (lt_slots_trans)).
          by move=> /allP /(_ b_j); rewrite mem_cat H1 /= => /trueI. 
      - by rewrite 2!addn1 ltnS. }
    have N_i'N_j's: N_i' ⇓^+ N_j'. 
    { constructor; [done|].
      rewrite t_N_j' t_N_i' 2!addn1 ltnS.
      move: (best_chain_valid (tree l) (t_now N-1)).
      rewrite -c_layout6=> /valid_chain_short_l => /andP [] _ /andP [] _.
      move/(order_path_min lt_slots_trans)/allP/(_ b_i').
        by rewrite !catA mem_cat orbC mem_head => /trueI. }
    move=> /(_ H) {H}.
    have ->: (sl b_j' = t_now N_j' - 1). 
    { by rewrite t_N_j' addn1 subn1 /=. }
    rewrite -t_N_i' /honest_advantage_range=> advant.
    move: (@chain_growth_parties
             (| adv_slots_range (t_now N_i') (t_now N_j' - 1) | + w)
             N_i' N_j'
             p_i' p_j'
             l_i' l_j'
             N0N_i' N_i'N_j's
             prog_N_i'
             honest_p_i' honest_p_j'
             state_p_i' state_p_j'
             advant). 
    rewrite bc_p_j' bc_p_i' addnC -[b_j' :: _]cat1s 3!catA size_cat leq_add2r.
    rewrite -!catA cat1s. move=> /=.
    move/(leq_sub2r 1). rewrite 3!subn1 /= -2!subn1. 
    rewrite -addnBA //. move: (best_chain_valid (tree l) (t_now N -1)).
    rewrite -c_layout6=> /valid_chain_short_l vc. 
    apply/limit_adv_bp_imply_honesty.
    - rewrite t_N_j' t_N_i' 2!addn1 subn1 /=.
      apply/allP=> b bin. apply/andP. constructor. 
      + move:vc=> /andP [] _ /andP [] _ /=.
        rewrite !catA -[(c12 ++ _) ++ _]catA. move: bin.
        elim: (c12 ++ c ++ c21 )=> //= b' bs IH. rewrite inE=> /orP [/eqP ->| /IH].
        * move=> /andP [] _ /(order_path_min lt_slots_trans) /allP/(_ b_i'). 
          by rewrite mem_cat mem_head orbC /= => /trueI. 
        * move=> {} IH path. apply/IH.
          rewrite path_min_sorted.
          -- by move/andP: path => [] _ /path_sorted. 
          -- apply/allP=> b'' b''in.
             move/andP: path => [] H1 H2. 
             apply/(lt_slots_trans H1). move/(order_path_min lt_slots_trans): H2.
               by move/allP/(_ b'')/(_ b''in).
      + move:vc=> /andP [] _ /andP [] _ /= /(order_path_min lt_slots_trans)/allP.
        by move=>/(_ b); rewrite !catA mem_cat -!catA bin => /trueI. 
    - move/andP: vc=> []. rewrite -cat1s /correct_blocks all_cat=> /andP [] _.
      by rewrite !catA all_cat => /andP []. 
    - move/andP: vc=> [] _ /andP [] _. rewrite -cat1s => /sorted_cat /andP [] _.
      by rewrite !catA=> /sorted_cat /andP []. }
Qed. 
