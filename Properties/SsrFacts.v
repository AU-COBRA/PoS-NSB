From mathcomp Require Import
     all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *Auxillirary lemmata *)

Lemma trueI (A : Type) : (true -> A) -> A. 
Proof. by move=>/(_ (eq_refl true)). Qed. 

Lemma in_not_in {T : eqType} (p p' : T) (ps : seq T) :
  p \in ps -> p' \notin ps -> p != p'.
Proof.
  elim: ps=> //= > IH. rewrite 2!in_cons=> /orP [/eqP ->| ?] //=.
  - rewrite eq_sym negb_or=> /andP [] //=.
  - by rewrite eq_sym negb_or=> /andP [] //= _ ?; apply: IH.
Qed.

Lemma gtn_trans : transitive gtn. 
Proof. by move=> > ? H; apply/(ltn_trans H). Qed. 

Lemma gtn_irr : irreflexive gtn.
Proof. by move=> ?; apply/ltnn. Qed. 

Lemma in_or_not_in {T : eqType} (p : T) (ps : seq T) :
  p \notin ps \/ p \in ps. 
Proof.  case: (_ \in _); by [constructor 2| constructor]. Qed.

Lemma subset_trans {T : eqType} (s1 s2 s3  : seq T) :
  {subset s1 <= s2} -> {subset s2 <= s3} -> {subset s1 <= s3}.
Proof. by move=>  H1 H2 ? /H1 /H2. Qed. 

Lemma subset_all {T : eqType} p (s1 s2 : seq T) :
  {subset s1 <= s2} -> all p s2 -> all p s1.
Proof.   
  elim: s1=> //= a s1' IH H H2.
  have H3: a \in s2 by rewrite H // mem_head. 
  apply/andP. constructor; last first.
  - apply: IH =>// a' H4. rewrite H // in_cons.
    apply/orP. by constructor 2.
  - move: H3=>/allP=> H3. by apply: H3.  
Qed.

Lemma subset_cons {T : eqType} (s: seq T) (x : T):
  {subset s <= x:: s}. 
Proof. by move=> ? H; rewrite in_cons H orbC. Qed. 

Lemma subset_cons2 {T : eqType} (s1 s2: seq T) (x : T):
  {subset s1 <= s2} -> {subset x::s1 <= x:: s2}. 
Proof.
  move=> sub ?. rewrite 2!in_cons => /orP [-> //| /sub ->].
    by rewrite orbC.
Qed. 

Lemma subset_catl {T : eqType} (s s': seq T):
  {subset s <= s' ++ s}. 
Proof. by move=> ? H; rewrite mem_cat H orbC. Qed. 

Lemma subset_catr {T : eqType} (s s': seq T):
  {subset s <= s ++ s'}. 
Proof. by move=> ? H; rewrite mem_cat H. Qed. 

Lemma subset_cat2 {T : eqType} (s1 s2 s3: seq T):
  {subset s1 <= s2} -> {subset s3 ++ s1 <= s3 ++ s2}. 
Proof. by move=> sb >; rewrite 2!mem_cat=> /orP [-> //| /sb ->]; rewrite orbC. Qed. 

Lemma filter_subset {T : eqType} p (s : seq T) :
  {subset [seq a <- s | p a] <= s}.
Proof. apply/mem_subseq/filter_subseq. Qed. 

Lemma subset_filter {T : eqType} p (s1 s2 : seq T) :
  {subset s1 <= s2} -> {subset [seq a <- s1 | p a] <= [seq a <- s2 | p a]}.
Proof. by move=> H ?; rewrite 2!mem_filter=> /andP [] -> /H ->. Qed. 

Lemma map_subset {T1 T2 : eqType} (s1 s2 : seq T1) (f : T1 -> T2) :
  {subset s1 <= s2} -> {subset [seq f x | x <- s1 ] <= [seq f x | x <- s2]}. 
Proof. by move=> H ? /mapP [] x /H ??; apply/mapP; exists x. Qed. 

Lemma subset_mem_eq (T : eqType) :
  forall (a b c : seq T),  {subset a <= c} -> b =i c  ->  (a ++ b) =i c. 
Proof.
  move=> > H1 H2 >. rewrite mem_cat H2.
  by case eq: (_ \in _)=> //=; rewrite H1.   
Qed. 

Lemma mem_eq_cons {T : eqType} (x : T) (s1 s2 : seq T) :
  (s1 =i s2) -> x :: s1 =i x :: s2.
Proof.
  by move=> H?; rewrite 2!inE H. 
Qed. 

Lemma subset_mem_eqW {T : eqType} (s1 s2 : seq T) :
  s1 =i s2 -> {subset s1 <= s2}. 
Proof. by move=> + ?; move->. Qed. 

Lemma mem_eq_nil  {T : eqType} (s : seq T) : [::] =i s -> s = [::].
Proof. by case: s => //= a ? H; move: (H a); rewrite mem_head. Qed.

Lemma inP {T : eqType} (s : seq T) a :
  reflect (exists s' s'', s = s' ++ (a :: s'')) (a \in s).
Proof. 
  case ineq: (_ \in _); constructor.
  - move: ineq. elim: s=> //= a' s IH.
    rewrite in_cons=> /orP [/eqP -> | /IH [s' [s'' ->] ] ].
    + by (exists [::]; exists s). 
    + by (exists (a' :: s'); exists s''). 
  - by move => [? [? H] ]; move: ineq; rewrite H mem_cat mem_head orbC. 
Qed. 

Lemma map_mem_eq  {T A : eqType} (f : T -> A) (s1 s2 : seq T) :
  s1 =i s2 -> [seq f a | a <- s1 ] =i [seq f a | a <- s2]. 
Proof. 
  move=> H b. case eqin : (_ \in _)=> //=.
  - move: eqin=> /mapP [? ]. rewrite H=> ? ->.
    by symmetry; apply/map_f. 
  - symmetry. apply/mapP. move=> [b' ]. rewrite -H=> ??. 
    move: eqin => /mapP eqin. apply/eqin. by exists b'. 
Qed. 

Lemma map_map {A B C : Type} (f : A -> B) (g : B -> C) (s : seq A):
  [seq g x | x <- [seq f x | x <- s] ] = [seq g (f x) | x <- s]. 
Proof. by elim: s => //= > <-. Qed. 

Lemma filter_mem_eq {T : eqType} p (s1 s2 : seq T) :
  s1 =i s2 -> [seq a <- s1 | p a] =i [seq a <- s2 | p a]. 
Proof. by move=> ??; rewrite 2!mem_filter; case: (p _)=> //=. Qed. 
  
Lemma predIC {T : Type} (p1 p2 : ssrbool.pred T):
  predI p1 p2 =1 predI p2 p1. 
Proof. by move=> ?; rewrite /predI /= andbC //=. Qed. 

Lemma map_nil {T1 T2 : Type} (f : T1 -> T2):
  forall t, [seq f x | x <- t] = [::] -> t = [::].
Proof. by elim. Qed.

Lemma cat_mem_eq_r {T : eqType} : forall (A B X : seq T),
    A =i B -> A ++ X =i B ++ X.
Proof. by move=> > H >; rewrite !mem_cat H. Qed.

Lemma cat_mem_eq {T : eqType} :
  forall (A B C D : seq T), A =i B -> C ++ B =i D -> C ++ A =i D.
Proof. by move=> > H ??; rewrite mem_cat H -mem_cat. Qed.

Lemma cat_mem_trans {T : eqType} :
  forall (A B C : seq T), A =i B -> B =i C ->  A =i C.
Proof. by move=> > ? H ?; rewrite -H. Qed.

Lemma mem_eq_sym {T : eqType} :
  forall (A B : seq T), A =i B -> B =i A.
Proof. by move=> > + ?; move->. Qed. 

Lemma true_is_true :
  forall X, true = X -> is_true X.
Proof. done. Qed.

(** Sorted **)
Lemma sorted_cat (T : Type) (r : rel T) (a b : seq T) :
  sorted r (a ++ b) -> sorted r a && sorted r b. 
Proof. by case: a=> //= >; rewrite cat_path=> /andP [] -> /= /path_sorted. Qed. 

(** Injectivity of cat. **)
Lemma cat_injr {T : Type} (s : seq T) : injective (cat s). 
Proof. by elim: s=> //= > IH > [] /IH. Qed. 

Lemma cat_injl {T : Type} (s : seq T) : injective (cat^~ s). 
Proof.
  elim: s=> [>| > IH >].
  - by rewrite 2!cats0. 
  - rewrite -cat1s 2!catA=> /IH. 
    by rewrite 2!cats1; apply/rcons_injl. 
Qed. 

(** The first item in s for which p holds or [None] if no such item is
    found. **)
Fixpoint findo {T : Type} (p : ssrbool.pred T) (s : seq T) :=
  if s is x :: xs then if p x then Some x else findo p xs else None.

Lemma findo_has {T : Type} (p : ssrbool.pred T) (s : seq T) :
  ((findo p s) : bool) = has p s.
Proof. by elim: s=> //= >; case: (p _). Qed.

Lemma findoP {T : Type} (p : ssrbool.pred T) (s : seq T) :
  reflect
    (exists s1 s2 x, s1 ++ [:: x] ++ s2 = s /\ p x /\ all (predC p) s1)
    (findo p s). 
Proof.
  elim: s=> //= [> | x s IH]. 
  - by constructor; move=> [] s [] ? [] ? []; case: s.
  - case pH: (p _)=> /=.
    + constructor. exists [::]. exists s. exists x. rewrite cat0s.
        by do! constructor.
    + apply/(iffP idP).
      * move/IH => [] s1 [] s2 [] x' [] <- [] H2 H3. 
        exists (x :: s1). exists s2. exists x'. rewrite -cat1s -catA 2!cat1s /=.
        do ! constructor; try done. 
          by rewrite pH H3. 
      * move=> [] s1 [] s2 [] x' [] H1 [] H2 H3.
        apply/IH. move: H1 H2 H3. 
        case: s1 => //= [ [] -> _ |]; first by rewrite pH.
        move=> x'' l [] -> <- ? /andP [] ??.
        exists l. exists s2. exists x'.
          by do ! constructor.
Qed.

Lemma perm_findo {T : eqType} (p : ssrbool.pred T) (s1 s2  : seq T):
  perm_eq s1 s2 -> (findo p s1 : bool) = (findo p s2 : bool). 
Proof. by move/perm_has; rewrite 2!findo_has. Qed. 

Lemma mem_findo {T : eqType} (p : ssrbool.pred T) (s1 s2  : seq T):
  s1 =i s2 -> (findo p s1 : bool) = (findo p s2 : bool). 
Proof. by move/eq_has_r; rewrite 2!findo_has. Qed. 

Lemma findoP' {T : eqType} (p : ssrbool.pred T) (s : seq T) (x : T):
  reflect
    (exists s1 s2, s1 ++ [:: x] ++ s2 = s /\ p x /\ all (predC p) s1)
    ((Some x) == (findo p s)). 
Proof. 
  elim: s x=> //= [> | x' s IH].
  - by constructor; move=> [] s [] ? []; case: s.
  - move=> x. apply/(iffP idP).
    + case pH: (p x')=> /=.
      * by case/eqP => ->; exists [::]; exists s.
      * move/IH => [] s1 [] s2 [] <- [] px al.
        exists (x' :: s1).  exists s2. do ! constructor; try done.
        apply/andP; constructor; [|done]. 
        by rewrite /= pH. 
    + move=> [] [] //=.
      * by move=> [] ? [] [] -> _ [] ->.
      * move=> x'' s' [] s'' [] [] -> H [] px /andP [] /negbTE -> al.
        apply/IH. rewrite -H. exists s'. exists s''.
        by do ! constructor. 
Qed.

Lemma findo_pred  {T : eqType} (p : ssrbool.pred T) (s : seq T) (x : T) :
  (findo p s) = Some x -> p x. 
Proof. 
  by move/esym/eqP/findoP' => [] ? [] ? [] _ []. 
Qed. 

Lemma findo_mem {T : eqType} (p : ssrbool.pred T) (s : seq T) (x : T) :
  Some x = findo p s -> x \in s. 
Proof.
  move/eqP/findoP'=> [] ? [] ? [] <- _.
  by rewrite mem_cat orbC mem_head. 
Qed. 

Definition rfindo {T : Type} (p : ssrbool.pred T) (s : seq T) :=
  findo p (rev s).

Arguments rfindo _/. 

Lemma rfindo_has {T : Type} (p : ssrbool.pred T) (s : seq T) :
  ((rfindo p s) : bool) = has p s.
Proof. by rewrite -has_rev /= findo_has. Qed. 

Lemma rfindoP {T : Type} (p : ssrbool.pred T) (s : seq T) :
  reflect
    (exists s1 s2 x, s1 ++ [:: x] ++ s2 = s /\ p x /\ all (predC p) s2)
    (rfindo p s).
Proof.
  apply/(iffP idP)=> /=. 
  - move/findoP=> [] s1 [] s2 [] x [] /(f_equal rev).
    rewrite revK 2!rev_cat -catA /= => H [] H1 H2.
    exists (rev s2). exists (rev s1). exists x. constructor; try done.
    constructor; try done.
      by rewrite all_rev.
  - move=> [] s1 [] s2 [] x [] <- [] H1 H2.
    rewrite -cat1s 2!rev_cat. apply/findoP. 
    exists (rev s2). exists (rev s1). exists x.
    rewrite catA. do 2! constructor; try done.  
    by rewrite all_rev. 
Qed. 

Lemma sub1:
  forall (a b : nat),a > 0 -> b > 0 -> (a == b) = (a - 1 == b - 1).
Proof. 
  move=> a b. case eq: (_==_)/eqP=> [->|]; first by rewrite eq_refl.
  move: eq. clear. case: a=> //. case: b=> // a' b'/=.
  by rewrite 2!subn1 -(pred_Sn a') -(pred_Sn b').
Qed. 

Definition olast {T : Type} (s : seq T) := if s is x :: _ then Some (last x s) else None. 

Lemma ohead_cat_some {T : Type} (a b : seq T) x :
  ohead a = Some x -> ohead a = ohead (a ++ b). 
Proof. by elim: a. Qed. 

(** ** Suffix 
    As new blocks are appeneded to the left of a chain do we need to
    define suffix rather than prefix. *)

Fixpoint suffix {T : eqType} (s1 s2 : seq T) : bool :=
  (s1 == s2) ||  if s2 is (x :: xs)
                then suffix s1 xs
                else false.


Arguments suffix _ _ !s2 /. 

Lemma suffix_rec {T : eqType} (s1 s2 : seq T) : suffix s1 s2 = (s1 == s2) || suffix s1 s2. 
Proof. by case: s2=> //= [|>]; case: (_==_). Qed. 

Notation "a ⪯ b" := (suffix a b) (at level 20).

Lemma suffix_refl {T : eqType} : reflexive (@suffix T).
Proof. by move=> >; rewrite suffix_rec eq_refl. Qed. 

Lemma suffixP {T : eqType} (s1 s2 : seq T) :
  reflect (exists xs, xs ++ s1 = s2) (s1 ⪯ s2). 
Proof.
  apply/(iffP idP). 
  - elim: s2 => [| x xs IH] //=.
    + by (rewrite orbC /= => /eqP ->; exists [::]). 
    + by move/orP=> [/eqP ->| /IH]; [exists [::]| move=> [] xs' <-; exists (x :: xs')]. 
  - by move=> [] xs <-; elim: xs => /= [| > ->]; [apply/suffix_refl| rewrite orbC].
Qed. 

Lemma suffix_catl {T : eqType} (xs ys : seq T) :  xs ⪯ (ys ++ xs). 
Proof. by apply/suffixP; exists ys. Qed.  

Lemma suffix_catl_F {T : eqType} (xs ys : seq T) :  ys != [::] -> (ys ++ xs) ⪯ xs = false. 
Proof.
  case: ys=> //= y ys _.
  apply/idP. move/suffixP=> [] [] //=.
  - rewrite -cat_cons=> /esym. rewrite -(cat0s xs).
    by move/cat_injl. 
  - move=> x xs'. rewrite -2!cat_cons catA=> /esym. 
    rewrite -(cat0s xs).
      by move/cat_injl. 
Qed. 

Lemma suffix_trans {T : eqType} : transitive (@suffix T).
Proof.
  move=> >. do 2! move/suffixP=> [] ? <-.  
  by rewrite catA; apply/suffix_catl. 
Qed.

Lemma suffix_anti {T : eqType} : antisymmetric (@suffix T).
Proof.
  move=> x y /andP [] /suffixP [] xs <- /suffixP [] ys.
  rewrite -{2}[x]cat0s catA=> /cat_injl.
  by case: ys; case xs.
Qed.

Lemma suffix_nil {T : eqType} (s : seq T) : [::] ⪯ s. 
Proof. by apply/suffixP; exists s; rewrite cats0. Qed. 

(** ** Longest common stem: Abbreviated lcs *)
Fixpoint lcs {T : eqType} (s1 s2 : seq T) : seq T :=
  if s1 ⪯ s2
  then s1
  else if s1 is x :: xs
       then lcs xs s2
       else [::]. 

Lemma lcs_suffix {T : eqType} (s1 s2 : seq T) :
  lcs s1 s2 ⪯ s1 && lcs s1 s2 ⪯ s2.
Proof.
  apply/andP; constructor; last first.
  - elim: s1 => /= [|> IH]; [by rewrite 2!suffix_nil|].
      by case H: ( (_::_) ⪯ _)=> //.
  - elim: s1=> /= [|> IH]; [by case (_ ⪯ _)|]. 
      by case H: ( (_::_) ⪯ _)=> //; [rewrite eq_refl| rewrite IH orbC]. 
Qed. 

Lemma lcsP {T : eqType} (s s1 s2 : seq T) :
  s ⪯ s1 && s ⪯ s2 = s ⪯ lcs s1 s2.
Proof.
  elim: s1 => //=.
  - rewrite suffix_nil orbC /= orbC /=.
    by case: (_==_)/eqP=> [->|] //=; rewrite suffix_nil.
  - move=> x xs /=. 
    move=> IH. 
    case H: ((_::_)⪯_)=> //=. 
    + move: H => /= /suffixP => [] [] ys <-.
      case: (_==_)/eqP=> [->|_] //=.
      * by rewrite suffix_catl.
      * case H: (_⪯_)=> //=. apply/(suffix_trans H).
        by rewrite -cat1s catA suffix_catl. 
    + rewrite -IH. 
      case: (_==_)/eqP=>[->|] //=.
      by rewrite H andbC. 
Qed.     

Lemma lcsC {T : eqType} : commutative (@lcs T). 
Proof.
  move=> >. 
  by apply/suffix_anti/andP; constructor; rewrite -lcsP andbC; apply/lcs_suffix. 
Qed. 

Lemma true1 (a b : bool) : a && b -> a.  
Proof. by case: a. Qed. 

Lemma true2 (a b : bool) : a && b -> b.  
Proof. by case: a. Qed. 

Lemma lcsA {T : eqType} : associative (@lcs T). 
Proof.
  move=> a b c. apply/suffix_anti/andP; constructor. 
  all: rewrite -lcsP; apply/andP; constructor. 
  - rewrite -lcsP; apply/andP; constructor. 
    + by apply/true1/lcs_suffix.
    + apply/(@suffix_trans _ (lcs b c)); [apply/true2/lcs_suffix|].
        by apply/true1/lcs_suffix.
  - apply/(@suffix_trans _ (lcs b c)); [apply/true2/lcs_suffix|]. 
        by apply/true2/lcs_suffix.
  - apply/(@suffix_trans _ (lcs a b)); [apply/true1/lcs_suffix|].
      by apply/true1/lcs_suffix.
  - rewrite -lcsP; apply/andP; constructor. 
    + apply/(@suffix_trans _ (lcs a b)); [apply/true1/lcs_suffix|].
        by apply/true2/lcs_suffix.
    + by apply/true2/lcs_suffix.
Qed. 

Lemma lcsss {T : eqType} : idempotent (@lcs T). 
Proof.
  move=> a. apply/suffix_anti/andP; constructor.
  - by move/andP: (lcs_suffix a a)=> [].
  - by rewrite -lcsP; apply/andP; constructor; apply/suffix_refl.
Qed. 

Lemma filter_filter {T : Type} (p : T -> bool) (s : seq T) :
  [seq x <- [seq x <- s | p x ] | p x] = [seq x <- s | p x ].
Proof.
  elim: s => //= > IH. case peq: p=> //=.  
  by rewrite peq IH. 
Qed. 

Lemma addn_injl n: injective (addn^~ n). 
Proof.
  move=> >; elim: n=> //= [| n IH].
  - by rewrite 2!addn0. 
  - by rewrite 2!addnS; case=> /IH.   
Qed. 

Lemma addn_injr n: injective (addn n). 
Proof.
  move=> >. rewrite addnC=> /esym. rewrite addnC.
  by move/addn_injl ->.
Qed. 

Lemma all_count0 {T: Type} (p : ssrbool.pred T) (s : seq T):
  count p s == 0 = all (predC p) s.
Proof. by elim: s => //= > IH; case: (p _)=> //=. Qed. 

Lemma in_subset1 {T : eqType} (s1 s2 : seq T):
  forall P : (T -> Prop), 
    {subset s1 <= s2} ->
    {in s2, forall x, P x} -> 
    {in s1, forall x, P x}. 
Proof. by move=> P sub H=> ? /sub/H. Qed. 

Lemma in_subset2 {T : eqType} (s1 s2 : seq T):
  forall P : (T -> T -> Prop), 
    {subset s1 <= s2} ->
    {in s2 &, forall x y, P x y} -> 
    {in s1 &, forall x y, P x y}. 
Proof. by move=> P sub H=> ?? /sub/H H' /sub /H'. Qed. 

Lemma perm_rem {T : eqType} (x : T) (s1 s2 : seq T) :
  perm_eq s1 s2 -> perm_eq (rem x s1) (rem x s2).
Proof.
  case xin: (x \in s1)=> perm. 
  - rewrite -(perm_cons x). apply/perm_trans.
    + by rewrite perm_sym; apply/(perm_to_rem xin).
    + by apply/(perm_trans perm)/perm_to_rem; rewrite -(perm_mem perm). 
  - rewrite rem_id; [rewrite rem_id //|].
    rewrite -(perm_mem perm).
    all: by rewrite xin. 
Qed. 

Lemma ltn_leq_trans n m p : m < n -> n <= p -> m < p. 
Proof. by move=> ?; apply: leq_trans. Qed.

Lemma instant1 (A B C : Type): A -> (B -> C) -> ((A -> B ) -> C).
Proof. by move=> a + /(_ a). Qed. 

Lemma instant2 (A B C D : Type):
  A -> B -> (C -> D) -> ((A -> B -> C ) -> D).
Proof. by move=> a b + /(_ a b). Qed. 

Lemma instant3 (A B C D E : Type):
  A -> B -> C -> (D -> E) -> ((A -> B -> C -> D ) -> E).
Proof. by move=> a b c + /(_ a b c). Qed. 

Lemma instant4 (A B C D E F : Type):
  A -> B -> C -> D -> (E -> F) -> ((A -> B -> C -> D -> E ) -> F).
Proof. by move=> a b c d + /(_ a b c d). Qed. 

Lemma instant5 (A B C D E F G : Type):
  A -> B -> C -> D -> E -> (F -> G) -> ((A -> B -> C -> D -> E -> F ) -> G).
Proof. by move=> a b c d e + /(_ a b c d e). Qed. 

Lemma instant6 (A B C D E F G H : Type):
  A -> B -> C -> D -> E -> F -> (G -> H) -> ((A -> B -> C -> D -> E -> F -> G ) -> H).
Proof. by move=> a b c d e f + /(_ a b c d e f). Qed. 

Lemma instant7 (A B C D E F G H I : Type):
  A -> B -> C -> D -> E -> F -> G -> (H -> I) -> ((A -> B -> C -> D -> E -> F -> G -> H ) -> I).
Proof. by move=> a b c d e f h + /(_ a b c d e f h). Qed. 



