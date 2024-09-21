(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 3 *)

Require Import Frap.Frap ZArith.
Require Import Pset3.Pset3Sig.

Module Impl.
  (* In this pset, we will practice two topics:
     1) Polymorphic container types, i.e. types parametrized by types,
        such as "option A", "list A", "tree A", and finally, "bitwise_trie A",
        which combines option and tree to obtain a new useful data structure.
     2) Higher-order functions (HOFs), i.e. functions that take other functions
        as arguments.

     Once again we have posted some general tips for advancing in this lab near
     the bottom of the signature file under "TIPS". Below the tips are a set of
     problem-specific, spoiler hints that will help you with these problems. Try
     only to consult these if you get stuck!
  *)

  (* As usual, the grading rubric for this pset is in Pset3Sig.v. *)

  (** ** Higher-order functions **)

  (* In class, we talked about a few useful functions at the blackboard
   * level of detail, and here is how we can define one of them in Coq.
   * It's the identity function [id], which just returns its argument
   * without modification: *)
  Definition id {A : Type} (x : A) : A := x.

  (* We also saw [compose], another higher-order function: [compose g f]
   * applies [f] to its input and then applies [g]. Argument order
   * follows the general convention of functional composition in
   * mathematics denoted by the small circle.
   *)
  Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

  (* Let's use a small circle to refer to [compose]. This will make our
     goals much more readable.
     It's up to you to decide whether you also want to use the circle notation
     in your definitions or whether you prefer to write "compose".

     Users of Emacs with company-coq can simply type \circ RET
     to insert ∘. *)
  Notation " g ∘ f " := (compose g f) (at level 40, left associativity).

  (* Here are three simple properties of function composition.
     Together, these properties mean that functions with ∘ form
     a "monoid". *)

  (* Hint: In the following, it might be helpful to use the following fact:
     If two functions return the same value for all inputs, they are the same. *)
  Check @FunctionalExtensionality.functional_extensionality.
  (* Aside: We called it a "fact" above, but logicians disagree about whether
     we should believe this or not -- one philosophical question is
     that even if merge sort and bubble sort return the same result for
     all inputs, they are two different things.
     Therefore, this "fact" is not actually built into Coq's kernel, but it's
     an axiom written down in the standard library, and if you believe in it,
     you can import it (the Frap library already does so).
     In any case, it is consistent with the rest of Coq's logic, i.e. by
     assuming this axiom, you will not be able to prove False, so we're safe.*)

  (* Let's make a shorthand for this: *)
  Definition fun_ext := @FunctionalExtensionality.functional_extensionality.

  Lemma compose_id_l : forall A B (f: A -> B),
      id ∘ f = f.
  Proof.
      intros.
      apply fun_ext.
      unfold compose.
      intros x.
      unfold id.
      equality.
  Qed.

  Lemma compose_id_r : forall A B (f: A -> B),
      f ∘ id = f.
  Proof.
      intros.
      apply fun_ext.
      unfold compose.
      intro x.
      unfold id.
      equality.
   Qed.


  Lemma compose_assoc : forall A B C D (f: A -> B) (g: B -> C) (h: C -> D),
      h ∘ (g ∘ f) = h ∘ g ∘ f.
  Proof.
      intros.
      apply fun_ext.
      unfold compose.
      intros x.
      equality.
   Qed.

  (* The selfCompose function takes a function and applies this function n times
     to the argument. There are different ways of defining it, but let's
     define it using only [id] and [compose]. *)
  Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
    match n with
    | O => id
    | S n' => f ∘ (selfCompose f n')
    end.

  (* Here's an example of what [selfCompose] can do:
     If we apply the function that adds 2 to its argument 7 times to the starting
     value 3, we obtain 3 + 7 * 2 = 17. *)
  Example selfCompose_plus1: selfCompose (plus 2) 7 3 = 17. Proof. equality. Qed.

  (* We can also use [selfCompose] to define exponentiation on natural numbers, by
     saying "to raise [base] to the power [e], apply the function that multiplies
     its argument by [base] to [1] [e] times".
     Define [exp] using [selfCompose] and [Nat.mul]. *)
  Definition exp(base e: nat): nat := 
      selfCompose (Nat.mul base) e 1.

  (* Once you define [exp], you can replace [Admitted.] below by [Proof. equality. Qed.] *)
  Lemma test_exp_2_3: exp 2 3 = 8. Proof. equality. Qed.
  Lemma test_exp_3_2: exp 3 2 = 9. Proof. equality. Qed.
  Lemma test_exp_4_1: exp 4 1 = 4. Proof. equality. Qed.
  Lemma test_exp_5_0: exp 5 0 = 1. Proof. equality. Qed.
  Lemma test_exp_1_3: exp 1 3 = 1. Proof. equality. Qed.

  (* And here's another example to illustrate [selfCompose]. Make sure you understand
     why its result is 256. *)
  Example selfCompose_square: selfCompose (fun (x: nat) => x * x) 3 2 = 256. Proof. equality. Qed.

  (** ** Inverse functions **)

  (* Using [compose] and [id], we can write a concise definition of when
     a function [g] is the left inverse of a function [f]: *)
  Definition left_inverse{A B: Type}(f: A -> B)(g: B -> A): Prop := g ∘ f = id.

  (* Here's an example: The function that subtracts two from its argument
     is the left inverse of the function that adds two to its argument. *)
  Example plus2minus2: left_inverse (fun (x: nat) => x + 2) (fun (x: nat) => x - 2).
  Proof.
    unfold left_inverse.
    unfold compose.
    Search (_ + ?x - ?x).
    unfold id.
    apply fun_ext.
    intros x.
    rewrite Nat.add_sub.
    equality.
  Qed.

  (* On the other hand, note that the other direction does not hold, because
     if a subtraction on natural numbers underflows, it just returns 0, so
     there are several [x] for which [x-2] returns 0 (namely 0, 1, and 2),
     so it can't have a left inverse. *)
  Example minus2plus2: ~ left_inverse (fun (x: nat) => x - 2) (fun (x: nat) => x + 2).
  Proof.
    unfold left_inverse.
    intros H.
    assert (H0: ((fun x => x+2) ∘ (fun x => x- 2)) 0 = id 0).
    {
     rewrite H. equality.
    }
    unfold compose in H0.
    unfold id in H0.
    Search (0 - _).
    rewrite Nat.sub_0_l in H0.
    simpl in H0.
    discriminate H0.
  Qed.


  (* Let us make the intuition from the previous paragraph more
     concrete, by proving that a function that is not injective
     cannot have a left inverse; or, in other words, that
     functions with left inverses are injective. *)

  (* HINT 1 (see Pset3Sig.v) *)
  Lemma left_invertible_injective {A}:
    forall (f g: A -> A),
      left_inverse f g ->
      (forall x y, f x = f y -> x = y).
  Proof.
    intros f g H x y Hfxfy.
    unfold left_inverse in H.
    assert (H1: g (f x) = g (f y)).
    {
      rewrite Hfxfy. equality.
    }

   assert (H2: (g ∘ f) x = (g ∘ f) y).
   {
     unfold compose. 
     assumption.
   }

   rewrite H in H2.
   unfold id in H2.
   assumption.
  Qed.

  (* Bonus question (no points): can you prove the reverse;
     i.e., can you prove that all injective functions have left
     inverses? *)

  (* The identity function is the inverse of itself.
     Note: we're using "@" in front of "id" to say "we want to provide all implicit
     type arguments explicitly, because otherwise Coq would not be able to infer them." *)
  Lemma left_inverse_id: forall A, left_inverse (@id A) (@id A).
  Proof.
    intros.
    unfold left_inverse.
    unfold compose.
    unfold id.
    equality.
  Qed.


  (* Now we can start proving interesting facts about inverse functions: *)
  (* Here's how to invert the power function: *)
  (* HINT 2 (see Pset3Sig.v) *)  
  Lemma invert_selfCompose{A: Type}: forall (f g: A -> A) (n: nat),
      left_inverse f g ->
      left_inverse (selfCompose f n) (selfCompose g n).
  Proof.
    unfold left_inverse.
    induct n.
    - simplify. apply left_inverse_id.
    - simplify.
 
    assert (Hg: forall n': nat, g ∘ selfCompose g n' = selfCompose g n' ∘ g).
    {
      induct n'.
      - simplify.
        rewrite compose_id_l.
        rewrite compose_id_r.
        equality.
      - simplify.
        rewrite IHn' at 1.
        auto.
    }

    rewrite Hg.
    Search ( _∘ _ ∘ _).
    rewrite compose_assoc. 
    rewrite <- compose_assoc with (h := selfCompose g n).
    rewrite H.
    rewrite compose_id_r.
    apply IHn.
    assumption.
  Qed.
  

  (** ** Polymorphic container types *)

  (* First, we'll reproduce some definitions we need from Lecture 2,
     [tree] and [flatten]: *)

  Inductive tree {A} :=
  | Leaf
  | Node (l : tree) (d : A) (r : tree).
  Arguments tree : clear implicits.

  Fixpoint flatten {A} (t : tree A) : list A :=
    match t with
    | Leaf => []
    | Node l d r => flatten l ++ d :: flatten r
    end.

  (* Bitwise tries are finite maps keyed by lists of Booleans.
   * We will implement a bitwise trie with entries of type [A]
   * by [tree (option A)]. The value at the root of the tree
   * corresponds to the entry for the key [nil : list bool],
   * the left subtree contains entries for those keys that
   * begin with [true], and the right subtree contains entries
   * for those keys that begin with [false].
   *
   * Tries are a common and powerful data structure; you can read
   * more about them at https://en.wikipedia.org/wiki/Trie .
   *)
  Definition bitwise_trie A := tree (option A).

  (* Define [lookup] such that [lookup k t] looks up the
   * map entry corresponding to the key [k : list bool] in the
   * bitwise trie [t : bitwise_trie A].
   *
   * Look at the examples below to get a better sense of what
   * this operation does: the argument [k] is a path, in which
   * [true] means "go left" and [false] means "go right".
   *)
  Fixpoint lookup {A} (k : list bool) (t : bitwise_trie A) {struct t} : option A :=
    match t, k with
    | Leaf, [] => None
    | Leaf, _ => None
    | Node l None r, [] => None
    | Node l (Some v) r, [] => Some v
    | Node l _ r, true::k' =>  lookup k' l
    | Node l _ r, false::k' => lookup k' r
    end.

  Example lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.
  Proof.
    simplify. equality.
  Qed.

  Example lookup_example2 : lookup [false; true]
      (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
                            = Some 1.
  Proof.
    simplify. equality.
  Qed.

  (* [Leaf] represents an empty bitwise trie, so a lookup for
   * any key should return [None].
   *)
  Theorem lookup_empty {A} (k : list bool)
    : lookup k (Leaf : bitwise_trie A) = None.
  Proof.
    simplify.
    case k.
    - equality.
    - equality.
  Qed.   

  (* HINT 3 (see Pset3Sig.v) *)

  (* Define an operation to "insert" a key and optional value
   * into a bitwise trie. The [insert] definition should satisfy two
   * properties: one is [lookup_insert] below, which says that if we
   * look up a key [k] in a trie where [(k, v)] has just been inserted,
   * the result should be [v]. The other is that lookups on keys different
   * from the one just inserted should be the same as on the original map.
   *
   * If an entry for that key already exists, [insert] should replace
   * that entry with the new one being inserted. Note that [insert] can
   * be used to remove an entry from the trie, too, by inserting [None]
   * as the value.
   *
   * Hint: it may be helpful to define an auxiliary function
   * that creates a singleton tree (a tree containing a single
   * key-value pair).
   *)
  Fixpoint build_singleton {A} (k : list bool) (v : option A) : bitwise_trie A :=
     match k with
     | [] => Node Leaf v Leaf
     | x :: k' => let branch := build_singleton k' v in
                  if x then Node branch None Leaf
                  else Node Leaf None branch
     end.

  Fixpoint insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) {struct t}
    : bitwise_trie A :=
    match t with
    | Leaf => build_singleton k v
    | Node l old_v r =>
      match k with
      | [] => Node l v r
      | x :: k' => if x then Node (insert k' v l) old_v r
                   else Node l old_v (insert k' v r)
      end
    end.

  Example insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
  Proof.
    simplify. equality.
  Qed.

  Example insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
  Proof.
    simplify. equality.
  Qed.

  Theorem lookup_insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) :
    lookup k (insert k v t) = v.
  Proof.
    generalize dependent v.
    generalize dependent k.
    induct t.
    - (* Case: t is Leaf *)
      simplify. induct k.
      + (* Case: k is [] *)
        simplify. 
        case v; equality.
      + (* Case: k is x::k' *)  
        simplify. case a; simplify.
        * apply IHk.
        * apply IHk.
    - (* Case: t is Node *)
      simplify. case k. 
      + (* Case: k is [] *)
        simplify.
        case v; equality.
      + (* Case: k is x::k' *)
        intros. case b.
        * simplify.
          case d; simplify.
            apply IHt1.
            apply IHt1.
        * simplify.
          case d; simplify.
            apply IHt2.
            apply IHt2.
  Qed.



  (* Define an operation to "merge" that takes two bitwise tries and merges
   * them together. The [merge] definition should combine two bitwise tries, 
   * preferring map entries from the first bitwise trie when an entry exists 
   * for both bitwise tries.
   *
   * The [merge] definition should satisfy three properties: one is 
   * [left_lookup_merge], which says that if a trie contains an entry [v] for a
   * key [k], then when this trie is the first trie in a merge with any other 
   * trie, then the resulting merged trie also contains an entry [v] for key [k].
   * The other, [lookup_merge_None], says that if the merge of two tries 
   * contains no entry for a given key [k], then neither did the two original
   * tries. The final is [merge_selfCompose], which says that if you repeatedly
   * merge one trie with another one or more times, it is the same as merging
   * the tries once.
   *)
  
  Fixpoint merge {A} (t1 t2 : bitwise_trie A) : bitwise_trie A :=
    match t1, t2 with
    | Leaf, Leaf => Leaf
    | Leaf, Node l v r => Node l v r
    | Node l v r, Leaf => Node l v r
    | Node l1 v1 r1, Node l2 None r2 =>
        Node (merge l1 l2) v1 (merge r1 r2)
    | Node l1 None r1, Node l2 v2 r2 =>
        Node (merge l1 l2) v2 (merge r1 r2)
    | Node l1 v1 r1, Node l2 v2 r2 =>
        Node (merge l1 l2) v1 (merge r1 r2)
    end.
  

  Lemma merge_example1 :
    merge (Node Leaf (Some 1) Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 1) Leaf.
  Proof.
    simplify. equality.
  Qed.

  Lemma merge_example2 :
    merge Leaf (Node Leaf (@None nat) Leaf) = Node Leaf None Leaf.
  Proof.
    simplify. equality.
  Qed.
  Lemma merge_example3 :
    merge (Node Leaf None Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 2) Leaf.
  Proof.
    simplify. equality.
  Qed.
    
  Theorem left_lookup_merge {A} : forall (t1 t2 : bitwise_trie A) k v,
      lookup k t1 = Some v ->
      lookup k (merge t1 t2) = Some v.
  Proof.
    intros.
    generalize dependent t1.
    generalize dependent k.
    induction t2 as [ | l2 IHl2 v2 r2 IHr2]. 
    - (* Case: t2 is Leaf *) 
      intros.
      destruct t1 as [ | l1 v1 r1].
      + rewrite lookup_empty in H. discriminate H.
      + simpl. destruct v1.
        * assumption.
        * assumption.
    - (* Case: t2 is Node l2 v2 r2 *)
      intros.
      destruct t1 as [ | l1 v1 r1].
      + rewrite lookup_empty in H. discriminate H.
      + simpl.
        destruct v1.
        * destruct v2.
          { (*Case v1 is Some a, v2 is Some a *) 
            destruct k.
            * simpl. simpl in H. assumption.
            * destruct b.
              + simpl. simpl in H.
                apply IHl2.
                assumption.
              + simpl. simpl in H.
                apply IHr2.
                assumption.
          }
          { (*Case v1 is Some a, v2 is None *)
            destruct k.
            * simpl. simpl in H. assumption.
            * destruct b.
              + simpl. simpl in H.
                apply IHl2.
                assumption.
              + simpl. simpl in H.
                apply IHr2.
                assumption. 
          }
        * destruct v2.
          { (*Case v1 is None, v2 is Some a *)
            destruct k.
            * simpl in H. discriminate H.
            * destruct b.
              + simpl. simpl in H.
                apply IHl2.
                assumption.
              + simpl. simpl in H.
                apply IHr2.
                assumption. 
          }
          { (*Case v1 is None, v2 is None *)
            destruct k.
            * simpl in H. discriminate H.
            * destruct b.
              + simpl. simpl in H.
                apply IHl2.
                assumption.
              + simpl. simpl in H.
                apply IHr2.
                assumption.
          }
    Qed.

  Theorem lookup_merge_None {A} : forall (t1 t2 : bitwise_trie A) k,
      lookup k (merge t1 t2) = None ->
      lookup k t1 = None /\ lookup k t2 = None.
  Proof.
    intros t1 t2 k H.
    generalize dependent t2.
    generalize dependent k.
    induction t1 as [| l1 IHl1 v1 r1 IHr1]; intros k t2 H.
    - (* Case: t1 is Leaf *)
      simpl in H.
      split.
      + (* Subcase: lookup k t1 = None *)
        rewrite lookup_empty. reflexivity.
      + (* Subcase: lookup k t2 = None *)
        destruct t2; simpl in H; assumption.
    - (* Case: t1 is Node l1 v1 r1 *)
      destruct t2 as [| l2 v2 r2].
      + (* Subcase: t2 is Leaf *)
        split.
        * (* Subcase: lookup k t1 = None *)
          simpl in H; destruct v1; assumption.
        * (* Subcase: lookup k t2 = None *)
          rewrite lookup_empty. reflexivity.
      + (* Subcase: t2 is Node l2 v2 r2 *)
        destruct k as [| b k'].
        * (* Subcase: k is [] *)
          destruct v1; destruct v2; simpl in H; try discriminate.
          split; reflexivity.
        * (* Subcase: k is b :: k' *)
          destruct b.
          -- (* Subcase: b is true *)
            simpl. simpl in H. destruct v1; destruct v2.
            ++ apply IHl1 in H.
               assumption.
            ++ apply IHl1 in H.
               assumption.
            ++ apply IHl1 in H.
               assumption.
            ++ apply IHl1 in H.
               assumption.
          -- (* Subcase: b is false *)
            simpl. simpl in H. destruct v1; destruct v2.
            ++ apply IHr1 in H.
               assumption.
            ++ apply IHr1 in H.
               assumption.
            ++ apply IHr1 in H.
               assumption.
            ++ apply IHr1 in H.
               assumption.
  Qed.

  (* HINT 5 (see Pset3Sig.v) *)
  Lemma merge_id {A} : forall (t1 : bitwise_trie A),
    merge t1 t1 = t1.
  Proof.
    intros t1.
    induction t1 as [ | l1 IHl1 v1 r1 IHr1].
    - (* Case: t1 is Leaf *)
      reflexivity.
    - (* Case: t1 is Node l1 v1 r1 *)
      simpl. destruct v1.
      + rewrite IHl1. rewrite IHr1. reflexivity.
      + rewrite IHl1. rewrite IHr1. reflexivity.
  Qed.

  Lemma merge_idempotent {A} : forall (t1 t2 : bitwise_trie A),
    merge t1 (merge t1 t2) = merge t1 t2.
  Proof.
    intros t1 t2.
    generalize dependent t1.
    induction t2 as [ | l2 IHl2 v2 r2 IHr2].
    - (* Case: t2 is Leaf *)
      intros. destruct t1.
      + simpl. reflexivity.
      + simpl. destruct d.
        * rewrite merge_id. rewrite merge_id. reflexivity.
        * rewrite merge_id. rewrite merge_id. reflexivity.
    - (* Case: t2 is Node l2 v2 r2 *)
      intros. simpl. destruct t1 as [ | l1 v1 r1].
      + simpl. reflexivity.
      + simpl. destruct v1.
        * destruct v2.
          { rewrite IHl2. rewrite IHr2. reflexivity. }
          { rewrite IHl2. rewrite IHr2. reflexivity. }
        * destruct v2.
          { rewrite IHl2. rewrite IHr2. reflexivity. }
          { rewrite IHl2. rewrite IHr2. reflexivity. }
  Qed.

  Theorem merge_selfCompose {A} : forall n (t1 t2 : bitwise_trie A),
      0 < n ->
      selfCompose (merge t1) n t2 = merge t1 t2.
  Proof.
    intros n t1 t2 H.
    induction n as [| n' IH].
    - (* Base case: n = 0 *)
      exfalso. (* This case is impossible because 0 < n *)
      inversion H.
    - (* Inductive case: n = S n' *)
      simpl.
      destruct n'.
      + (* Case: n' = 0 *)
        simpl. reflexivity.
      + (* Case: n' > 0 *)
        intros. simpl. simpl in IH.
        unfold compose.
        unfold compose in IH.
        rewrite IH.
        * rewrite merge_idempotent.
          reflexivity.
        * linear_arithmetic.
  Qed.

  (* Define an operation to "mirror" that takes a tree (not necessarily a 
   * trie) and returns the mirrored version of the tree.
   *
   * The [mirror] definition should satisfy two properties: one is 
   * [mirror_mirror_id], which says that if you mirror a tree twice, it
   * results in the original tree. The other is [flatten_mirror_rev] which
   * states that flattening a mirrored tree is equivalent to reversing the
   * list resulting from the flattening of that same tree.
 *)
  
  Fixpoint mirror {A} (t : tree A) : tree A :=
    match t with
    | Leaf => Leaf
    | Node l d r => Node (mirror r) d (mirror l)
    end.     

  Example mirror_test1 :
    mirror (Node Leaf 1 (Node Leaf 2 (Node Leaf 3 Leaf))) =
    Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf.
  Proof.
    simplify. equality.
  Qed.
  
  Theorem mirror_mirror_id {A} : forall (t : tree A),
      mirror (mirror t) = t.
  Proof.
    intros t.
    induction t as [ | l IHl d r IHr].
    - (* Case: t is Leaf *)
      reflexivity.
    - (* Case: t is Node l d r *)
      simpl. rewrite IHl. rewrite IHr. reflexivity.
  Qed.
  
  Theorem flatten_mirror_rev {A} : forall (t : tree A),
      flatten (mirror t) = rev (flatten t).
  Proof.
    intros t.
    induction t as [ | l IHl d r IHr].
    - (* Case: t is Leaf *)
      reflexivity.
    - (* Case: t is Node l d r *)
      simpl. rewrite IHl. rewrite IHr.
      rewrite rev_app_distr.
      simpl.
      rewrite <- app_assoc.
      reflexivity.
  Qed.

  (** ** HOFs on lists and trees **)
  
  (* Just like we defined [map] for lists, we can similarly define
   * a higher-order function [tree_map] that applies a function on
   * elements to all of the elements in the tree, leaving the tree
   * structure intact.
   *)
  Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
    : tree B :=
    match t with
    | Leaf => Leaf
    | Node l d r => Node (tree_map f l) (f d) (tree_map f r)
    end.

  Example tree_map_example :
    tree_map (fun x => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf)))
    = (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).
  Proof.
    simplify. equality.
  Qed.

  (* [tree_map_flatten] shows that [map]
   * and [tree_map] are related by the [flatten] function.
   *)
  (* HINT 6 (see Pset3Sig.v) *)
  Theorem tree_map_flatten : forall {A B : Type} (f : A -> B) (t : tree A),
      flatten (tree_map f t) = map f (flatten t).
  Proof.
    intros A B f t.
    induction t as [ | l IHl d r IHr].
    - (* Case: t is Leaf *)
      reflexivity.
    - (* Case: t is Node l d r *)
      simpl. rewrite IHl. rewrite IHr.
      rewrite map_app. reflexivity.
  Qed.

  (* This function asserts that a predicate holds over all
     elements of a tree. *)
  Fixpoint tree_forall {A} (P: A -> Prop) (tr: tree A) :=
    match tr with
    | Leaf => True
    | Node l d r => tree_forall P l /\ P d /\ tree_forall P r
    end.

  (* Define a similar function for the [exists] case; that is, define
     a function that asserts that a predicate holds for at least
     one value of a tree. *)
  Fixpoint tree_exists {A} (P: A -> Prop) (tr: tree A) {struct tr} : Prop :=
    match tr with
    | Leaf => False
    | Node l d r => tree_exists P l \/ P d \/ tree_exists P r
    end.

  (* Two sanity checks for your function: *)
  Lemma tree_exists_Leaf {A} (P: A -> Prop):
    ~ tree_exists P Leaf.
  Proof.
    simplify. auto.
  Qed.

  Lemma tree_forall_exists {A} (P: A -> Prop):
    forall tr, tr <> Leaf -> tree_forall P tr -> tree_exists P tr.
  Proof.
    intros tr H H0.
    destruct tr as [ | l d r].
    - exfalso. apply H. reflexivity.
    - simpl. destruct l as [ | l' d' r'].
      + simpl in H0. inversion H0. inversion H2.
        right. left. assumption.
      + simpl in H0. inversion H0. inversion H2.
        right. left. assumption.
  Qed.

  (* What does the following theorem mean? Write a short
     explanation below. *)


  Lemma tree_forall_sound {A} (P: A -> Prop):
    forall tr, tree_forall P tr ->
          forall d, tree_exists (fun d' => d' = d) tr ->
               P d.
  Proof.
    intros tr H_forall d H_exists.
    induction tr as [ | l IHl d' r IHr].
    - (* Base Case: Leaf *)
      simpl in H_exists.
      contradiction.
    - (* Inductive Case: Node *)
      simpl in H_exists.
      destruct H_forall as [H_l [H_d' H_r]].
      destruct H_exists as [H_el | [H_ed | H_er]].
      + (* Case: d exists in the left subtree *)
        apply IHl.
        * apply H_l.
        * exact H_el.
      + (* Case: d is the current node's data *)
        subst.
        exact H_d'.
      + (* Case: d exists in the right subtree *)
        apply IHr.
        * apply H_r.
        * exact H_er.
  Qed.

  (** ** Binary search trees **)

  (* Like tries, binary search trees (BSTs) are a popular way to
     store structured data.  We will use them to implement a set
     data type, with methods to insert a new element, remove an
     existing element, and check whether the set contains a
     given element.

     Proving a complete BST implementation in a week is a bit
     too much at this point in the term, so we will start this
     week with definitions and correctness proofs for membership
     tests. *)

  (* BSTs will allow us to illustrate an important idea: data
     abstraction, the general principle that data structures
     should expose interfaces that abstract over (i.e., hide)
     the complexities of their internal representation.  Data
     abstraction is a key ingredient of modularity in most
     programming languages.  (We have a lecure on it coming in
     a week.)

     Concretely, this means that client code using our set
     library built with BSTs shouldn't have to think about
     binary trees at all: instead, we'll write all specs in
     terms of abstract sets, representing a set of values of
     type [A] using the type [A -> Prop].
   *)


  (* This makes our numeric notations refer to integers instead of nats.
     We use integers in this assignment since they'll work more nicely
     with monotonicity later. Don't worry, [linear_arithmetic] can handle
     integers as well as nats.
   *)
  Local Open Scope Z_scope.
  Check 1.

  Fixpoint bst (tr : tree Z) (s : Z -> Prop) :=
    match tr with
    | Leaf => forall x, ~ (s x) (* s is empty set *)
    | Node l d r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
    end.

  (* First, let's get familiar with this definition by proving
     that [bst tr s] implies that all elements of [tr] have
     property [s].  Recall that you may need to prove a stronger
     lemma than the one we show here. *)

  (* If you want to apply a lemma that binds terms that don't appear
     in the goal, Coq can't infer what those terms should be. You
     may need to give them explicitly when you apply the lemma.
     A potentially helpful tip: you can use the `apply` tactic like so:

                   apply <theorem name> with (<x>:=<term>)

     where <x> is a forall-bound name in theorem statement you're
     trying to apply and <term> is what you what to fill in for <x>.
   *)
  

  (* HINT 7 (see Pset3Sig.v) *)
  Lemma tree_forall_implies:
  forall tr (P Q: Z -> Prop),
    tree_forall P tr ->
    (forall x, P x -> Q x) ->
    tree_forall Q tr.
  Proof.
    intros tr P Q H_forall H_implies.
    induction tr as [ | l IHl d r IHr].
    - (* Case: tr is Leaf *)
      simpl. linear_arithmetic.
    - (* Case: tr is Node l d r *)
      simpl.
      split.
      + apply IHl. apply H_forall.
      + split.
        * apply H_implies. apply H_forall.
        * apply IHr. apply H_forall.
  Qed.

  Lemma bst_implies:
    forall tr s, bst tr s -> tree_forall s tr.
  Proof.
    intros tr.
    induction tr as [ | l IHl d r IHr].
    - (* Case: Leaf *)
      simpl. constructor.
    - (* Case: Node l d r *)
      simpl.
      intros s H.
      destruct H as [H_d [H_l H_r]].
      split.
      + (* Prove tree_forall s l *)
          apply tree_forall_implies with (P := fun x => s x /\ x < d).
          -- apply IHl. apply H_l.
          -- intros x [s_x _]. assumption.
      + split.
        * (* Prove s d *)
          assumption.
        * (* Prove tree_forall s r *)
          apply tree_forall_implies with (P := fun x => s x /\ d < x).
          -- apply IHr. apply H_r.
          -- intros x [s_x _]. assumption.
  Qed.

  (* Next, let's prove that elements of the left subtree of a
     BST node are less than the node's data and that all
     elements of the right subtree are greater than it.  This
     should be a consequence of the lemma you proved for
     [bst_implies]; our solution does not use induction here. *)

  Lemma bst_node_ordered :
    forall l d r s,
      bst (Node l d r) s ->
      tree_forall (fun x => x < d) l /\ tree_forall (fun x => d < x) r.
  Proof.
    intros l d r s H.
    split.
    - apply tree_forall_implies with (P := fun x => s x /\ x < d).
      + apply bst_implies with (s := fun x => s x /\ x < d).
        apply H.
      + intros x [s_x x_l].
        assumption.
    - apply tree_forall_implies with (P := fun x => s x /\ d < x).
      + apply bst_implies with (s := fun x => s x /\ d < x).
        apply H.
      + intros x [s_x d_x].
        assumption.
  Qed.


  (* Here is another convenient property: if two sets are the
     same, then a bst representing one also represents the
     other.  Hint: [rewrite] and related tactics can be used
     with logical equivalence, not just equality! *)

  Lemma bst_iff : forall tr P Q,
      bst tr P ->
      (forall x, P x <-> Q x) ->
      bst tr Q.
  Proof.
    intros tr.
    induction tr as [ | l IHl d r IHr].
    - (* Case: Leaf *)
      intros P Q H_bst H_iff.
      simpl.
      intros x H_x.
      specialize (H_iff x).
      apply H_iff in H_x.
      simpl in H_bst.
      specialize (H_bst x).
      contradiction.
    - (* Case: Node l d r *)
      simpl in *.
      intros P Q H_bst H_iff.
      destruct H_bst as [H_d [H_l H_r]].
      split.
      + apply H_iff.
        apply H_d.
      + split.
        * apply IHl with (P := fun x => P x /\ x < d).
          -- assumption.
          -- intros x.
             split; intros [HP Hx]; split.
             { apply H_iff. assumption. }
             { assumption. }
             { apply H_iff. assumption. }
             { assumption. }
        * apply IHr with (P := fun x => P x /\ d < x).
          -- assumption.
          -- intros x.
             split; intros [HP Hx]; split.
             { apply H_iff. assumption. }
             { assumption. }
             { apply H_iff. assumption. }
             { assumption. }
  Qed.

  (* Let's prove something about the way we can map over binary search
     trees while preserving the bst structure. In order to preserve the
     ordered structure of the data in a BST, the function that is mapped over
     must be strictly monotonically increasing. This means that if "f" is a
     strictly monotone-increasing function, and x and y are numbers where
     x is less than y, then f x must also be less than f y.

     The resulting predicate of the mapped tree is then recharacterized as
     a property that holds for all and only the mapped values of the 
     original tree.
     *)

  Theorem bst_strict_monotone_increasing : forall tr P Q f g,
      bst tr P ->
      left_inverse g f ->
      (forall x y, x < y <-> f x < f y) ->
      (forall x, P x <-> Q (f x)) ->
      bst (tree_map f tr) Q.
  Proof.
    intros tr.
    induction tr as [ | l IHl d r IHr].
    - (* Case: Leaf *)
      intros P Q f g H_bst H_left_inverse H_strict_mono H_iff.
      simpl.
      constructor.
    - (* Case: Node l d r *)
      simpl.
      constructor.
      + (* Prove that f d is the root of the mapped tree *)
        apply H_iff.
        apply H_bst.
      + (* Prove that the left subtree is a BST *)
        apply IHl.
        * (* Prove that the left subtree is a BST *)
          apply H_bst.
        * (* Prove left inverse *)
          apply H_left_inverse.
        * (* Prove strict monotonicity *)
          apply H_strict_mono.
        * (* Prove the equivalence of predicates *)
          apply H_iff.
      + (* Prove that the right subtree is a BST *)
        apply IHr.
        * (* Prove that the right subtree is a BST *)
          apply H_bst.
        * (* Prove left inverse *)
          apply H_left_inverse.
        * (* Prove strict monotonicity *)
          apply H_strict_mono.
        * (* Prove the equivalence of predicates *)
          apply H_iff.
  Qed.
  Admitted.

  (* Monotone functions can be characterized as monotone increasing or 
     monotone decreasing. In the case of a strictly monotonically decreasing
     function we have the property that for a function f, if x is less than y
     then f y is less than f x.

     Let's prove the result of mapping a strictly monotonically decreasing
     function over a binary search tree. This will be similar to the mapping
     a strictly monotone-increasing function over a tree, only now to preserve
     the ordered property the resulting tree must be mirrored.
     *)
  
  Theorem bst_strict_monotone_decreasing_mirror : forall tr P Q f g,
      bst tr P ->
      left_inverse g f ->
      (forall x y, x < y <-> f x > f y) ->
      (forall x, P x <-> Q (f x)) ->
      bst (mirror (tree_map f tr)) Q.
  Proof.
  Admitted.
  
  (* [member] computes whether [a] is in [tr], but to do so it *relies* on the
     [bst] property -- if [tr] is not a valid binary search tree, [member]
     will (and should, for performance) give arbitrarily incorrect answers. *)

  Fixpoint bst_member (a: Z) (tr: tree Z) : bool :=
    match tr with
    | Leaf => false
    | Node lt v rt =>
      match compare a v with
      | Lt => bst_member a lt
      | Eq => true
      | Gt => bst_member a rt
      end
    end.

  Lemma member_bst : forall tr s a,
      bst tr s -> bst_member a tr = true <-> s a.
  Proof.
  Admitted.

  (* Next week, we will look at insertion and deletion in
     BSTs. *)

  Local Close Scope Z_scope.

  (** ****** Optional exercises ****** *)

  (* Everything below this line is optional! *)

  (* You've reached the end of the problem set. Congrats!
   *
   * [fold] is a higher-order function that is even more general
   * than [map]. In essence, [fold f z] takes as input a list
   * and produces a term where the [cons] constructor is
   * replaced by [f] and the [nil] constructor is replaced
   * by [z].
   *
   * [fold] is a "right" fold, which associates the binary operation
   * the opposite way as the [fold_left] function from Coq's
   * standard library.
   *)
  Fixpoint fold {A B : Type} (b_cons : A -> B -> B) (b_nil : B)
           (xs : list A) : B :=
    match xs with
    | nil => b_nil
    | cons x xs' => b_cons x (fold b_cons b_nil xs')
    end.

  (* For instance, we have
         fold plus 10 [1; 2; 3]
       = 1 + (2 + (3 + 10))
       = 16
   *)
  Example fold_example : fold plus 10 [1; 2; 3] = 16.
  Proof.
    simplify.
    equality.
  Qed.

  (* Prove that [map] can actually be defined as a particular
   * sort of [fold].
   *)
  Lemma map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
      map f xs = fold (fun x ys => cons (f x) ys) nil xs.
  Proof.
  Admitted.

  (* Since [fold f z] replaces [cons] with [f] and [nil] with
   * [z], [fold cons nil] should be the identity function.
   *)
  Theorem fold_id : forall {A : Type} (xs : list A),
      fold cons nil xs = xs.
  Proof.
  Admitted.

  (* If we apply [fold] to the concatenation of two lists,
   * it is the same as folding the "right" list and using
   * that as the starting point for folding the "left" list.
   *)
  Theorem fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                               (xs ys : list A),
      fold f z (xs ++ ys) = fold f (fold f z ys) xs.
  Proof.
  Admitted.

  (* Using [fold], define a function that computes the
   * sum of a list of natural numbers.
   *)
  Definition sum : list nat -> nat. Admitted.

  Example sum_example : sum [1; 2; 3] = 6.
  Proof.
  Admitted.

  (* Using [fold], define a function that computes the
   * conjunction of a list of Booleans (where the 0-ary
   * conjunction is defined as [true]).
   *)
  Definition all : list bool -> bool. Admitted.

  Example all_example : all [true; false; true] = false.
  Proof.
  Admitted.


  (* The following two theorems, [sum_append] and [all_append],
   * say that the sum of the concatenation of two lists
   * is the same as summing each of the lists first and then
   * adding the result.
   *)
  Theorem sum_append : forall (xs ys : list nat),
      sum (xs ++ ys) = sum xs + sum ys.
  Proof.
  Admitted.


  Theorem all_append : forall (xs ys : list bool),
      all (xs ++ ys) = andb (all xs) (all ys).
  Proof.
  Admitted.

  (* Using [fold], define a function that composes a list of functions,
   * applying the *last* function in the list *first*.
   *)
  Definition compose_list {A : Type} : list (A -> A) -> A -> A. Admitted.

  Example compose_list_example :
    compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.
  Proof.
  Admitted.


  (* Show that [sum xs] is the same as converting each number
   * in the list [xs] to a function that adds that number,
   * composing all of those functions together, and finally
   * applying that large composed function to [0].
   * Note that function [plus], when applied to just one number as an
   * argument, returns a function over another number, which
   * adds the original argument to it!
   *)
  Theorem compose_list_map_add_sum : forall (xs : list nat),
      compose_list (map plus xs) 0 = sum xs.
  Proof.
  Admitted.
End Impl.

Module ImplCorrect : Pset3Sig.S := Impl.

(* Authors:
 * Ben Sherman
 * Adam Chlipala
 * Samuel Gruetter
 * Clément Pit-Claudel
 * Amanda Liu
 *)
