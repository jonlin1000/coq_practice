(** * ProofsAndPrograms: The Fundamentals of the Coq Proof Assistant *)


(** Ignore this line *)
Set Warnings "-notation-overridden,-parsing".

(* ################################################################# *)
(** * Programs *)

(** Let's start by defining a simple inductive datatype, corresponding
   to a coin: *)

Inductive coin : Type :=
| heads : coin
| tails : coin.

(** We can define a function [flip] that turns the coin over: *)

Definition flip (c : coin) : coin :=
  match c with
  | heads => tails
  | tails => heads
  end.

(** Let's look at a few examples of coin flips. *)

Compute (flip heads).
Compute (flip tails).

(** You might notice that this coin corresponds to a boolean value.
   Conveniently, Coq makes the same observation! This allows us to
   write an alternative definition of flip. *)

Definition flip' (c : coin) := if c then tails else heads.

Compute (flip' heads).
Compute (flip' tails).

(** In general, Coq will allow us to use its conditional statement for
   any datatype with two constructors. The first constructor will be
   treated as [true] and the second as [false]. This [if] statement is
   really just notation for the corresponding [match] statement. *)

(** We will often want to check the types of various objects from
   [coin] to coins to functions. For this we use the [Check]
   command. *)

Check heads.
Check coin.
Check flip.
Check (flip heads).

(** Let's look at a slightly more complicated datatype corresponding to
   a play in the game Rock-Paper-Scissors: *)

Inductive play : Type :=
| rock : play
| paper : play
| scissors : play.

(** There are three possible outcomes: a win a loss and a tie. *)
Inductive outcome : Type :=
| win : outcome
| loss : outcome
| tie : outcome.

(** We can use these to define a game of Rock-Paper-Scissors. *)

Definition game (p1 p2 : play) : outcome :=
  match p1, p2 with
  | rock, scissors  => win
  | scissors, paper => win
  | paper, rock     => win
  | scissors, rock  => loss
  | paper, scissors => loss
  | rock, paper     => loss
  | _, _            => tie
  end.

(** That's pretty wordy, even given our use of wildcard characters to
   capture the three remaining cases, where both players tie. It would
   be nice if there were some way to express 'A beats B' and then use
   that to define losses. *)

(** Fortunately, Coq has the ability to define exactly that through its
   use of propositions. *)

(* ################################################################# *)
(** * Propositions *)

(** A predicate in Coq, which has the type [Prop], expresses the truth
   of a given claim. Let's define a prop corresponding to 'A beats B'.
   *)

Inductive beats : play -> play -> Prop :=
| crushes : beats rock scissors
| cuts    : beats scissors paper
| covers  : beats paper rock.

(** Since [beats] takes any two plays to a Prop, both of the following
   are valid propositions. *)

Check (beats rock scissors).
Check (beats rock rock).

(** The important difference between [beats rock scissors] and [beats
   rock rock] is that [beats rock scissors] is _True_. For a Prop to
   be true means that there is an element of that type. *)

Check crushes.

(** It so happens that [beats rock rock] is _False_, but showing its
   falsity is somewhat complicated. We'll return to the subject of
   falsity later in this chapter.  *)

(** It's worth noting that 'Prop' isn't special. We could replace every
   instance of Prop in this chapter with 'Type' and nothing would
   break. The significance of 'Prop' lies in its interpretation: We
   treat 'beats' not as a Type that depends on two plays but as a
   _claim_ about those two plays. *)

(** We can easily define [loses] and [ties]: *)

Inductive loses : play -> play -> Prop :=
| crushed  : loses scissors rock
| cut      : loses paper scissors
| covered  : loses rock paper.

Inductive ties : play -> play -> Prop :=
| tie_rock : ties rock rock
| tie_paper : ties paper paper
| tie_scissors : ties scissors scissors.

(** Time to start proving things!  
   Here's a simple claim : If A beats B, then B loses to A. *)

Definition beats_backwards_loses (p1 p2 : play) (b : beats p1 p2) : loses p2 p1 :=
  match b with
  | crushes => crushed
  | cuts    => cut
  | covers  => covered
  end.

(** In fact, we could have simply defined '[loses] in terms of [beats]! *)

Definition loses' (p1 p2 : play) := beats p2 p1.

(** **** Exercise: 2 stars (loses_then_loses')  *)
(** Show that these two definitions of [loses] are equivalent. *)

Definition loses_then_loses' (p1 p2 : play) (l : loses p1 p2) : loses' p1 p2 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition loses'_then_loses (p1 p2 : play) (l : loses' p1 p2) : loses p1 p2 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** [] *)


(** Our examples above didn't involve any computation - we haven't even
   defined any (traditional) functions on plays. Let's try proving
   some things about coin flipping.  *)

(** First, we will introduce two predicates on pair of coins: *)

Inductive same : coin -> coin -> Prop :=
| same_heads : same heads heads 
| same_tails : same tails tails.

Inductive inverse : coin -> coin -> Prop :=
| heads_tails : inverse heads tails 
| tails_heads : inverse tails heads.

(** Let's first show that flipping always yields an inverse. *)
Definition flip_inverse (c : coin) : inverse c (flip c) :=
  match c with
  | heads => heads_tails
  | tails => tails_heads
  end.

(** We can also show that flipping a coin twice yields the original
   coin. *)

Definition flip_involutive (c : coin) : same c (flip (flip c)) :=
  match c with
  | heads => same_heads
  | tails => same_tails
  end.

(** Just like any coq term, we can reuse earlier proofs: *)

Definition flip_thrice (c : coin) : same (flip c) (flip (flip (flip c))) 
(* WORKED IN CLASS *) :=
  flip_involutive (flip c).


(* ################################################################# *)
(** * Logic *)

(** Now that we know how to prove things, it would be nice to have some
   logical connectives, like [and] and [or] to increase the
   expressiveness of our logic. It would also be nice to have more
   tools for logical reasoning, which we will develop in this section.
   *)

(* ================================================================= *)
(** ** Logic 101 *)

(** Let's start off with a simple rule of logic: Modus Ponens Modus
   Ponens says that if X -> Y and X are true, so is Y.  In our
   context, that means that from a function of type [X -> Y] and a
   term of type [X], we can construct a [Y]. *)

Definition modus_ponens (X Y : Prop) (P : X -> Y) (x : X) : Y := P x.

(** Note that Modus Ponens is simply function application! *)

(** Here's the chain rule, which corresponds to function composition: *)
Definition chain_rule (X Y Z : Prop) (P : X -> Y) (Q : Y -> Z) : X -> Z :=
  fun x => Q (P x).

(** We know that a [Prop] is true if it has any elements. A false
   [Prop] would then be a Prop without any elements. While many Props
   are true and many are false, it's worth having at least one
   archetypal [True] and [False]. *)

Inductive True := t.
Inductive False := .

(** [False] is actually a really exciting thing to prove. If I can
   construct an element of [False], I can obtain whatever I want -
   even elements of other uninhabited Props! *)

Definition ex_falso_quodlibet (X : Prop) (f : False) : X :=
  match f with
  end.

(** **** Exercise: 2 stars (X_then_X)  *)
(** State and prove the theorem that for any X, X implies X. *)

(** What does this correspond to computationally? *)


(** We can now use our chain rule to reverse modus ponens. *)

Definition modus_tollens (X Y : Prop) : (X -> Y) -> (Y -> False) -> (X -> False) :=
  chain_rule X Y False.

(* ================================================================= *)
(** ** And and Or *)
(** Let's define some standard logical connectives: *)

Inductive and (X Y : Prop) : Prop :=
  conj : X -> Y -> and X Y.

Inductive or (X Y : Prop) : Prop :=
 | or_introl : X -> or X Y
 | or_intror : Y -> or X Y.

(** The following commands just say that we don't need to provide type
    arguments to our constructors of [and] and [or]. *) 
Arguments conj {X Y}.
Arguments or_introl {X Y}.
Arguments or_intror {X Y}.

(** We can also introduce some notations for these connectives: *)
Infix "/\" := and : type_scope. 
Infix "\/" := or : type_scope.

(** From the perspective of functional programming, [and] and [or] are
    just product types and sum types respectively. Indeed, the Coq
    standard library separately defines [A * B] and [A + B] over
    [Type]s. But it's useful to have these for Props as well. *)

(** What can we prove about [and] and [or]?
   Some basic properties include symmetry and associativity. *)

Definition and_symm (X Y : Prop) : X /\ Y -> Y /\ X 
(* WORKED IN CLASS *) :=
  fun xy =>
  match xy with
  | conj x y => conj y x
  end.
                                              
(** **** Exercise: 2 stars (or_symm)  *)
(** Prove a similar theorem for `or` *)

Definition or_symm (X Y : Prop) : X \/ Y -> Y \/ X 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** [] *)

Definition and_assoc (X Y Z : Prop) : (X /\ Y) /\ Z -> X /\ (Y /\ Z)  
(* WORKED IN CLASS *) :=
  fun xyz =>
  match xyz with
  | conj (conj x y) z => conj x (conj y z)
  end.

(* ################################################################# *)
(** * The Proof Environment *)

(** Unfortunately, these proofs can get pretty heavy, especially when
   there are a lot of cases to match on. For instance, consider the
   following proof that [or] is associative. *)

Definition or_assoc (X Y Z : Prop) : (X \/ Y) \/ Z -> X \/ (Y \/ Z) :=
  fun xyz =>
    match xyz with
    | or_introl xy => match xy with
                     | or_introl x => or_introl x
                     | or_intror y => or_intror (or_introl y)
                     end
    | or_intror z => or_intror (or_intror z)
    end.

(** And it just gets messier from here. *)

(** Instead of having to write out Coq proofs as complicated programs
    involving multiple levels of matching, function application and so
    forth, Coq provides a convenient environment for building proofs,
    step by step.

   Here's [and_symm] again: *)

Lemma and_symm' (X Y : Prop) : X /\ Y -> Y /\ X.
Proof.
(* WORKED IN CLASS *)
  intros xy.             (* introduce the hypotheses *)
  destruct xy as [x y].  (* case analysis *)
  apply (conj y x).      (* apply a term *)
Qed.

(** Since in lemmas we don't reference X and Y on the right hand side
    of [:=], we tend to name all of our arguments on the right side of
    the [:] We can also apply [conj] and fill in X and Y later. *)

Lemma and_symm'' : forall (X Y : Prop), X /\ Y -> Y /\ X.
Proof.
  intros X Y xy.
  destruct xy as [x y].
  apply conj.
  apply y.
  apply x.
Qed.

(** Let's return to `or_assoc` *)

Lemma or_assoc' : forall (X Y Z : Prop), (X \/ Y) \/ Z -> X \/ (Y \/ Z).
Proof.
  (* WORKED IN CLASS *)
  intros X Y Z xyz.
  destruct xyz as [xy | z].
  (* Two goals! We can address each separately. *)
  - destruct xy as [x | y].
    + apply or_introl.
      apply x.
    + apply or_intror.
      apply or_introl.
      apply y.
  - apply or_intror.
    apply or_intror.
    apply z.
Qed.

(** **** Exercise: 3 stars (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall X Y Z : Prop,
  X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ================================================================= *)
(** ** Constructive Logic *)

(** Since Coq requires us to construct a term in order to demonstrate
    that a type is inhabited, not all theorems of classical logic are
    true in Coq's own logic. *)

Lemma excluded_middle : forall (X : Prop), X \/ (X -> False).
Proof.
    intros X.
  (* Unfortunately, we can't proceed as we have no hypotheses
     and no elements of type X or X -> False *)
  Abort.

(** The law of double negation is more interesting: *)

Definition double_negation_forwards : forall (X : Prop), X -> ((X -> False) -> False). 
Proof.
  (* WORKED IN CLASS *)
  intros X x.
  intros nx.
  apply nx.
  apply x.
Qed.
  
Definition double_negation_backwards : forall (X : Prop), ((X -> False) -> False) -> X. 
Proof.
    intros X nnx.
  (* Once again, there's no clear way to proceed. Indeed 
     ~ ~ X -> X is not a theorem of Coq's logic *)
  Abort.

(** Jumping back to our game of rock-paper-scissors, using the proof
    system it's not hard to prove some basic theorems. *)

Lemma beats_same : forall (x y y' : play), beats x y -> ties y y' -> beats x y'.
Proof.
  (* WORKED IN CLASS *)
  intros x y y' B T.
  destruct T.
  - apply B.
  - apply B.
  - apply B.  
Qed.  
  
(** Here's a more succinct definition of [ties]: *)

Inductive ties' : play -> play -> Prop :=
| ties_same : forall (p : play), ties' p p.
                            
(** Let's try proving the theorem above in our new system. *)

Lemma beats_same' : forall (x y y' : play), beats x y -> ties' y y' -> beats x y'.
Proof.
  (* WORKED IN CLASS *)
  intros x y y' B T.
  destruct T as [t].
  apply B.
Qed.  
  
(** **** Exercise: 2 stars (ties_symm)  *)
(** Using the new definition, prove that if a ties b then b ties a *)
Theorem ties_symm : forall (x y : play), ties' x y -> ties' y x.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)








(* ################################################################# *)
(** * Equality *)

(** Note that we separately defined [ties] and [same] for plays and
    coins.  Wouldn't it be nice if we could define a single proposition
    for any type that claims two terms of that type are identical? *)

Inductive eq (A : Type) : A -> A -> Prop :=
  | eq_refl : forall (a : A), eq A a a.

Notation "x == y" := (eq _ x y) (at level 70): type_scope.

(** Of course, there are other, arguably more useful ways to define
    equality.  Here's Leibniz's definition (and, as far as we know, not
    Newton's): *)

Definition Leq (A : Type) (a b : A) : Prop := forall (P : A -> Prop), P a -> P b.  

Notation "x =L y" := (Leq _ x y) (at level 70): type_scope.

(** That is, 'a' is equal to 'b' if everything true of 'a' is true of
    'b'. *) 

(** Let's show that Leq is at least as strong as eq. *)

Lemma Leq_then_eq : forall (A : Type) (a b : A), a =L b -> a == b.
Proof.
  (* WORKED IN CLASS *)
  intros A a b L.
  unfold Leq in L.
  apply L.
  apply eq_refl.
Qed.
  
Print Leq_then_eq.

(** Let's try going in the opposite direction. *)

Lemma eq_then_Leq : forall (A : Type) (a b : A), a == b -> a =L b.
Proof.
  intros A a b H.
  unfold Leq.
  intros P p.
  destruct H.
  apply p.
Qed.

(** For convenience, we can package these up into a single claim. *)

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).
Notation "A <-> B" := (iff A B) (at level 95) : type_scope.

Definition eq_Leq (A : Type) (a b : A) : a == b <-> a =L b :=
  conj (eq_then_Leq A a b) (Leq_then_eq A a b).

(** What does this tell us? It says that it's okay to replace a with b
    throughout a proposition if we know that [eq a b]. Let's try it
    out. *)

Lemma inverse_of_flip : forall (x y : coin), flip x == y -> inverse x y.
Proof.
  (* WORKED IN CLASS *)
  intros x y H.
  apply (eq_then_Leq coin (flip x) y).
  apply H.
  Search inverse.
  apply flip_inverse.
Qed.
  
(** This observation forms the basis of Coq's [rewrite] rule, which
    uses a hypotheses of the form [a = b] to replace all instances of
    [a] with [b] in a proposition.  We'll use Coq's standard library
    equality (which is identical to our own) to illustrate: *)

Lemma eq_trans : forall (A : Type) (a b c : A), a = b -> b = c -> a = c.
Proof.
  intros A a b c H H0.
  rewrite H.
  apply H0.
Qed.

(** **** Exercise: 1 star (eq_trans')  *)
(** Exercise: Prove this using our version of eq, which doesn't have
    [rewrite]. **)
(** Remove "[Admitted.]" and fill in the proof. *)

Lemma eq_trans' : forall (A : Type) (a b c : A),  a == b -> b == c -> a == c.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (y_is_nice)  *)
(** Exercise: Use one of the lemmas above to prove that y
    is nice **)
(** Remove "[Admitted.]" and fill in the proof. *)
Lemma y_is_nice : forall (X : Type) (x y : X) (nice : X -> Prop),
    x == y -> nice x -> nice y.
Proof.
(* FILL IN HERE *) Admitted.

(** [] *)

    
