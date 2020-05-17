(* This is how you make a comment *)
(* This file is worked out code from the document 
http://www.cs.umd.edu/class/spring2019/cmsc631/files/ProofsAndPrograms.html.
Nowhere do I claim this is original code. *)

(* Simple Inductive Type: a coin which flips heads or tails *)
Inductive coin : Type := (* This defines coin, which is a Type *)
| heads : coin (* Pattern matching, as in functional languages. *)
| tails : coin.

(* I guess a period ends definitions. *)

(* A function which flips a coin's values from heads to tails *)
Definition flip (c : coin) : coin :=
  match c with
  | heads => tails
  | tails => heads
  end.

Compute (flip heads). (* Computes the result of flip heads *)
Compute (flip tails).

(* Alternative def'n of flip using if else statements *)
Definition flip2 (c : coin) : coin :=
  if c then tails else heads.

Compute (flip2 heads).
Compute (flip2 tails).

(*The check command: used to check types of objects. *)
Check heads.
Check coin.
Check flip.

(* Another Example: Rock, Paper, Scissors. An example of a non-group. *)
(* is Type the same thing as Set? *)
Inductive rps : Type :=
| rock : rps
| paper : rps
| scissors : rps.

Inductive outcome : Type :=
| win : outcome
| loss : outcome
| tie : outcome.

(* Defining the game of rps: the long way. Brute force, even considering pattern matching. *)
Definition game (p q : rps) : outcome :=
  match p, q with
  | rock, scissors => win
  | rock, paper => loss
  | scissors, rock => loss
  | scissors, paper => win
  | paper, rock => win
  | paper, scissors => loss
  | _, _ => tie
  end.

(* This took a lot of work. Is there a simpler way we could do this? *)
(* A predicate has type Prop. Like a proposition, it expresses truth of a given claim. *)

(* Inductive type beats, which corresponds to 'A beats B'. *)
(* the different types crushes, cuts, covers are naming conventions *)
(* which mostly for example, indicate that beats(rock, scissors) is true, and others are false. *)
Inductive beats : rps -> rps -> Prop :=
| crushes : beats rock scissors
| cuts : beats scissors paper
| covers: beats paper rock.

Check (beats rock scissors).
Check (beats rock rock).
Check crushes.

(* Similarly, define the loses and ties predicates. *)

Inductive loses : rps -> rps -> Prop :=
| crushed : loses scissors rock
| cut : loses paper scissors
| covered : loses rock paper.
Inductive ties : rps -> rps -> Prop :=
| tie_rock : ties rock rock
| tie_paper : ties paper paper
| tie_scissors : ties scissors scissors.


(* Here is a claim: if A loses to B, then B loses to A. *)
(* This is the proof of the claim? *)
(*
Here is what this is doing:
This 'proof' abuses the pattern matching of the system. 
We take beats p q and we will return loses q p.
The Coq system will ensure that:
- The pattern matcher is exhaustive.
- The output makes sense.
*)
Definition beats_backwards_loses (p q : rps) (b: beats p q) : loses q p :=
match b with
| crushes => crushed
| cuts => cut
| covers => covered
end.

Definition loses2 (p q : rps) := beats q p.

Check(loses2).

Definition loses_then_loses2 (p q : rps) (l : loses p q) : loses2 p q :=
match l with
| crushed => crushes
| cut => cuts
| covered => covers
end.

Check (loses_then_loses2).
Check (crushed).
Example

Definition loses2_then_loses (p q : rps) (l : loses2 p q) : loses p q :=
match l with
| crushes => crushed
| cuts => cut
| covers => covered
end.

(* This shows the two definitions are equivalent. The 'proof' here is essentially by casework,
I suppose. *)

(* Another example: defining some predicates on pairs of coins. *)

Inductive same : coin -> coin -> Prop := 
| same_heads : same heads heads
| same_tails : same tails tails.

Inductive inverse : coin -> coin -> Prop :=
| h_t : inverse heads tails
| t_h : inverse tails heads.

(* We will show that flipping gives you an inverse *)
Definition flip_inverse (c : coin) : inverse c (flip c) :=
match c with
| heads => h_t
| tails => t_h
end.

(* Double flipping gives you the original *)
Definition flip_involutive (c : coin) : same c (flip (flip c)) :=
match c with
| heads => same_heads
| tails => same_tails
end.

(* We can obviously use these previous 'proofs' in future proofs. *)
Definition triple_flip (c : coin) : same (flip c) (flip (flip (flip c))) :=
  flip_involutive (flip c).

