Require Import String.
Require Import List.

(** In this project, we implement a small brute-force SAT-Solver and formally
    prove it to be correct and complete. *)

(* ################################################################# *)
(** * Syntax *)

(** First, we formalize the syntax of boolean propositional formulas. *)

(* ================================================================= *)
(** ** Identifiers *)

(** We specify the [id] type for identifiers, i.e., variables, of our formulas 
    and define a boolean equality function and prove it to be equivalent to 
    propositional equality. *)

Inductive id : Type :=
  | Id (x : string).

Definition eqb_id (x y : id) : bool :=
  match x, y with
  | Id x, Id y => String.eqb x y
  end.

Lemma eqb_id_refl : forall (x : id),
  eqb_id x x = true.
Proof.
  intros x. destruct x. 
  simpl. rewrite eqb_eq. reflexivity.
  Qed.

Lemma eqb_id_eq : forall (x y : id),
  eqb_id x y = true <-> x = y.
Proof.
  intros x y. split; intros H; destruct x; destruct y;
  [f_equal | injection H; intros H']; 
  apply eqb_eq; assumption.
  Qed.

Lemma eqb_id_neq : forall (x y : id),
  eqb_id x y = false <-> x <> y.
Proof.
  intros x y. split; intros H; destruct x; destruct y.
  - intros contra. simpl in H. rewrite eqb_neq in H.
    injection contra. exact H.
  - destruct (eqb_id (Id x) (Id x0)) eqn:Eeq.
    + rewrite eqb_id_eq in Eeq. contradiction.
    + reflexivity.
  Qed.

(* ================================================================= *)
(** ** Abstract Syntax Tree / Grammar *)

(** We can now specify the type of formulas [form] through a set of rules. *)

Inductive form : Type :=
  | form_var (x : id)
  | form_bool (b : bool)
  | form_conj (p : form) (q : form)
  | form_disj (p : form) (q : form)
  | form_impl (p : form) (q : form)
  | form_neg (p : form).

(* ================================================================= *)
(** ** Concrete Syntax *)

(** For ease of reading, we specify notations representing the concrete syntax
    of formulas in Coq. *)

(* TODO: what am I doing here? *)
Coercion form_var : id >-> form. (* TODO: what am I doing here? *)
Declare Custom Entry form. 
Notation "<{ p }>" := p (p custom form at level 99).
Notation "( p )" := p (in custom form, p at level 90). 
Notation "x" := x (in custom form at level 0, x constr at level 0).
Notation "'true'" := (form_bool true) (in custom form at level 0).
Notation "'false'" := (form_bool false) (in custom form at level 0).
Notation "p /\ q" := (form_conj p q) (in custom form at level 30,
                                        left associativity).
Notation "p \/ q" := (form_disj p q) (in custom form at level 50,
                                        left associativity).
Notation "p -> q" := (form_impl p q) (in custom form at level 70,
                                        left associativity).
Notation "~ p" := (form_neg p) (in custom form at level 10).

(** Again, for ease of reading, we specify syntactic sugar for variables [x],
    [y] and [z]. *)

Definition x : id := Id "x".
Definition y : id := Id "y".
Definition z : id := Id "z".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(* ================================================================= *)
(** ** Examples *)

(** In the following examples, we illustrate the correspondence between 
    abstract and concrete syntax. *)

Definition abstract_syntax_example : form :=
    <{ ~x \/ true \/ z /\ y -> z }>.
Unset Printing Notations.
Print abstract_syntax_example.
Set Printing Notations.

Definition concrete_syntax_example1 : form :=
    form_conj (form_disj x (form_neg y)) (form_disj (form_neg x) y).
Print concrete_syntax_example1.

Definition concrete_syntax_example2 : form :=
    form_impl (form_neg y) (form_disj x y).
Print concrete_syntax_example2.

Definition concrete_syntax_example3 : form :=
    form_conj (form_conj x (form_neg x)) (form_bool true).
Print concrete_syntax_example3.

(* ################################################################# *)
(** * Semantics *)

(** Next, we specify the semantics of formulas, that is, their interpretation 
    when given a valuation. *)

(* ================================================================= *)
(** ** Valuations *)

(** We define a valuation as a total map from identifiers to booleans. *)

Definition valuation : Type := id -> bool .

Definition empty_valuation : valuation := fun x => false.
Definition override (V : valuation) (x : id) (b : bool) : valuation :=
    fun y => if eqb_id x y then b else V y.

Notation "x '!->' b" := (override empty_valuation x b) (at level 100).
Notation "x '!->' b ';' V" := (override V x b)
    (at level 100, b at next level, right associativity).

Definition valuation_example :=
    x !-> true ; y !-> false ; z !-> true.
Unset Printing Notations.
Print valuation_example.
Set Printing Notations.

(** We will later make use of the following lemma.
    _Source: Pierce et. al. Logical Foundations. Vol. 1 Software Foundations. 
    Electronic textbook, 2024._ *)
    
Lemma update_eq : forall (V : valuation) (x : id) (b : bool),
  (x !-> b ; V) x = b.
Proof.
  intros V x b. unfold override. 
  rewrite eqb_id_refl. reflexivity.
  Qed.


