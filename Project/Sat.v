Require Import String.
Require Import List.
Require Import Bool.

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
  destruct x as [x]. simpl.
  rewrite String.eqb_eq. reflexivity.
  Qed.

Lemma eqb_id_eq : forall (x y : id),
  eqb_id x y = true <-> x = y.
Proof.
  intros x y. split; 
  intros H; destruct x as [x]; destruct y as [y];
  [f_equal | injection H; intros H']; 
  apply String.eqb_eq; assumption.
  Qed.

Lemma eqb_id_neq : forall (x y : id),
  eqb_id x y = false <-> x <> y.
Proof.
  intros x y. split; 
  intros H; destruct x as [x]; destruct y as [y].
  - (* -> *) intros contra. simpl in H. 
    rewrite String.eqb_neq in H. injection contra. exact H.
  - (* <- *) destruct (eqb_id (Id x) (Id y)) eqn:Exy.
    + rewrite eqb_id_eq in Exy. contradiction.
    + reflexivity.
  Qed.

(* ================================================================= *)
(** ** Abstract Syntax Tree / Grammar *)

(** We can now specify the type of formulas [form] through a set of rules. *)

Inductive form : Type :=
  | (* x *) form_var (x : id)
  | (* true, false *) form_bool (b : bool)
  | (* p /\ q *) form_conj (p : form) (q : form)
  | (* p \/ q *) form_disj (p : form) (q : form)
  | (* p -> q *) form_impl (p : form) (q : form)
  | (* ~p *) form_neg (p : form).

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

(** We define a valuation as a total map from identifiers to booleans. By
    default, identifiers are mapped to [false]. *)

Definition valuation : Type := id -> bool .

Definition empty_valuation : valuation := fun x => false.
Definition override (v : valuation) (x : id) (b : bool) : valuation :=
    fun y => if eqb_id x y then b else v y.

(** Again, let us also introduce shorthand notations. *)

Notation "x '!->' b" := (override empty_valuation x b) (at level 100).
Notation "x '!->' b ';;' v" := (override v x b)
    (at level 100, b at next level, right associativity).

Definition valuation_example :=
    x !-> true ;; y !-> false ;; z !-> true.
Unset Printing Notations.
Print valuation_example.
Set Printing Notations.

(** We will later make use of the following lemma.
    _Source: Pierce et. al. Logical Foundations. Vol. 1 Software Foundations. 
    Electronic textbook, 2024_ *)
    
Lemma update_eq : forall (v : valuation) (x : id) (b : bool),
  (x !-> b ;; v) x = b.
Proof.
  intros v x b. unfold override. 
  rewrite eqb_id_refl. reflexivity.
  Qed.

(* ================================================================= *)
(** ** Interpreter *)

(** The following function interprets a formula in the context of a valuation, 
    that is, returns [true] if and only if the formula holds for the given 
    mapping of identifiers to boolean values. *)

Fixpoint interp (v : valuation) (p : form) : bool :=
  match p with
  | form_var x => v x
  | <{ true }> => true
  | <{ false }> => false
  | <{ p /\ q }> => (* both need to hold *) (interp v p) && (interp v q)
  | <{ p \/ q }> => (* one needs to hold *) (interp v p) || (interp v q)
  | <{ p -> q }> => (* equiv ~p \/ q *) (negb (interp v p)) || (interp v q)
  | <{ ~p }> => negb (interp v p)
  end.

Example interp_example1 : 
  interp empty_valuation <{ x \/ (y /\ z) \/ (false -> x) }> = true.
Proof. reflexivity. Qed.

Example interp_example2 :
  interp (x !-> true ;; y !-> false ;; z !-> true)
    <{ x -> ((x \/ y) /\ (~z)) }> 
  = false.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Optimizer *)

(** Many formulas are not in minimal form, i.e., can further be simplified 
    purely on a syntactic basis without considering a valuation. We first give
    give an inductive predicate for formulas that do not contain atoms, i.e., do
    not contain [true] or [false]. *)

Inductive contains_no_atoms : form -> Prop :=
  | cna_var : forall (x : id), 
      contains_no_atoms <{ x }>
  | cna_cdi : forall (p q1 q2 : form), 
      p = <{ q1 /\ q2 }> \/ p = <{ q1 \/ q2 }> \/ p = <{ q1 -> q2 }> ->
      contains_no_atoms q1 ->
      contains_no_atoms q2 ->
      contains_no_atoms p (* (q1 op q2) has not atoms if q1 and q2 do not *)
  | cna_neg : forall (p : form),
      contains_no_atoms p ->
      contains_no_atoms <{ ~p }>.

(** Then, we define a formula to be minimal if it is either an atom or does not
    contain any atoms. *)

Definition minimal_form (p : form) : Prop :=
  (exists (b : bool), p = form_bool b) \/ contains_no_atoms p.

(* ================================================================= *)
(** ** Function *)

(** We know introduce the optimizer function. It performs a DFS post-order
    traversal of the abstract syntax tree and applies allowed simplifications at
    each step. *)

Fixpoint optim (p : form) : form :=
  match p with
  | <{ q1 /\ q2 }> =>
    let q1_opt := optim q1 in 
    let q2_opt := optim q2 in
    match q1_opt, q2_opt with
    | <{ true }>, _ => q2_opt
    | _, <{ true }> => q1_opt
    | <{ false }>, _ => <{ false }>
    | _, <{ false }> => <{ false }>
    | _, _ => <{ q1_opt /\ q2_opt }>
    end
  | <{ q1 \/ q2 }> =>
    let q1_opt := optim q1 in
    let q2_opt := optim q2 in
    match q1_opt, q2_opt with
    | <{ true }>, _ => <{ true }>
    | _, <{ true }> => <{ true }>
    | <{ false }>, _ => q2_opt
    | _, <{ false }> => q1_opt
    | _, _ => <{ q1_opt \/ q2_opt }>
    end
  | <{ q1 -> q2 }> =>
    let q1_opt := optim q1 in
    let q2_opt := optim q2 in
    match q1_opt, q2_opt with
    | <{ true }>, _ => q2_opt
    | _, <{ true }> => <{ true }>
    | <{ false }>, _ => <{ true }>
    | _, <{ false }> => <{ ~q1_opt }>
    | _, _ => <{ q1_opt -> q2_opt }>
    end
  | <{ ~q }> =>
    let q_opt := optim q in
    match q_opt with
    | <{ true }> => <{ false }>
    | <{ false }> => <{ true }>
    | _ => <{ ~q_opt }>
    end
  | _ => p
  end.

(* ================================================================= *)
(** ** Correctness *)

(** First, let us underline that the optimizer indeed purely operates on a
    syntactical level through the following lemma. *)

Lemma optim_no_atoms_same : forall (p : form),
  contains_no_atoms p -> optim p = p.
Proof.
  intros p H. induction H as [x | p q1 q2 Hp Hq1 IHq1 Hq2 IHq2 | q Hq IHq].
  - reflexivity.
  - destruct Hp as [Hp | [Hp | Hp]]; rewrite Hp; clear Hp;
    simpl; rewrite IHq1; clear IHq1; rewrite IHq2; clear IHq2;
    inversion Hq1 as [xq1 Hxq1 | q1' q11 q12 Hq1' Hq11 Hq12 | q1' Hq1'];
    inversion Hq2 as [xq2 Hxq2 | q2' q21 q22 Hq2' Hq21 Hq22 | q2' Hq2'];
    try destruct Hq1' as [Hq1' | [Hq1' | Hq1']];
    try destruct Hq2' as [Hq2' | [Hq2' | Hq2']]; subst; reflexivity.
  - simpl. rewrite IHq. destruct q; try reflexivity.
    inversion Hq. destruct H as [H | [H | H]]; inversion H.
  Qed.

(** Naturally, we need to show that the optimizer does not change the semantics
    of formulas, meaning that given an identical valuation, the interpreter will 
    _always_ return the same result for the formula itself and its optimized 
    version. *)

Hint Resolve andb_true_r : core.
Hint Resolve andb_false_r : core.
Hint Resolve orb_true_r : core.
Hint Resolve orb_false_r : core.

Ltac destruct_if b q := 
  let rw :=
    repeat match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end in
  destruct b; rw;
  [ reflexivity | destruct q; try destruct b; reflexivity]. 

Theorem optim_correct : forall (v : valuation) (p : form),
  interp v p = interp v (optim p).
Proof.
  induction p as [x | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                  q1 IHq1 q2 IHq2 | q1 IHq1]; 
  try reflexivity;
  simpl; destruct (optim q1);
  try destruct_if b (optim q2);
  try destruct b;
  try (rewrite IHq1; reflexivity);
  destruct (optim q2);
  try (simpl in *; rewrite IHq1, IHq2; reflexivity);
  try destruct b;
  simpl in *; rewrite IHq1, IHq2; auto.
  Qed.

(* ================================================================= *)
(** ** Minimizing Property *)

(** Now, we show that we actually gain something by using the optimizer, 
    meaning it indeed transforms any formula to its minimal form. *)

Theorem optim_minimizes : forall (p : form),
  minimal_form (optim p).
Proof.
  induction p as [x | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 |
                  q IHq];
  unfold minimal_form; simpl.
  - (* x *) right. constructor.
  - (* bool *) left. exists b. reflexivity.
  - (* q1 /\ q2 *) destruct IHq1 as [IHq1 | IHq1]; 
    destruct IHq2 as [IHq2 | IHq2].
    + (* q1, q2 bool *) left. 
      destruct IHq1 as [b1 IHq1]. destruct IHq2 as [b2 IHq2].
      rewrite IHq1. rewrite IHq2.
      destruct b1.
      * exists b2. reflexivity.
      * destruct b2; exists false; reflexivity.
    + (* q1 bool, q2 no atoms *) destruct IHq1 as [b1 IHq1]. rewrite IHq1.
      destruct b1.
      * (* b1 = true *) right. assumption.
      * (* b1 = false *) left. exists false. 
        destruct (optim q2); try destruct b; constructor.
    + (* q1 no atoms, q2 bool *) destruct IHq2 as [b2 IHq2]. rewrite IHq2.
      destruct b2.
      * (* b2 = true *) right; destruct (optim q1);
        (* optim q1 not bool *) try assumption.
        (* optim q1 bool *) inversion IHq1. 
        destruct H as [H | [H | H]]; inversion H.
      * (* b2 = false *) left. exists false.
        destruct (optim q1); try destruct b; constructor.
    + (* q1, q2 no atoms *) destruct (optim q1);
      (* optim q1 not bool *) try (right; destruct (optim q2);
      (* optim q2 bool *) try (inversion IHq2; destruct H as [H | [H | H]]; 
      inversion H);
      (* else *) econstructor; 
      try (left; reflexivity);
      try rewrite <- H; assumption).
      (* optim q1 bool *) destruct b.
      -- (* b = true *) right. assumption.
      -- (* b = false *) left. exists false. 
         destruct (optim q2); try destruct b; reflexivity.
  - (* q1 \/ q2 *) destruct IHq1 as [IHq1 | IHq1]; 
    destruct IHq2 as [IHq2 | IHq2].
    + (* q1, q2 bool *) left. 
      destruct IHq1 as [b1 IHq1]. destruct IHq2 as [b2 IHq2].
      rewrite IHq1. rewrite IHq2.
      destruct b1.
      * exists true. reflexivity.
      * destruct b2; [exists true | exists false]; reflexivity.
    + (* q1 bool, q2 no atoms *) destruct IHq1 as [b1 IHq1]. rewrite IHq1.
      destruct b1.
      * (* b1 = true *) left. exists true. reflexivity.
      * (* b1 = false *) destruct (optim q2);
        (* optim q2 bool *) try (inversion IHq2; destruct H as [H | [H | H]]; 
        inversion H);
        (* else *) right; try rewrite <- H; assumption.
    + (* q1 no atoms, q2 bool *) destruct IHq2 as [b2 IHq2]. rewrite IHq2.
      destruct b2.
      * (* b2 = true *) left. destruct (optim q1); exists true;
        try destruct b; reflexivity.
      * (* b2 = false *)  destruct (optim q1); 
        (* optim q1 bool *) try (inversion IHq1; destruct H as [H | [H | H]]; 
        inversion H);
        (* else *) right; try rewrite <- H; assumption.
    + (* q1, q2 no atoms *) destruct (optim q1);
      destruct (optim q2);
      try (inversion IHq1; destruct H as [H | [H | H]]; inversion H);
      try (inversion IHq2; destruct H as [H | [H | H]]; inversion H);
      right; econstructor; try (right; left; reflexivity);
      try rewrite <- H; try assumption;
      inversion IHq2; destruct H3 as [H3 | [H3 | H3]]; inversion H3. 
      Unshelve. auto. auto. auto. auto. auto. auto.
  - (* q1 -> q2 *) destruct IHq1 as [IHq1 | IHq1]; 
    destruct IHq2 as [IHq2 | IHq2].
    + (* q1, q2 bool *) left. 
      destruct IHq1 as [b1 IHq1]. destruct IHq2 as [b2 IHq2].
      rewrite IHq1. rewrite IHq2.
      destruct b1.
      * exists b2. reflexivity.
      * destruct b2; exists true; reflexivity.
    + (* q1 bool, q2 no atoms *) destruct IHq1 as [b1 IHq1]. rewrite IHq1.
      destruct b1.
      * (* b1 = true *) right. assumption.
      * (* b1 = false *) destruct (optim q2);
        (* optim q2 bool *) try (inversion IHq2; destruct H as [H | [H | H]]; 
        inversion H);
        (* else *) left; exists true; reflexivity.
    + (* q1 no atoms, q2 bool *) destruct IHq2 as [b2 IHq2]. rewrite IHq2.
      destruct b2.
      * (* b2 = true *) left. destruct (optim q1); exists true;
        try destruct b; reflexivity.
      * (* b2 = false *)  destruct (optim q1);
        (* optim q1 bool *) try (inversion IHq1; destruct H as [H | [H | H]]; 
        inversion H);
        (* else *) right; constructor; try rewrite <- H; assumption.
    + (* q1, q2 no atoms *) destruct (optim q1);
      (* optim q1 bool *) try (inversion IHq1; destruct H as [H | [H | H]];
      inversion H);
      (* else *) destruct (optim q2);
      (* optim q2 bool *) try (inversion IHq2; 
      try destruct H as [H | [ H | H]]; try destruct H3 as [H3 | [H3 | H3]];
      try inversion H; try inversion H3);
      (* else *) right; econstructor; try (right; right; reflexivity);
      try rewrite <- H; try rewrite <- H3; subst; assumption.
  - (* ~q *) destruct IHq as [IHq | IHq]; destruct (optim q);
    try (destruct IHq as [b IHq]); try inversion IHq;
    (* optim q not bool *) try (right; constructor; assumption);
    try destruct b; left; try (exists true; reflexivity);
    exists false; reflexivity.
  Qed.