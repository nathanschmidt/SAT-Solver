Require Import String.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.

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

Theorem id_eq_dec : forall (x y : id),
  {x = y} + {x <> y}.
Proof.
  intros x y. destruct (eqb_id x y) eqn:Exy.
  + left. rewrite eqb_id_eq in Exy. exact Exy.
  + right. rewrite eqb_id_neq in Exy. exact Exy.
  Defined.

(* ================================================================= *)
(** ** Abstract Syntax Tree / Grammar *)

(** We can now specify the type of formulas [form] through a set of rules. *)

Inductive form : Type :=
  | (* x *) form_id (x : id)
  | (* true, false *) form_bool (b : bool)
  | (* p /\ q *) form_conj (p : form) (q : form)
  | (* p \/ q *) form_disj (p : form) (q : form)
  | (* p -> q *) form_impl (p : form) (q : form)
  | (* ~p *) form_neg (p : form).

(* ================================================================= *)
(** ** Concrete Syntax *)

(** For ease of reading, we specify notations representing the concrete syntax
    of formulas in Coq. *)

Coercion form_id : id >-> form.
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

(** We will later make use of the following lemmas.
    _Source: Pierce et. al. Logical Foundations. Vol. 1 Software Foundations. 
    Electronic textbook, 2024_ *)
    
Lemma override_eq : forall (v : valuation) (x : id) (b : bool),
  (x !-> b ;; v) x = b.
Proof.
  intros v x b. unfold override. 
  rewrite eqb_id_refl. reflexivity.
  Qed.

Lemma override_neq : forall (v : valuation) (x1 x2 : id) (b : bool),
  x1 <> x2 ->
  (x1 !-> b ;; v) x2 = v x2.
Proof.
  intros v x1 x2 b H. unfold override. 
  rewrite <- eqb_id_neq in H. rewrite H.
  reflexivity.
  Qed.

Lemma override_same : forall (v : valuation) (x : id),
  (x !-> v x ;; v) = v.
Proof.
  intros v x. unfold override.
  apply functional_extensionality.
  intros x'. destruct (eqb_id x x') eqn:Exx'.
  - f_equal. rewrite eqb_id_eq in Exx'. exact Exx'.
  - reflexivity.
  Qed.

Lemma override_shadow : forall (v : valuation) (x : id) (b1 b2 : bool),
  (x !-> b2 ;; x !-> b1 ;; v) = (x !-> b2 ;; v).
Proof.
  intros v x b1 b2. unfold override.
  apply functional_extensionality.
  intros x'. destruct (eqb_id x x'); reflexivity.
  Qed.

Lemma override_permute : forall (v : valuation) (x1 x2 : id) (b1 b2 : bool),
  x2 <> x1 ->
  (x1 !-> b1 ;; x2 !-> b2 ;; v)
  =
  (x2 !-> b2 ;; x1 !-> b1 ;; v).
Proof.
  intros v x1 x2 b1 b2 H. unfold override.
  apply functional_extensionality.
  intros x. destruct (eqb_id x1 x) eqn:Ex1x.
  - destruct (eqb_id x2 x) eqn:Ex2x.
    + rewrite eqb_id_eq in Ex1x. rewrite Ex1x in H. 
      rewrite eqb_id_eq in Ex2x. rewrite Ex2x in H.
      exfalso. apply H. reflexivity.
    + reflexivity.
  - destruct (eqb_id x2 x) eqn:Ex2x.
    + reflexivity.
    + reflexivity.
  Qed.

(* ================================================================= *)
(** ** Interpreter *)

(** The following function interprets a formula in the context of a valuation, 
    that is, returns [true] if and only if the formula holds for the given 
    mapping of identifiers to boolean values. *)

Fixpoint interp (v : valuation) (p : form) : bool :=
  match p with
  | form_id x => v x
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
  | cna_id : forall (x : id), 
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

Example optim_example1 : 
  optim <{ x /\ (~true /\ (z \/ true)) -> x /\ y /\ z }> = <{ true }>.
Proof. reflexivity. Qed.

Example optim_example2 :
  optim <{ x /\ (y \/ (false -> z)) }> = <{ x }>.
Proof. reflexivity. Qed.

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
(** ** Minimization Property *)

(** Now, we show that we actually gain something by using the optimizer, 
    meaning it indeed transforms any formula to its minimal form. *)

Ltac destruct_or :=
  repeat match goal with
  | [ H : _ \/ _ |- _ ] => destruct H as [H | H]
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : _ = _ |- _ ] => rewrite H
  end.

Ltac destruct_invert q IH H := 
  destruct q;
  try (inversion IH; destruct H as [H | [H | H]]; inversion H);
  try (right; constructor; try rewrite <- H; assumption);
  try (right; try rewrite <- H; assumption).

Theorem optim_minimizes : forall (p : form),
  minimal_form (optim p).
Proof.
  induction p as [x | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 |
                  q IHq];
  unfold minimal_form in *; simpl.
  - (* x *) right. constructor.
  - (* bool *) left. exists b. reflexivity.
  - (* q1 /\ q2 *) destruct_or.
    + (* q1, q2 bool *) left. 
      destruct x1.
      * exists x0. reflexivity.
      * destruct x0; exists false; reflexivity.
    + (* q1 no atoms, q2 bool *) destruct x0.
      * (* b2 = true *) right; destruct (optim q1);
        (* optim q1 not bool *) try assumption.
        (* optim q1 bool *) inversion IHq1. 
        destruct H0 as [H0 | [H0 | H0]]; inversion H0.
      * (* b2 = false *) left. exists false.
        destruct (optim q1); try destruct b; constructor.
    + (* q1 bool, q2 no atoms *) destruct x0.
      * (* b1 = true *) right. assumption.
      * (* b1 = false *) left. exists false. 
        destruct (optim q2); try destruct b; constructor.
    + (* q1, q2 no atoms *) destruct (optim q1);
      (* optim q1 not bool *) try (right; destruct_invert (optim q2) IHq2 H;
      (* else *) econstructor; 
      try (left; reflexivity);
      try rewrite <- H; assumption).
      (* optim q1 bool *) destruct b.
      -- (* b = true *) right. assumption.
      -- (* b = false *) left. exists false. 
         destruct (optim q2); try destruct b; reflexivity.
  - (* q1 \/ q2 *) destruct_or.
    + (* q1, q2 bool *) left. destruct x1.
      * exists true. reflexivity.
      * destruct x0; [exists true | exists false]; reflexivity.
    + (* q1 no atoms, q2 bool *) destruct x0.
      * (* b2 = true *) left. destruct (optim q1); exists true;
        try destruct b; reflexivity.
      * (* b2 = false *) destruct_invert (optim q1) IHq1 H0.
    + (* q1 bool, q2 no atoms *) destruct x0.
      * (* b1 = true *) left. exists true. reflexivity.
      * (* b1 = false *) destruct_invert (optim q2) IHq2 H0.
    + (* q1, q2 no atoms *) destruct_invert (optim q1) IHq1 H;
      destruct_invert (optim q2) IHq2 H;
      right; econstructor; try (right; left; reflexivity);
      try rewrite <- H; try assumption;
      inversion IHq2; destruct H3 as [H3 | [H3 | H3]]; inversion H3. 
      Unshelve. auto. auto. auto. auto. auto. auto.
  - (* q1 -> q2 *) destruct_or.
    + (* q1, q2 bool *) left. destruct x1.
      * exists x0. reflexivity.
      * destruct x0; exists true; reflexivity.
    + (* q1 no atoms, q2 bool *) destruct x0.
      * (* b2 = true *) left. destruct (optim q1); exists true;
        try destruct b; reflexivity.
      * (* b2 = false *) destruct_invert (optim q1) IHq1 H.
        left. destruct b; [exists false | exists true]; reflexivity.
    + (* q1 bool, q2 no atoms *) destruct x0.
      * (* b1 = true *) right. assumption.
      * (* b1 = false *) destruct_invert (optim q2) IHq2 H;
        left; exists true; try destruct b; reflexivity.
    + (* q1, q2 no atoms *) destruct_invert (optim q1) IHq1 H;
      destruct (optim q2);
      (* optim q2 bool *) try (inversion IHq2; 
      try destruct H as [H | [ H | H]]; try destruct H3 as [H3 | [H3 | H3]];
      try inversion H; try inversion H3);
      (* else *) right; econstructor; try (right; right; reflexivity);
      try rewrite <- H; try rewrite <- H3; subst; assumption.
  - (* ~q *) destruct_or.
    + (* optim q bool *) left. destruct x0; 
      [exists false | exists true]; reflexivity.
    + (* optim q not bool *) destruct_invert (optim q) IHq H.
  Qed.

(* ################################################################# *)
(** * Solver *)

(** Moving on, we can finally define our SAT-Solver function. *)

(* ================================================================= *)
(** ** Satisfiability *)

(** To this end, let us formally establish the concept of satisfiability. *)

Definition satisfiable (p : form) : Prop :=
  exists (v : valuation), interp v p = true.

Example satisfiable_example1 : satisfiable <{ (x \/ ~y) /\ (~x \/ y) }>.
Proof. exists (x !-> true ;; y !-> true). reflexivity. Qed.

Example satisfiable_example2 : satisfiable <{ ~y -> (x \/ y) }>.
Proof. exists (y !-> true). reflexivity. Qed.

(* ================================================================= *)
(** ** Extracting Identifiers *)

(** We will construct the solver in incremental steps. Let us introduce the
    notion of finit sets of identifiers using the [ListSet] standard library
    implementation. *)

Definition empty_id_set := empty_set id.
Definition id_set_add := set_add id_eq_dec.
Definition id_set_union := set_union id_eq_dec.

Lemma id_set_add_no_effect : forall (x : id) (ids : set id),
  set_In x ids -> id_set_add x ids = ids.
Proof.
  intros x ids H. induction ids as [| y ys IHys].
  - inversion H.
  - simpl. destruct (id_eq_dec x y).
    + reflexivity.
    + f_equal. apply IHys.
      simpl in H. destruct H as [H | H].
      * symmetry in H. apply n in H. inversion H.
      * exact H.
  Qed.

Lemma id_set_add_effect : forall (x : id) (ids : set id),
  ~ set_In x ids -> id_set_add x ids = ids ++ [x].
Proof.
  intros x ids H. induction ids as [| y ys IHys].
  - (* ids = [] *) reflexivity.
  - (* ids = y :: ys *) simpl. destruct (id_eq_dec x y).
    + (* x = y *) subst. simpl in H. apply not_or_and in H.
      destruct H as [H _]. exfalso. apply H. reflexivity.
    + (* x <> y *) simpl in H. apply not_or_and in H.
      destruct H as [H1 H2]. apply IHys in H2. rewrite H2.
      reflexivity.
  Qed.

(** We can now define a function that, given a formula, collects all contained
    identifiers.  *)

Fixpoint collect_ids (p : form) : set id :=
  match p with
  | form_id x => id_set_add x (empty_set id)
  | <{ p /\ q }> | <{ p \/ q }> | <{ p -> q }> => 
    id_set_union (collect_ids p) (collect_ids q)
  | <{ ~p }> => collect_ids p
  | _ => empty_id_set
  end.

(** Of course, it is important to show this function leaves out no identifiers.
    Therefore, let us define when an identifier is contained in a formula [p] 
    and then prove that this is exactly the case when it is in 
    [collect_ids p]. *)

Fixpoint id_in_form (x : id) (p : form) : bool :=
  match p with
  | form_id y => eqb_id x y
  | <{ q1 /\ q2 }> | <{ q1 \/ q2 }> | <{ q1 -> q2 }> => 
    id_in_form x q1 || id_in_form x q2
  | <{ ~q }> => id_in_form x q
  | _ => false
  end.

Ltac destruct_apply :=
  repeat match goal with
  | [ H1 : ?P, H2 : ?P -> ?Q |- _ ] => apply H2 in H1; try exact H1;
    unfold id_set_union;
    try (eapply set_union_intro1 in H1; exact H1);
    (eapply set_union_intro2 in H1; exact H1)
  | [ H : ?H1 || ?H2 = true |- _ ] => rewrite orb_true_iff in H; destruct H
  end.

Lemma id_in_form_iff_in_collect_ids : forall (x : id) (p : form),
  id_in_form x p = true <-> set_In x (collect_ids p).
Proof.
  intros x p. split; intros H;
  induction p as [y | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 |
                  q IHq];
  simpl in *;
  try (rewrite eqb_id_eq in H; left; symmetry; exact H);
  try discriminate H;
  try destruct_apply;
  try (apply set_union_elim in H; destruct H as [H | H]);
  try (apply IHq1 in H; rewrite H; reflexivity);
  try (apply IHq2 in H; rewrite H; rewrite orb_true_r; reflexivity);
  try (destruct H as [H | H]; try (rewrite eqb_id_eq; symmetry; exact H));
  inversion H.
  Qed.

(** That is relevant as only identifiers in the formula influence its
    satisfiability. *)

Lemma id_not_in_form_no_influence : forall (x : id) (v : valuation) (p : form),
  id_in_form x p = false -> 
  interp (x !-> true ;; v) p = interp (x !-> false ;; v) p.
Proof.
  intros x v p H.
  induction p as [y | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 |
                  q IHq];
  simpl in *;
  (* q1 op q2 *) try (rewrite orb_false_iff in H; destruct H as [H1 H2];
    apply IHq1 in H1; apply IHq2 in H2; rewrite H1, H2; reflexivity).
  - (* y *) destruct (id_eq_dec x y).
    + subst. simpl in  H. rewrite eqb_id_refl in H. discriminate H.
    + simpl. rewrite override_neq; try rewrite override_neq;
      try reflexivity; assumption.
  - (* bool *) reflexivity.
  - (* ~q *) apply IHq in H. rewrite H. reflexivity.
  Qed.

(* ================================================================= *)
(** ** Collecting Valuations *)

(** Moving on, when given a set (without duplicates) of identifiers, we want
    to generate a list of all possible valuations that our solver will need
    to check to determine if a formula is satisfiable. *)

Fixpoint collect_vals (ids : set id) : list valuation :=
  match ids with
  | [] => [empty_valuation]
  | x :: xs => 
    let xs_vals := collect_vals xs in
    map (fun y => x !-> true ;; y) xs_vals ++ xs_vals
  end.

Example collect_vals_example : collect_vals [x; y] = 
  [(x !-> true ;; y !-> true) ; (x !-> true) ;
   (y !-> true) ; empty_valuation].
Proof. reflexivity. Qed.

(** With the use of two helper lemmas, we show that for all identifiers, we
    always generate valuations where they are both mapped to [true] and 
    [false]. *)

Lemma empty_valuation_in_collect_vals : forall (ids : set id),
  In empty_valuation (collect_vals ids).
Proof.
  intros ids. induction ids as [| x xs IHxs]; simpl.
  - left. reflexivity.
  - rewrite in_app_iff. right. exact IHxs.
  Qed.

Corollary collect_vals_not_empty : forall (ids : set id),
  collect_vals ids <> [].
Proof.
  intros ids contra1.
  assert (contra2 : ~ In empty_valuation (collect_vals ids)).
  { intros contra2. rewrite contra1 in contra2. 
    simpl in contra2. exact contra2. }
  apply contra2. apply empty_valuation_in_collect_vals.
  Qed.

Ltac backwards_not_eq :=
  repeat match goal with
  | [ H : ?P /\ ?Q |- _ ] => destruct H
  | [ H : In _ (_ ++ _) |- _ ] => rewrite in_app_iff in H
  | [ H : ?P -> ?Q |- ?Q ] => apply H
  | [ |- ?P /\ ?Q ] => split
  | [ H : ?P \/ ?Q |- _ ] => destruct H
  | [ H : In _ (map _ _) |- _ ] => rewrite in_map_iff in H; destruct H; subst
  | [ H1 : (?y !-> _ ;; _) ?x = _, H2 : ?y <> ?x |- _ ] => 
    rewrite override_neq in H1; try assumption
  | [ H : _ = _ |- _ ] => subst
  end.

Lemma collect_vals_all_ids : forall (x : id) (ids : set id),
  set_In x ids <->
  (exists v, In v (collect_vals ids) /\ v x = true) /\
  (exists v, In v (collect_vals ids) /\ v x = false).
Proof.
  intros x ids. split; intros H.
  - (* -> *) split. 
    + generalize dependent x; 
      induction ids as [| y ys IHys]; intros x H.
      * (* ids = [] *) inversion H.
      * (* ids = y :: ys *) simpl in H. destruct H as [H | H].
        -- (* y = x *) subst. simpl.
           destruct (collect_vals ys) as [| v vs] eqn:Evals.
           ++ (* vals = [] *) apply collect_vals_not_empty in Evals.
           inversion Evals.
           ++ (* vals = v :: vs *) exists (x !-> true ;; v). simpl. split.
              ** left. reflexivity.
              ** rewrite override_eq. reflexivity.
        -- (* x in ys *) apply IHys in H. destruct H as [v [H1 H2]].
           simpl. exists (y !-> true ;; v). split.
           ++ rewrite in_app_iff. left. eapply in_map in H1. exact H1.
           ++ destruct (id_eq_dec y x).
              ** subst. rewrite override_eq. reflexivity.
              ** rewrite override_neq; assumption.
    + exists empty_valuation. split.
      * apply empty_valuation_in_collect_vals.
      * reflexivity.
  - (* <- *) induction ids as [| y ys IHys]; destruct H as [[v1 H1] [v2 H2]].
    + (* ids = [] *) simpl in H1. destruct H1 as [[H11 | H11] H12].
      * subst. discriminate H12.
      * inversion H11.
    + (* ids = y :: ys *) simpl in *. destruct (id_eq_dec y x).
      * (* y = x *) left. exact e.
      * (* y <> x *) right. backwards_not_eq;
        try (exists x1; split; assumption);
        try (exists v1; split; assumption);
        try (exists x0; split; assumption);
        exists v2; split; assumption.
  Qed.

(* ================================================================= *)
(** ** Searching Through Valuations *)

(** The final recursive function needed checks if any valuation [v] in a list 
    satisfies a given formula and returns [Some v] if such a [v] is found or
    [None] if not. *)

Fixpoint check_vals (p : form) (l : list valuation) : option valuation :=
  match l with
  | [] => None
  | v :: vs => 
    if interp v p
      then Some v
    else
      check_vals p vs
  end.

(** Sticking all bits together, we can now define our brute-force solver. *)

Definition find_valuation (p : form) : option valuation :=
  let optim_p := optim p in
  let ids := collect_ids optim_p in
  let vals := collect_vals ids in
  check_vals optim_p vals.

Definition solver (p : form) : bool :=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.

(** [solver] is a decision procedure for [satisfiable]. That is, [satisfiable]
    is the concrete problem _P_ on formulas _p_ we are considering and [solver] 
    an algorithm that given a concrete _p_ is able to answer to that problem 
    with yes, i.e., [true],  if _P p_, or no, i.e., [false], if _~P p_. *)

Example solver_pos_example1 : solver <{ (x \/ ~y) /\ (~x \/ y) }> = true.
Proof. reflexivity. Qed.

Example solver_pos_example2 : solver <{ ~y -> (x \/ y) }> = true.
Proof. reflexivity. Qed.

Example solver_pos_example3 : 
  solver <{ ((x -> y) \/ (x /\ ~x)) /\ (y /\ z) }> = true.
Proof. reflexivity. Qed.

Example solver_neg_example1 : solver <{ x /\ ~x }> = false.
Proof. reflexivity. Qed. 

Example solver_neg_example2 : solver <{ (y -> x) /\ ~x /\ y /\ z }> = false.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Soundness *)  

(** Let us verify that the solver does not return false positives, meaning a
    formula is indeed satisfiable if the solver returns [true] for it. *)

Lemma solver_sound : forall (p : form),
  solver p = true -> satisfiable p.
Proof.
  intros p H. unfold solver in H. 
  destruct (find_valuation p) eqn:Epv; [clear H | discriminate H].
  exists v. unfold find_valuation in Epv. unfold check_vals in Epv.
  induction (collect_vals (collect_ids (optim p))) as [| v' vs' IHvs'].
  - discriminate Epv.
  - destruct (interp v' (optim p)) eqn:Eiv'.
    + injection Epv. intros Evv'. subst.
      rewrite <- optim_correct in Eiv'. exact Eiv'.
    + apply IHvs'. exact Epv.
  Qed.

(* ================================================================= *)
(** ** Completeness *) 

(** As final step towards the verification of our decision procedure, we now
    prove that if a formula is satisfiable, then our solver will correctly
    return [true] for it. To this end, we need a few helper lemmas. We start off
    by showing that two valuations identical for all variables contained in a
    formula have the same interpretation. *)

Lemma interp_eq : forall (v v' : valuation) (p : form),
  (forall (x : id), id_in_form x p = true -> v x = v' x) ->
  interp v p = interp v' p.
Proof.
  intros v v' p H.
  induction p as [x | b' | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                  q1 IHq1 q2 IHq2 | q IHq];
  (* q1 op q2 *) try (simpl; f_equal;
    [try (f_equal; apply IHq1); try apply IHq1 | apply IHq2]; 
    intros x Hq; simpl in H;
    assert (Hq1q2 : id_in_form x q1 || id_in_form x q2 = true);
    (* assert proof *) try (rewrite Hq; try rewrite orb_true_r; reflexivity);
    apply H in Hq1q2; exact Hq1q2).
  - (* x *) assert (Hx : id_in_form x x = true). 
    { simpl. rewrite eqb_id_refl. reflexivity. }
    apply H in Hx. simpl. exact Hx.
  - (* bool *) reflexivity.
  - (* ~q *) simpl. f_equal. apply IHq. intros x Hq. 
    apply H. simpl. exact Hq.
  Qed.

(** Next, we want to show that [find_valuation] always considers all
    combinations of mappings for contained variables, i.e., all valuations
    always have an equivalent mapping that is checked by [solver]. We need
    quite a few helper lemmas, however, we unfortunately did not manage to prove
    the lemma itself. *)

Lemma collect_vals_add_preserv : forall (v : valuation) (ids : set id) (x : id),
  In v (collect_vals ids) ->
  In v (collect_vals (id_set_add x ids)).
Proof.
  intros v ids. generalize dependent v.
  induction ids as [| y ys IHys]; intros v x H; simpl in *.
  - (* [] *) destruct H as [H | H].
    + right. left. exact H.
    + inversion H.
  - (* y :: ys *) rewrite in_app_iff in H. destruct H as [H | H].
    + rewrite in_map_iff in H. destruct H as [v' [H1 H2]]. 
      destruct (id_eq_dec x y).
      * subst. simpl. rewrite in_app_iff. left.
        rewrite in_map_iff. exists v'. split.
        -- reflexivity.
        -- assumption.
      * simpl. rewrite in_app_iff. rewrite in_map_iff. left.
        exists v'. split.
        -- assumption.
        -- apply IHys. exact H2.
    + destruct (id_eq_dec x y); simpl; rewrite in_app_iff; 
      right; try apply IHys; exact H.
  Qed.

Lemma collect_vals_union_preserv1 : forall (v : valuation) (ids1 ids2 : set id),
  In v (collect_vals ids1) ->
  In v (collect_vals (id_set_union ids1 ids2)).
Proof.
  intros v ids1 ids2 H. induction ids2 as [| x xs IHxs]; simpl in *.
  - (* [] *) exact H.
  - (* x :: xs *) apply collect_vals_add_preserv. exact IHxs.
  Qed.

Lemma collect_vals_add_overr : forall (v : valuation) (x : id) (ids : set id),
  In v (collect_vals ids) ->
  In (x !-> true ;; v) (collect_vals (id_set_add x ids)).
Proof. 
  intros v x ids. generalize dependent v.
  induction ids as [| y ys IHys]; intros v H; simpl in *.
  - (* [] *) destruct H as [H | H].
    + subst. simpl. left. reflexivity.
    + inversion H.
  - (* y :: ys *) destruct (id_eq_dec x y);
    subst; simpl; rewrite in_app_iff in H; destruct H as [H | H]; simpl;
    try (rewrite in_app_iff; right; apply IHys; assumption);
    try (rewrite in_app_iff; left; rewrite in_map_iff);
    try (rewrite in_map_iff in H; destruct H as [v' [H1 H2]]; subst).
    + rewrite override_shadow. exists v'. split; [reflexivity | assumption].
    + exists v. split; [reflexivity | assumption].
    + exists (x !-> true ;; v'). split;
      [apply override_permute | apply IHys]; assumption.
  Qed.

Lemma collect_vals_union_preserv2 : forall (v : valuation) (ids1 ids2 : set id),
  In v (collect_vals ids2) ->
  In v (collect_vals (id_set_union ids1 ids2)).
Proof.
  intros v ids1 ids2. generalize dependent v.
  induction ids2 as [| x xs IHxs]; intros v H.
  - (* ids2 = [] *) destruct ids1 as [| y ys].
    + (* ids1 = [] *) simpl. exact H.
    + (* ids1 = y :: ys *) simpl. destruct H as [H | H].
      * subst. rewrite in_app_iff. right. 
        apply empty_valuation_in_collect_vals.
      * inversion H.
  - (* ids2 =  x :: xs *) simpl in H. rewrite in_app_iff in H.
    destruct H as [H | H].
    + rewrite in_map_iff in H. destruct H as [v' [H1 H2]].
      subst. simpl. apply collect_vals_add_overr. apply IHxs. exact H2.
    + simpl. apply collect_vals_add_preserv. apply IHxs. exact H.
  Qed.

Lemma collect_vals_contains_combi : 
  forall (v1 v2 : valuation) (ids1 ids2 : set id) (b b' : bool),
    In v1 (collect_vals ids1) -> In v2 (collect_vals ids2) ->
    In (fun x => if b then v1 x else if b' then v2 x else empty_valuation x) 
    (collect_vals (id_set_union ids1 ids2)).
Proof.
  intros v1 v2 ids1 ids2. generalize dependent v2.
  induction ids2 as [| x xs IHxs];
  intros v2 b b' Hv1 Hv2; simpl in *.
  - destruct Hv2 as [Hv2 | Hv2]; destruct b; destruct b'; subst; auto.
    + apply empty_valuation_in_collect_vals.
    + apply empty_valuation_in_collect_vals.
    + inversion Hv2.
    + inversion Hv2.
  - destruct b; destruct b'; 
    rewrite in_app_iff in Hv2; rewrite in_map_iff in Hv2;
    destruct Hv2 as [[v' [Hv21 Hv22]] | Hv2]; subst;
    try apply empty_valuation_in_collect_vals.
    + apply collect_vals_add_preserv.
      apply (IHxs v' true false Hv1) in Hv22. assumption.
    + apply collect_vals_add_preserv.
      apply (IHxs v2 true false Hv1) in Hv2. assumption.
    + apply collect_vals_add_preserv.
      apply (IHxs v' true false Hv1) in Hv22. assumption.
    + apply collect_vals_add_preserv.
      apply (IHxs v2 true false Hv1) in Hv2. assumption.
    + apply collect_vals_add_overr.
      apply (IHxs v' false true Hv1) in Hv22. assumption.
    + apply collect_vals_add_preserv.
      apply (IHxs v2 false true Hv1) in Hv2. assumption.
  Qed.

Lemma v_equiv_in_collect_vals : forall (v : valuation) (p : form),
  exists (v' : valuation),
    (forall (x : id), id_in_form x p = true -> v x = v' x) /\
    In v' (collect_vals (collect_ids p)).
Proof.
  intros v p. induction p as [y | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                                   q1 IHq1 q2 IHq2 | q IHq];
  (* q1 op q2 *) try (destruct IHq1 as [v1 [IHq11 IHq12]];
    destruct IHq2 as [v2 [IHq21 IHq22]]; simpl;
    exists (fun y => 
      if id_in_form y q1 
        then v1 y 
      else if id_in_form y q2 
        then v2 y 
      else empty_valuation y);
    split;
    [intros x H; rewrite orb_true_iff in H; destruct H as [H | H]; rewrite H;
      [apply IHq11; assumption | destruct (id_in_form x q1) eqn:Exq1;
        [apply IHq11 | apply IHq21]; assumption] |
      (* eapply (collect_vals_contains_combi)*) admit]).
  - (* y *) exists (y !-> v y). split.
    + intros x H. simpl in H. rewrite eqb_id_eq in H. subst.
      rewrite override_eq. reflexivity.
    + simpl. destruct (v y).
      * left. reflexivity.
      * right. left. apply functional_extensionality.
        intros x. destruct (id_eq_dec y x).
        -- subst. rewrite override_eq. reflexivity.
        -- rewrite override_neq; [reflexivity | assumption].
  - (* bool *) exists empty_valuation. split.
    + intros x H. inversion H.
    + apply empty_valuation_in_collect_vals.
  - (* ~q *) destruct IHq as [v' [IHq1 IHq2]]. exists v'. split.
    + intros x H. apply IHq1. simpl in H. exact H.
    + simpl. exact IHq2.
  Admitted.

(** Now, assuming [v_equiv_in_collect_vals] holds, we could show the 
    completeness of our solver. *)

Lemma solver_complete : forall (p : form),
  satisfiable p -> solver p = true.
Proof.
  intros p. intros H.
  unfold satisfiable in H. destruct H as [v H].
  unfold solver. unfold find_valuation.
  rewrite optim_correct in H.
  assert (Hv' : exists (v' : valuation),
    (forall (x : id), id_in_form x (optim p) = true -> v x = v' x) /\
    In v' (collect_vals (collect_ids (optim p)))).
  { apply v_equiv_in_collect_vals. }
  destruct Hv' as [v' [Hv'1 Hv'2]].
  apply interp_eq in Hv'1.
  induction (collect_vals (collect_ids (optim p))) as [| h t IHt]; 
  simpl in Hv'2.
  - (* [] *) inversion Hv'2.
  - (* h :: t *) destruct Hv'2 as [Hv'2 | Hv'2].
    + subst. simpl. rewrite H in Hv'1. rewrite <- Hv'1. reflexivity.
    + apply IHt in Hv'2. simpl. 
      destruct (interp h (optim p)); [reflexivity | assumption].
  Qed. 

(** From the soundness and completeness of our solver, it would indeed follow
    that it is a correct decision procedure for [satisfiable]. *)

Theorem solver_decision_procedure : forall (p : form),
  solver p = true <-> satisfiable p.
Proof. split; [apply solver_sound | apply solver_complete]. Qed.
