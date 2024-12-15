Require Import String.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Lists.ListSet.

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

(** We will later make use of the following lemmas.
    _Source: Pierce et. al. Logical Foundations. Vol. 1 Software Foundations. 
    Electronic textbook, 2024_ *)
    
Lemma override_eq : forall (v : valuation) (x : id) (b : bool),
  (x !-> b ;; v) x = b.
Proof.
  intros v x b. unfold override. 
  rewrite eqb_id_refl. reflexivity.
  Qed.

Theorem override_neq : forall (v : valuation) (x1 x2 : id) (b : bool),
  x1 <> x2 ->
  (x1 !-> b ;; v) x2 = v x2.
Proof.
  intros v x1 x2 b H. unfold override. 
  rewrite <- eqb_id_neq in H. rewrite H.
  reflexivity.
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
(** ** Minimization Property *)

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
(** ** Identifier Extraction *)

(** We will construct the solver in incremental steps. First, we define a
    function that, given a formula, collects all contained identifiers. *)

Definition empty_id_set := empty_set id.
Definition id_set_add := set_add id_eq_dec.
Definition id_set_union := set_union id_eq_dec.

Fixpoint collect_ids (p : form) : set id :=
  match p with
  | form_var x => id_set_add x (empty_set id)
  | <{ p /\ q }> | <{ p \/ q }> | <{ p -> q }> => 
    id_set_union (collect_ids p) (collect_ids q)
  | <{ ~p }> => collect_ids p
  | _ => empty_id_set
  end.

(** Of course, it is important to show this function leaves out no identifiers.
    Therefore, let us define when an identifier is contained in a formula [p] 
    and then prove that this is exactly the case when it is in 
    [collect_ids p].*)

Fixpoint id_in_form (x : id) (p : form) : bool :=
  match p with
  | form_var y => eqb_id x y
  | <{ q1 /\ q2 }> | <{ q1 \/ q2 }> | <{ q1 -> q2 }> => 
    id_in_form x q1 || id_in_form x q2
  | <{ ~q }> => id_in_form x q
  | _ => false
  end.

Lemma id_in_form_iff_in_collect_ids : forall (x : id) (p : form),
  id_in_form x p = true <-> set_In x (collect_ids p).
Proof.
  intros x p. split; intros H;
  induction p as [y | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 |
                  q IHq];
  simpl in *.
  - rewrite eqb_id_eq in H. left. symmetry. exact H.
  - discriminate H.
  - destruct (id_in_form x q1).
    + simpl in *. apply IHq1 in H.
      unfold id_set_union. eapply set_union_intro1 in H.
      exact H.
    + destruct (id_in_form x q2).
      * simpl in H. apply IHq2 in H.
        unfold id_set_union. eapply set_union_intro2 in H.
        exact H.
      * discriminate H.
  - destruct (id_in_form x q1).
    + simpl in *. apply IHq1 in H.
      unfold id_set_union. eapply set_union_intro1 in H.
      exact H. 
    + destruct (id_in_form x q2).
      * simpl in H. apply IHq2 in H.
        unfold id_set_union. eapply set_union_intro2 in H.
        exact H.
      * discriminate H.
  - destruct (id_in_form x q1).
    + simpl in *. apply IHq1 in H.
      unfold id_set_union. eapply set_union_intro1 in H.
      exact H. 
    + destruct (id_in_form x q2).
      * simpl in H. apply IHq2 in H.
        unfold id_set_union. eapply set_union_intro2 in H.
        exact H.
      * discriminate H.
  - apply IHq in H. exact H.
  - destruct H as [H | H].
    + rewrite eqb_id_eq. symmetry. exact H.
    + inversion H.
  - inversion H.
  - apply set_union_elim in H. destruct H as [H | H].
    + apply IHq1 in H. rewrite H. reflexivity.
    + apply IHq2 in H. rewrite H. rewrite orb_true_r. reflexivity.
  - apply set_union_elim in H. destruct H as [H | H].
    + apply IHq1 in H. rewrite H. reflexivity.
    + apply IHq2 in H. rewrite H. rewrite orb_true_r. reflexivity.
  - apply set_union_elim in H. destruct H as [H | H].
    + apply IHq1 in H. rewrite H. reflexivity.
    + apply IHq2 in H. rewrite H. rewrite orb_true_r. reflexivity.
  - apply IHq in H. exact H.
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
    map (fun y => x !-> true ;; y) xs_vals 
    ++ map (fun y => x !-> false ;; y) xs_vals
  end.

Example collect_vals_example : collect_vals [x; y] = 
  [(x !-> true ;; y !-> true) ; (x !-> true ;; y !-> false) ;
   (x !-> false ;; y !-> true) ; (x !-> false ;; y !-> false)].
Proof. reflexivity. Qed.

(** With the use of one helper lemma, we show that for all identifiers, we
    always generate valuations where they are both mapped to [true] and 
    [false]. *)

Lemma collect_vals_not_empty : forall (ids : set id),
  collect_vals ids <> [].
Proof.
  intros ids. induction ids as [| x xs]; 
  intros contra; simpl in contra.
  - discriminate contra.
  - apply app_eq_nil in contra. destruct contra as [contra1 contra2].
    assert (Hlen : length (collect_vals xs) >= 1).
    { destruct (collect_vals xs) as [| v vs].
      - contradiction.
      - simpl. apply le_n_S. apply le_0_n. }
    assert (Hlen_map : length (
            map (fun y : valuation => x !-> true;; y) (collect_vals xs))
            = 0).
    { rewrite contra1. reflexivity. }
    erewrite <- map_length in Hlen. rewrite Hlen_map in Hlen.
    inversion Hlen.
  Qed.

Lemma collect_vals_all_ids : forall (x : id) (ids : set id),
  set_In x ids <->
  (exists v, In v (collect_vals ids) /\ v x = true) /\
  (exists v, In v (collect_vals ids) /\ v x = false).
Proof.
  intros x ids. split; intros H.
  - (* -> *) split; generalize dependent x; 
    induction ids as [| y ys IHys]; intros x H.
    + (* ids = [] *) inversion H.
    + (* ids = y :: ys *) simpl in H. destruct H as [H | H].
      * (* y = x *) subst. simpl.
        destruct (collect_vals ys) as [| v vs] eqn:Evals.
        -- (* vals = [] *) apply collect_vals_not_empty in Evals.
           inversion Evals.
        -- (* vals = v :: vs *) exists (x !-> true ;; v). simpl. split.
           ++ left. reflexivity.
           ++ rewrite override_eq. reflexivity.
      * (* x in ys *) apply IHys in H. destruct H as [v [H1 H2]].
        simpl. exists (y !-> true ;; v). split.
        -- apply in_or_app. left. 
           eapply in_map in H1. exact H1.
        -- destruct (eqb_id y x) eqn:Eyx.
           ++ rewrite eqb_id_eq in Eyx. subst.
              rewrite override_eq. reflexivity.
           ++ rewrite eqb_id_neq in Eyx. rewrite override_neq; assumption.
    + (* ids = [] *) inversion H.
    + (* ids = y :: ys *) simpl in H. destruct H as [H | H].
      * (* y = x *) subst. simpl.
        destruct (collect_vals ys) as [| v vs] eqn:Evals.
        -- (* vals = [] *) apply collect_vals_not_empty in Evals.
           inversion Evals.
        -- (* vals = v :: vs *) exists (x !-> false ;; v). split.
           ++ apply in_or_app. right. simpl. left. reflexivity.
           ++ rewrite override_eq. reflexivity.
      * (* x in ys *) apply IHys in H. destruct H as [v [H1 H2]].
        simpl. exists (y !-> false ;; v). split.
        -- apply in_or_app. right. 
           eapply in_map in H1. exact H1.
        -- destruct (eqb_id y x) eqn:Eyx.
           ++ rewrite eqb_id_eq in Eyx. subst.
              rewrite override_eq. reflexivity.
           ++ rewrite eqb_id_neq in Eyx. rewrite override_neq; assumption.
  - (* <- *) induction ids as [| y ys IHys]; destruct H as [[v1 H1] [v2 H2]].
    + (* ids = [] *) simpl in H1. destruct H1 as [[H11 | H11] H12].
      * subst. discriminate H12.
      * inversion H11.
    + (* ids = y :: ys *) simpl in *.
      destruct (eqb_id y x) eqn:Eyx.
      * (* y = x *) rewrite eqb_id_eq in Eyx. left. exact Eyx.
      * (* y <> x *) rewrite eqb_id_neq in Eyx. right.
        destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
        apply in_app_or in H11. apply in_app_or in H21.
        apply IHys. split.
        -- destruct H11 as [H11 | H11].
           ++ rewrite in_map_iff in H11. destruct H11 as [v [H111 H112]].
              subst. exists v. split.
              ** assumption.
              ** rewrite override_neq in H12; assumption.
           ++ rewrite in_map_iff in H11. destruct H11 as [v [H111 H112]].
              subst. exists v. split.
              ** assumption.
              ** rewrite override_neq in H12; assumption.
        -- destruct H21 as [H21 | H21].
           ++ rewrite in_map_iff in H21. destruct H21 as [v [H211 H212]].
              subst. exists v. split.
              ** assumption.
              ** rewrite override_neq in H22; assumption.
           ++ rewrite in_map_iff in H21. destruct H21 as [v [H211 H212]].
              subst. exists v. split.
              ** assumption.
              ** rewrite override_neq in H22; assumption.
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

(** Let us verify that the solver doesn't return false positives, meaning a
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
    return [true] for it. *)

Lemma interp_eq : forall (v v' : valuation) (p : form),
  (forall (x : id), id_in_form x p = true -> v x = v' x) ->
  interp v p = interp v' p.
Proof.
  intros v v' p H.
  induction p as [x | b' | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                  q1 IHq1 q2 IHq2 | q IHq].
  - (* x *) assert (Hx : id_in_form x x = true). 
    { simpl. rewrite eqb_id_refl. reflexivity. }
    apply H in Hx. simpl. exact Hx.
  - (* bool *) reflexivity.
  - (* q1 /\ q2 *) simpl. f_equal.
    + apply IHq1. intros x Hq1.
      simpl in H.
      assert (Hq1q2 : id_in_form x q1 || id_in_form x q2 = true).
      { rewrite Hq1. reflexivity. }
      apply H in Hq1q2. exact Hq1q2.
    + apply IHq2. intros x Hq2.
      simpl in H.
      assert (Hq1q2 : id_in_form x q1 || id_in_form x q2 = true).
      { rewrite Hq2. rewrite orb_true_r. reflexivity. }
      apply H in Hq1q2. exact Hq1q2.
  - (* q1 \/ q2 *) simpl. f_equal.
    + apply IHq1. intros x Hq1.
      simpl in H.
      assert (Hq1q2 : id_in_form x q1 || id_in_form x q2 = true).
      { rewrite Hq1. reflexivity. }
      apply H in Hq1q2. exact Hq1q2.
    + apply IHq2. intros x Hq2.
      simpl in H.
      assert (Hq1q2 : id_in_form x q1 || id_in_form x q2 = true).
      { rewrite Hq2. rewrite orb_true_r. reflexivity. }
      apply H in Hq1q2. exact Hq1q2.
  - (* q1 -> q2 *) simpl. f_equal.
    + f_equal. apply IHq1. intros x Hq1.
      simpl in H.
      assert (Hq1q2 : id_in_form x q1 || id_in_form x q2 = true).
      { rewrite Hq1. reflexivity. }
      apply H in Hq1q2. exact Hq1q2.
    + apply IHq2. intros x Hq2.
      simpl in H.
      assert (Hq1q2 : id_in_form x q1 || id_in_form x q2 = true).
      { rewrite Hq2. rewrite orb_true_r. reflexivity. }
      apply H in Hq1q2. exact Hq1q2.
  - (* ~q *) simpl. f_equal. 
    apply IHq. intros x Hq. apply H. 
    simpl. exact Hq.
  Qed.

Lemma testtest : forall (v1 v2 : valuation) (ids1 ids2 : set id),
  In v1 (collect_vals ids1) -> In v2 (collect_vals ids2) ->
  In (fun x => if existsb (eqb_id x) ids1 then v1 x else v2 x) 
    (collect_vals (id_set_union ids1 ids2)).
Proof. Admitted.

Lemma existsb_eqb_iff_in : forall (x : id) (l : list id),
  existsb (eqb_id x) l = true <-> In x l.
Proof.
  intros x l. split; intros H; induction l as [| hd tl IHtl].
  - discriminate H.
  - simpl in *. destruct (eqb_id x hd) eqn:Exhd.
    + left. rewrite eqb_id_eq in Exhd. symmetry. exact Exhd.
    + right. simpl in H. apply IHtl in H. exact H.
  - inversion H.
  - simpl in *; destruct (eqb_id x hd) eqn:Efi; destruct H as [H | H];
    try reflexivity.
    + rewrite eqb_id_neq in Efi. symmetry in H. 
      apply Efi in H. inversion H.
    + apply IHtl in H. rewrite H. reflexivity.
  Qed.

Lemma v_equiv_in_collect_vals : forall (v : valuation) (p : form),
  exists (v' : valuation), 
    In v' (collect_vals (collect_ids p)) /\ 
    (forall (x : id), id_in_form x p = true -> v x = v' x).
Proof. 
  intros v p. induction p as [x | b' | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                              q1 IHq1 q2 IHq2 | q IHq].
  - (* x *) assert (Hb : exists (b : bool), v x = b).
    { destruct (v x); [exists true | exists false]; reflexivity. }
    destruct Hb as [b Hb]. 
    exists (x !-> b). split.
    + destruct b.
      * (* true *) simpl. left. reflexivity.
      * (* false *) simpl. right. left. reflexivity.
    + intros x' Hin.
      simpl in Hin. rewrite eqb_id_eq in Hin. subst.
      rewrite override_eq. reflexivity.
  - (* bool *) exists empty_valuation. split.
    + simpl. left. reflexivity.
    + intros x Hin. discriminate Hin.
  - (* q1 /\ q2 *) simpl.
    destruct IHq1 as [v1 [IHq11 IHq12]]. destruct IHq2 as [v2 [IHq21 IHq22]].
    exists 
      (fun y => if existsb (eqb_id y) (collect_ids q1) then v1 y else v2 y). 
    split.
    + apply testtest; assumption.
    + intros x H. rewrite orb_true_iff in H. destruct H as [H | H].
      * destruct (existsb (eqb_id x) (collect_ids q1)) eqn:Ee1.
        -- apply IHq12. assumption.
        -- assert (contra : ~ In x (collect_ids q1)).
           { intros contra. rewrite <- existsb_eqb_iff_in in contra.
             rewrite Ee1 in contra. discriminate contra. }
           rewrite <- id_in_form_iff_in_collect_ids in contra.
           apply contra in H. inversion H.
      * destruct (existsb (eqb_id x) (collect_ids q1)) eqn:Ee1.
        -- rewrite existsb_eqb_iff_in in Ee1.
           rewrite <- id_in_form_iff_in_collect_ids in Ee1.
           apply IHq12 in Ee1. assumption.
        -- destruct (existsb (eqb_id x) (collect_ids q2)) eqn:Ee2.
           ++ apply IHq22 in H. assumption.
           ++ assert (contra : ~ In x (collect_ids q2)).
              { intros contra. rewrite <- existsb_eqb_iff_in in contra.
                rewrite Ee2 in contra. discriminate contra. }
              rewrite <- id_in_form_iff_in_collect_ids in contra.
              apply contra in H. inversion H.
    - (* q1 \/ q2 *)  
  Admitted.

(* Lemma test : forall (v : valuation) (p : form) (b : bool),
  interp v p = b ->
  exists (v' : valuation), In v' (collect_vals (collect_ids p)) /\
  interp v p = interp v' p.
Proof.
  intros v p b H. induction p as [x | b' | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                                  q1 IHq1 q2 IHq2 | q IHq].
  - (* x *) destruct b.
    + (* true *) exists (x !-> true). split.
      * simpl. left. reflexivity.
      * rewrite H. simpl. rewrite override_eq. reflexivity.
    + (* false *) exists (x !-> false). split.
      * simpl. right. left. reflexivity.
      * rewrite H. simpl. rewrite override_eq. reflexivity.
  - (* bool *) exists empty_valuation. split.
    + simpl. left. reflexivity.
    + simpl. reflexivity.
  - (* q1 /\ q2 *) simpl.
  Admitted. *)

Lemma solver_complete : forall (p : form),
  satisfiable p -> solver p = true.
Proof.
  intros p. intros H.
  unfold satisfiable in H. destruct H as [v H].
  unfold solver. unfold find_valuation.
  rewrite optim_correct in H.
  induction (optim p) as [x | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                          q1 IHq1 q2 IHq2 | q IHq]; simpl.
  - (* x *) rewrite override_eq. reflexivity.
  - (* bool *) destruct b.
    + (* true *) reflexivity.
    + (* false *) discriminate H.
  - (* q1 /\ q2 *) simpl in H. rewrite andb_true_iff in H.
    destruct H as [H1 H2].
    destruct (check_vals q1 (collect_vals (collect_ids q1))) as [v1 |] eqn:E1.
    + (* Some v1 *) destruct (check_vals q2 (collect_vals (collect_ids q2))) 
      as [v2 | ] eqn:E2.
      * (* Some v2 *) destruct (collect_vals (collect_ids q1)) as [| h1 t1].
        -- (* [] *) discriminate E1.
        -- (* h1 :: t1 *) simpl in E1. unfold check_vals in E1. (* Some v2 *) admit.
      * (* None *) apply IHq2 in H2. discriminate H2. 
    + (* None *) apply IHq1 in H1. discriminate H1.
