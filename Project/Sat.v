Require Import ProjectLib.

(* ########################### *)
(** * Syntax *)
(* ########################### *)

(** ** Abstract Syntax Tree *)

Inductive form : Type :=
    | form_var (x : id)
    | form_bool (b : bool)
    | form_conj (p : form) (q : form)
    | form_disj (p : form) (q : form)
    | form_impl (p : form) (q : form)
    | form_neg (p : form).

(** ** Concrete Syntax *)

(* difficulty: remember notation as always in template usually *)
Coercion form_var : id >-> form.
Declare Custom Entry form. (* difficult finding out why this is more powerful compared to Declare Scope *)
Notation "<{ p }>" := p (p custom form at level 99).
Notation "( p )" := p (in custom form, p at level 90). (* don't really understand difference to previous lign *)
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
(* TODO: check precedences *)

Definition x : id := Id "x".
Definition y : id := Id "y".
Definition z : id := Id "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(** ** Examples *)

Definition syntax_example : form :=
    <{ ~x \/ true \/ z /\ y -> z }>.
Unset Printing Notations.
Print syntax_example.
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

(* ########################### *)
(** * Semantics *)
(* ########################### *)

(** ** Valuation *)

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

(** ** Interpreter *)

Fixpoint interp (V : valuation) (p : form) : bool :=
    match p with
    | form_var x => V x
    | <{ true }> => true
    | <{ false }> => false
    | <{ p /\ q }> => (interp V p) && (interp V q) (* 1st argument is fully computed to true or false before function is applied (Stlc) *)
    | <{ p \/ q }> => (interp V p) || (interp V q)
    | <{ p -> q }> => (negb (interp V p)) || (interp V q)
    | <{ ~p }> => negb (interp V p)
    end.

(* ########################### *)
(** * Optimizer *)
(* ########################### *)

(* Difficulty: first wrote all cases for and, or and impl directly without pattern matching on the optimized version, leaving out potential for
   optimization and therefore trying the apply_optim fixpoint which is not possible in Coq. *)
(* Now bottom-up approach *)
Fixpoint optim (p : form) : form :=
    match p with
    | <{ q /\ q' }> =>
        let q_opt := optim q in 
        let q'_opt := optim q' in
        match q_opt, q'_opt with
        | <{ true }>, _ => q'_opt
        | _, <{ true }> => q_opt
        | <{ false }>, _ => <{ false }>
        | _, <{ false }> => <{ false }>
        | _, _ => <{ q_opt /\ q'_opt }>
        end
    | <{ q \/ q' }> =>
        let q_opt := optim q in
        let q'_opt := optim q' in
        match q_opt, q'_opt with
        | <{ true }>, _ => <{ true }>
        | _, <{ true }> => <{ true }>
        | <{ false }>, _ => q'_opt
        | _, <{ false }> => q_opt
        | _, _ => <{ q_opt \/ q'_opt }>
        end
    | <{ q -> q' }> =>
        let q_opt := optim q in
        let q'_opt := optim q' in
        match q_opt, q'_opt with
        | <{ true }>, _ => q'_opt
        | _, <{ true }> => <{ true }>
        | <{ false }>, _ => <{ true }>
        | _, <{ false }> => <{ ~q_opt }>
        | _, _ => <{ q_opt -> q'_opt }>
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

(* Difficulty: fixpoint termination => doesn't work *)
(* Fixpoint apply_optim (p : form) :=
    let p_opt := optim p in
    if eqb_form p p_opt
        then p
    else
        apply_optim (p_opt). *)

(** ** Correctness *)

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
    [ reflexivity |
      destruct q; try destruct b; reflexivity]. 

(* TODO: make look nicer *)
Theorem optim_correct : forall V p,
    interp V p = interp V (optim p).
Proof.
    induction p as [x | b | q IHq q' IHq' | q IHq q' IHq' | q IHq q' IHq' |
                    q IHq]; 
    try reflexivity;
    simpl; destruct (optim q) as [x | b | q_opt1 q_opt2 | q_opt1 q_opt2 |
                                    q_opt1 q_opt2 | q_opt];
    try destruct_if b (optim q');
    try destruct b;
    try (rewrite IHq; reflexivity);
    destruct (optim q');
    try (simpl in *; rewrite IHq, IHq'; reflexivity);
    try destruct b;
    simpl in *; rewrite IHq, IHq'; auto.
    Qed.

(** ** Completeness *)

(* TODO: rewrite as equations ? *)
Fixpoint contains_no_atoms (f : form) : bool :=
    match f with
    | form_var _ => true
    | <{ p /\ q }> | <{ p \/ q }> | <{ p -> q }> => 
        contains_no_atoms p && contains_no_atoms q
    | <{ ~p }> => contains_no_atoms p
    | _ => false
    end.

(* underlines optimizer syntax-driven *)
Lemma optim_no_atoms_same : forall (f : form),
    contains_no_atoms f = true -> optim f = f.
Proof.
    intros f H.
    induction f as [x | b | p IHp q IHq | p IHp q IHq | 
                            p IHp q IHq | p IHp];
    simpl in *; 
    try (apply andb_prop in H; destruct H as [Hp Hq];
         apply IHp in Hp; apply IHq in Hq;
         rewrite Hp; rewrite Hq; simpl).
    - reflexivity.
    - reflexivity.
    Admitted.

Definition minimal_form (f : form) : Prop :=
    (exists b, f = form_bool b) \/ contains_no_atoms f = true.

(* helper lemma *)
Lemma if_same : forall (X : Type) (b : bool) (x : X),
    (if b then x else x) = x.
Proof. intros X b x. destruct b; reflexivity. Qed.

(* Idea: theorem proving that this is the simplest form 
    check if predicate valid, with predicate being certain constructs not contained in form 
    i.e. either only true or false or no atoms (true or false) contained *)
(* TODO: reduce proof size further *)
(* ++ 
TODO!!! 
++ 
check if proof length can be reduced further by using optim_same_no_atoms lemma *)
Theorem optim_minimizes : forall (f : form),
    minimal_form (optim f).
Proof.
    intros f.
    induction f as [x | b | p IHp q IHq | p IHp q IHq | 
                            p IHp q IHq | p IHp];
    unfold minimal_form;
    (* form_bool b *) try (right; reflexivity);
    (* form_var x *) try (left; exists b; reflexivity).
    - destruct IHp as [IHp | IHp]; destruct IHq as [IHq | IHq];
      simpl;
      try (destruct IHp as [bp IHp]; rewrite IHp; clear IHp;
           destruct bp);
      try (destruct IHq as [bq IHq]; rewrite IHq; clear IHq;
           destruct bq);
      try (left; exists true; reflexivity);
      try (left; try destruct (optim q); try destruct (optim p); 
           try rewrite if_same; exists false; reflexivity);
      right; try destruct (optim q); try destruct (optim p);
      try discriminate; simpl in *;
      try rewrite IHp; try rewrite IHq;
      try reflexivity; assumption.
    - destruct IHp as [IHp | IHp]; destruct IHq as [IHq | IHq];
      simpl;
      try (destruct IHp as [bp IHp]; rewrite IHp; clear IHp;
           destruct bp);
      try (destruct IHq as [bq IHq]; rewrite IHq; clear IHq;
           destruct bq);
      try (left; try destruct (optim p);
           try rewrite if_same; exists true; reflexivity);
      try (left; try destruct (optim p); exists false; reflexivity);
      right; try destruct (optim q); try destruct (optim p);
      try discriminate; simpl in *;
      try rewrite IHp; try rewrite IHq;
      reflexivity.
    - destruct IHp as [IHp | IHp]; destruct IHq as [IHq | IHq];
      simpl;
      try (destruct IHp as [bp IHp]; rewrite IHp; clear IHp;
           destruct bp);
      try (destruct IHq as [bq IHq]; rewrite IHq; clear IHq;
           destruct bq);
      try (left; try destruct (optim p); try destruct (optim q);
           try rewrite if_same; exists true; reflexivity);
      try (left; exists false; reflexivity);
      right; try destruct (optim q); try destruct (optim p);
      try discriminate; simpl in *;
      try rewrite IHp; try rewrite IHq;
      reflexivity.
    - destruct IHp as [IHp | IHp].
        + left. destruct IHp as [bp IHp]. simpl. rewrite IHp.
          destruct bp; [exists false | exists true]; reflexivity.
        + right. simpl. destruct (optim p); 
          simpl in *; try discriminate; assumption.
    Qed.

