(* coq platform docs coq.inria.fr/platform-docs *)

Require Import ProjectLib. (* checked if export help with Bas, didn't make a difference *)
Import List. (* dont' know why necessary, otherwise strange error.... *)

(* TODO: change all functions to use (f : form), not (p : form) *)

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

(* from Maps chapter of LF *)
Lemma update_eq : forall (V : valuation) (x : id) (b : bool),
  (x !-> b ; V) x = b.
Proof.
  intros V x b. unfold override. 
  rewrite eqb_id_refl. reflexivity.
  Qed.

(** ** Interpreter *)

Fixpoint interp (V : valuation) (f : form) : bool :=
    match f with
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

Inductive contains_no_atoms' : form -> Prop :=
  | cna_var : forall (x : id),
      contains_no_atoms' <{ x }>
  | cna_cdi : forall (f p q : form),
      f = <{ p /\ q }> \/ f = <{ p \/ q }> \/ f = <{ p -> q }> ->
      contains_no_atoms' p ->
      contains_no_atoms' q ->
      contains_no_atoms' f
  | cna_neg : forall (p : form),
      contains_no_atoms' p ->
      contains_no_atoms' <{ ~p }>.

(* TODO: Fixpoint and inductive equivalent or reprove optim_minimizes *)

(* underlines optimizer syntax-driven *)
Lemma optim_no_atoms_same : forall (f : form),
    contains_no_atoms' f -> optim f = f.
Proof.
  intros f H. induction H as [x | f p q Hf Hp IHp Hq IHq | p Hp IHp].
  - reflexivity.
  - destruct Hf as [Hf | [Hf | Hf]]; rewrite Hf; clear Hf;
    simpl; rewrite IHp; clear IHp; rewrite IHq; clear IHq;
    inversion Hp as [xp Hxp | pf p1 p2 Hpf Hp1 Hp2 | p' Hp'];
    inversion Hq as [xq Hxq | qf q1 q2 Hqf Hq1 Hq2 | q' Hq'];
    try destruct Hpf as [Hpf | [Hpf | Hpf]];
    try destruct Hqf as [Hqf | [Hqf | Hqf]]; subst; reflexivity.
  - simpl. rewrite IHp. destruct p; try reflexivity.
    inversion Hp. destruct H as [H | [H | H]]; inversion H.
  Qed.

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

(* ########################### *)
(** * Solver *)
(* ########################### *)

(** ** Satisfiability *)

Definition satisfiable (p : form) : Prop :=
  exists (V : valuation), interp V p = true.

Lemma satisfiable_test1 : satisfiable <{ (x \/ ~y) /\ (~x \/ y) }>.
Proof. exists (x !-> true ; y !-> true). reflexivity. Qed.

Lemma satisfiable_test2 : satisfiable <{ ~y -> (x \/ y) }>.
Proof. exists (y !-> true). reflexivity. Qed.

(* Don't care about order of vars in resulting list, just need to be all unique *)
Fixpoint ids_union (l1 l2 : list id) :=
  match l1 with
  | [] => l2
  | hd :: tl =>
    if (List.find (fun x => eqb_id x hd) l2)
      then ids_union tl l2
    else
      ids_union tl (hd :: l2)
  end.

Example ids_union_example1 : ids_union [x; y; z] [x; y] = [z; x; y].
Proof. reflexivity. Qed.

Example ids_union_example2 : 
  ids_union [x; y; z] [Id "a"; Id "b"] = [z; y; x; Id "a"; Id "b"].
Proof. reflexivity. Qed.

(** ** Solver *)

(* TODO: Think about if want to prove some properties showing ids_union correct *)

(* Helper functions *)
Fixpoint collect_vars (f : form) : list id :=
  match f with
  | form_var x => [x]
  | <{ p /\ q }> | <{ p \/ q }> | <{ p -> q }> => 
    ids_union (collect_vars p) (collect_vars q)
  | <{ ~p }> => collect_vars p
  | _ => []
  end.

Fixpoint collect_valuations (l : list id) (acc : list valuation) : list valuation :=
  match l with
  | [] => acc
  | x :: xs => collect_valuations xs ((map (fun v => x !-> true ; v) acc) ++ acc)
  end.

Fixpoint check_valuations (f : form) (l : list valuation) : option valuation :=
  match l with
  | [] => None
  | v :: vs => 
    if interp v f
      then Some v
    else
      check_valuations f vs
  end.

(* Abandonned idea: directly collect valuations instead of variables
   Problem: in e.g. (x \/ x) for the left and the right we get the same valuations,
   but we combine them to actually 4 instead of just 2 valuations.
   For success that's fine I guess, that makes us check twice the same stuff
   even if no valuation exists. 
   Considered sets, but didn't want to include extra library, so implemented
   this list merging function *)
Definition find_valuation (f : form) : option valuation :=
  let optim_f := optim f in
  let vars := collect_vars optim_f in
  let valuations := collect_valuations vars [empty_valuation] in
  (* doesn't work as interp keeps no trace of v but just says true or false*)
  (* find is_some (map (fun v => interp v optim_f) valuations). *)
  (* Also following solutions better runtime as stops as soon as one found *)
  check_valuations optim_f valuations.

Lemma find_valuation_disj : forall (p q : form) (v : valuation),
  find_valuation <{ p /\ q }> = Some v ->
  exists (vp vq : valuation), 
    find_valuation p = Some vp /\ find_valuation q = Some vq.
Proof.
  intros p q v H.

Definition solver (f : form) : bool :=
  match find_valuation f with
  | Some _ => true
  | None => false
  end.

(* TODO (in report?): exercise 2.6 *)

Example solver_pos_test1 : solver <{ (x \/ ~y) /\ (~x \/ y) }> = true.
Proof. reflexivity. Qed.

Example solver_pos_test2 : solver <{ ~y -> (x \/ y) }> = true.
Proof. reflexivity. Qed.

Example solver_pos_test3 : solver <{ ((x -> y) \/ (x /\ ~x)) /\ (y /\ z) }> = true.
Proof. reflexivity. Qed.

Example solver_neg_test1 : solver <{ x /\ ~x }> = false.
Proof. reflexivity. Qed. 

Example solver_neg_test2 : solver <{ (y -> x) /\ ~x /\ y /\ z }> = false.
Proof. reflexivity. Qed.

Lemma solver_sound : forall (f : form),
  solver f = true -> satisfiable f.
Proof.
  intros f H. unfold solver in H. 
  destruct (find_valuation f) eqn:Efv; [clear H | discriminate H].
  exists v. unfold find_valuation in Efv.
  unfold check_valuations in Efv.
  (* We know check_valuations returns Some v, but it only does so
     if interp v f = true.
     Therefore, given list of valuations, either the head is the 
     returned valuation or some valuation in the tail.
     Correctness of encapsulated functions doesn't matter,
     can just do case distinction and see them as black box *)
  induction 
  (collect_valuations (collect_vars (optim f)) [empty_valuation])
  as [| v' vs' IHvs'].
  - discriminate Efv.
  - destruct (interp v' (optim f)) eqn:Eiv'.
    + injection Efv. intros Evv'. subst.
      rewrite <- optim_correct in Eiv'. exact Eiv'.
    + apply IHvs'. exact Efv.
  Qed.
