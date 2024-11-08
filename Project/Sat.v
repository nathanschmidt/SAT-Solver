Require Import ProjectLib.

(* Syntax *)
Inductive form : Type :=
    | form_var (x : id)
    | form_bool (b : bool)
    | form_conj (p : form) (q : form)
    | form_disj (p : form) (q : form)
    | form_impl (p : form) (q : form)
    | form_neg (p : form).

(* Concrete Syntax *)
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

(* Semantics *)
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

Fixpoint interp (V : valuation) (p : form) : bool :=
    match p with
    | form_var x => V x
    | <{ true }> => true
    | <{ false }> => false
    | <{ p /\ q }> => (interp V p) && (interp V q)
    | <{ p \/ q }> => (interp V p) || (interp V q)
    | <{ p -> q }> => (negb (interp V p)) || (interp V q)
    | <{ ~p }> => negb (interp V p)
    end.

Fixpoint optim (p : form) : form :=
    match p with
    | <{ q /\ true }> => optim q
    | <{ true /\ q }> => optim q
    | <{ _ /\ false }> => <{ false }>
    | <{ false /\ _ }> => <{ false }>
    | <{ q /\ q' }> =>
        let q_opt := optim q in 
        let q'_opt := optim q' in
        <{ q_opt /\ q'_opt }>
    | <{ _ \/ true }> => <{ true }>
    | <{ true \/ _ }> => <{ true }>
    | <{ q \/ false }> => optim q
    | <{ false \/ q }> => optim q
    | <{ q \/ q' }> =>
        let q_opt := optim q in
        let q'_opt := optim q' in
        <{ q_opt \/ q'_opt }>
    | <{ true -> q }> => optim q
    | <{ _ -> true }> => <{ true }>
    | <{ false -> _ }> => <{ true }>
    (* | <{ q -> false }> => optim <{ ~q }> *)
    | <{ q -> q' }> =>
        let q_opt := optim q in
        let q'_opt := optim q' in
        <{ q_opt -> q'_opt }>
    | <{ ~true }> => <{ false }>
    | <{ ~false }> => <{ true }>
    | <{ ~q }> =>
        let q_opt := optim q in
        <{ ~q_opt }>
    | _ => p
    end.

Theorem optim_correct : forall V p,
    interp V p = interp V (optim p).
Proof.
    (* TODO *) Admitted.

(* Difficulty: fixpoint termination => doesn't work *)
(* Fixpoint apply_optim (p : form) :=
    let p_opt := optim p in
    if eqb_form p p_opt
        then p
    else
        apply_optim (p_opt). *)
