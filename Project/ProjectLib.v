(** * Library file that should be used for the term projects of introduction
to functional programming 2015. This file is based on SfLib.v of Software
Foundations by Benjamin Pierce and others. *)

(** * From the Coq Standard Library *)

Require Export Bool.
Require Export List.
Export ListNotations. (* Lots of struggle with this: wrong error message
for append caused by this, see https://chatgpt.com/c/674392d2-50f0-8013-bde7-1ee91d8c3c33 *)
Require Export Arith.
Require Export NPeano.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)
Require Export String.

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(** * From Logic.v *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

(**  Identifiers *)

(** We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers. *)

(* Inductive id : Type :=
  Id : nat -> id.

Definition beq_id (x x' : id) : bool :=
  match x, x' with
  | Id y, Id y' => Nat.eqb y y'
  end.
Lemma beq_id_refl : forall x : id,
  true = beq_id x x.
Proof.
  intros x; destruct x as [y]; simpl; symmetry; apply Nat.eqb_refl.
Qed.
Lemma beq_id_eq: forall x x' : id,
  true = beq_id x x' -> x = x'.
Proof.
  intros x x' H; destruct x as [y]; destruct x' as [y']; simpl in H.
  symmetry in H. apply Nat.eqb_eq in H. rewrite H. reflexivity.
Qed. *)

Inductive id : Type :=
    Id (x : string).

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

(* needed for nodup -- removed later *)
(* Theorem id_dec : forall (x y : id),
  {x = y} + {x <> y}.
Proof.
  intros x y. destruct (eqb_id x y) eqn:Exy;
  destruct x as [x]; destruct y as [y]; simpl in Exy.
  - rewrite eqb_eq in Exy. left. f_equal. assumption.
  - rewrite eqb_neq in Exy. right. intros contra. apply Exy.
    injection contra. intros contra'. assumption.
  Qed. *)

Definition is_some {A : Type} (x : option A) :=
  match x with
  | Some _ => true
  | None => false
  end.