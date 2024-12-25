Fixpoint collect_vals (ids : set id) : list (list (id * bool)) :=
  match ids with
  | [] => [[]]
  | x :: xs => 
    let vals' := collect_vals xs in
    map (fun v => (x, true) :: v) vals' ++ map (fun v => (x, false) :: v) vals'
  end.

Example collect_vals_example : collect_vals [x; y] = 
  [[(x, true); (y, true)]; [(x, true); (y, false)] ;
    [(x, false); (y, true)]; [(x, false); (y, false)]].
Proof. reflexivity. Qed.

Example collect_vals_union : collect_vals (id_set_union [y; x] [y; z]) =
  [[(y, true); (x, true); (z, true)]; [(y, true); (x, true); (z, false)];
  [(y, true); (x, false); (z, true)]; [(y, true); (x, false); (z, false)];
  [(y, false); (x, true); (z, true)]; [(y, false); (x, true); (z, false)];
  [(y, false); (x, false); (z, true)]; [(y, false); (x, false); (z, false)]].
Proof. reflexivity. Qed.

Lemma test : forall (l1 l2 : list (id * bool)) (ids1 ids2 : set id),
  In l1 (collect_vals ids1) -> In l2 (collect_vals ids2) ->
  In (l1 ++ filter (fun v2 => existsb (fun v1 => negb (eqb_id (fst v1) (fst v2))) l1) l2)
  (collect_vals (id_set_union ids1 ids2)).
Proof.
  intros l1 l2 ids1 ids2.
  generalize dependent ids1. generalize dependent l2. generalize dependent l1.
  induction ids2; intros l1 l2 ids1 H1 H2; simpl in *.
  - destruct H2.
    + subst. simpl. rewrite app_nil_r. exact H1.
    + inversion H.
  - rewrite in_app_iff in H2. destruct H2 as [H2 | H2]; rewrite in_map_iff in H2;
    destruct H2 as [x [H21 H22]].
    + subst. eapply IHids2 in H22.
      * simpl. destruct (existsb (fun v1 : id * bool => negb (eqb_id (fst v1) a)) l1).
        -- simpl.
  Admitted.

Fixpoint pairs_to_val (l : list (id * bool)) : valuation :=
  match l with
  | [] => empty_valuation
  | v :: vs => override (pairs_to_val vs) (fst v) (snd v)
  end.

Example pairs_to_val_example : map pairs_to_val (collect_vals [x; y]) =
  [(x !-> true ;; y !-> true); (x !-> true ;; y !-> false);
    (x !-> false ;; y !-> true); (x !-> false ;; y !-> false)].
Proof. reflexivity. Qed.

(* Fixpoint interp' (l : list (id * bool)) (p : form) : bool :=
  match p with
  | form_id x =>
    match find (fun v => eqb_id (fst v) x) l with
    | Some v => snd v
    | None => false
    end
  | <{ true }> => true
  | <{ false }> => false
  | <{ p /\ q }> => (* both need to hold *) (interp' l p) && (interp' l q)
  | <{ p \/ q }> => (* one needs to hold *) (interp' l p) || (interp' l q)
  | <{ p -> q }> => (* equiv ~p \/ q *) (negb (interp' l p)) || (interp' l q)
  | <{ ~p }> => negb (interp' l p)
  end.

Lemma interp_iff_interp' : forall (l : list (id * bool)) (p : form) (b : bool),
  interp (pairs_to_val l) p = b <-> interp' l p = b.
Proof.
  intros l p b. split; intros H; induction p.
  - simpl in *. destruct (find (fun v : id * bool => eqb_id (fst v) x0) l).
    + simpl.

Example interp'_example1 : 
  interp' [] <{ x \/ (y /\ z) \/ (false -> x) }> = true.
Proof. reflexivity. Qed.

Example interp'_example2 :
  interp' [(x, true); (y, false); (z, true)] <{ x -> ((x \/ y) /\ (~z)) }> 
  = false.
Proof. reflexivity. Qed. *)

Fixpoint check_vals (p : form) (l : list (list (id * bool))) : option valuation :=
  match l with
  | [] => None
  | v :: vs =>
    let v' := pairs_to_val v in
    if interp v' p
      then Some v'
    else
      check_vals p vs
  end.

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

Lemma solver_sound : forall (p : form),
  solver p = true -> satisfiable p.
Proof.
  intros p H. unfold solver in H. 
  destruct (find_valuation p) eqn:Epv; [clear H | discriminate H].
  exists v. unfold find_valuation in Epv. unfold check_vals in Epv.
  induction (collect_vals (collect_ids (optim p))) as [| v' vs' IHvs'].
  - discriminate Epv.
  - destruct (interp (pairs_to_val v') (optim p)) eqn:Eiv'.
    + injection Epv. intros Evv'. subst.
      rewrite <- optim_correct in Eiv'. exact Eiv'.
    + apply IHvs'. exact Epv.
  Qed.

Lemma interp_eq : forall (v v' : valuation) (p : form),
  (forall (x : id), id_in_form x p = true -> v x = v' x) ->
  interp v p = interp v' p.
Proof.
  intros v v' p H.
  induction p as [x | b' | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                  q1 IHq1 q2 IHq2 | q IHq];
  (* q1 op q2 *) try (simpl; f_equal;
    [try (f_equal; apply IHq1); try apply IHq1 | apply IHq2]; intros x Hq; simpl in H;
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

Lemma v_equiv_in_collect_vals : forall (v : valuation) (p : form),
  exists (l : list (id * bool)),
    In l (collect_vals (collect_ids p)) /\
    interp v p = interp (pairs_to_val l) p.
Proof.
  intros v p. induction p as [y | b | q1 IHq1 q2 IHq2 | q1 IHq1 q2 IHq2 | 
                                   q1 IHq1 q2 IHq2 | q IHq].
  - (* y *) exists [(y, v y)]. split.
    + simpl. destruct (v y).
      * left. reflexivity.
      * right. left. reflexivity.
    + simpl. rewrite override_eq. reflexivity.
  - (* b *) simpl. exists []. split; try left; reflexivity.
  - (* q1 /\ q2 *) destruct IHq1 as [l1 [IHq11 IHq12]].
    destruct IHq2 as [l2 [IHq21 IHq22]]. simpl.
    rewrite IHq12. rewrite IHq22.
    exists (l1 ++ l2).
    split.
    + 
     intros x H. rewrite orb_true_iff in H. destruct H.
      * simpl. admit.
    + Admitted.