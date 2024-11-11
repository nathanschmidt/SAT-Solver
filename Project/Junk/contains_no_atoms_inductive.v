(* Quite some blow-up in proof*)
Inductive contains_no_atoms : form -> Prop :=
    | cna_var : forall x,
        contains_no_atoms (form_var x)
    | cna_cdi : forall f p q,
        f = <{ p /\ q }> \/ f = <{ p \/ q }> \/ f = <{ p -> q }> ->
        contains_no_atoms p ->
        contains_no_atoms q ->
        contains_no_atoms f
    | cna_neg : forall p,
        contains_no_atoms p ->
        contains_no_atoms <{ ~p }>.

Theorem optim_minimizes : forall (f : form),
    minimal_form (optim f).
Proof.
    intros f.
    induction f as [x | b | p IHp q IHq | p IHp q IHq | 
                            p IHp q IHq | p IHp];
    unfold minimal_form.
    - right. constructor.
    - left. exists b. reflexivity.
    - destruct IHp as [IHp | IHp].
        + destruct IHq as [IHq | IHq].
            * left. simpl. 
              destruct IHp as [bp IHp]. destruct bp.
              -- rewrite IHp. assumption.
              -- rewrite IHp. destruct (optim q); 
                 try rewrite if_same; exists false;
                 reflexivity.
            * simpl. destruct IHp as [bp IHp].
              rewrite IHp. destruct bp.
              -- right. assumption.
              -- left. destruct (optim q);
                 try rewrite if_same; exists false;
                 reflexivity.
        + destruct IHq as [IHq | IHq].
            * destruct IHq as [bq IHq]. destruct bq.
                -- simpl. rewrite IHq. destruct (optim p); auto.
                   left. destruct b; [exists true | exists false];
                   reflexivity.
                -- left. simpl. rewrite IHq. destruct (optim p);
                try rewrite if_same; exists false;
                 reflexivity.
            * right. simpl. inversion IHp.
                -- inversion IHq.
                    ++ econstructor.
                        ** left. reflexivity.
                        ** constructor.
                        ** constructor.
                    ++ destruct H as [H | [H | H]]; rewrite H;
                       econstructor;
                       try (left; reflexivity);
                       econstructor;
                       try (left; reflexivity);
                       try (right; left; reflexivity);
                       try (right; right; reflexivity);
                       assumption.
                    ++ econstructor.
                        ** left. reflexivity.
                        ** constructor.
                        ** 