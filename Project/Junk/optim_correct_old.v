(* Approach: first manual proofs of whole project, then automization., then Ltac *)
Theorem optim_correct_old : forall V p,
    interp V p = interp V (optim p).
Proof.
    induction p as [x | b | q IHq q' IHq' | q IHq q' IHq' | q IHq q' IHq' |
                    q IHq]; 
    try reflexivity.
    - simpl. destruct (optim q) as [x | b | q_opt1 q_opt2 | q_opt1 q_opt2 |
                                    q_opt1 q_opt2 | q_opt];
      try (destruct (optim q') as [x' | b' | q'_opt1 q'_opt2 | q'_opt1 q'_opt2 |
                                  q'_opt1 q'_opt2 | q'_opt];
          try (simpl in *; rewrite IHq, IHq'; reflexivity);
          destruct b'; rewrite IHq, IHq'; auto).
        + destruct_if b (optim q').
    - simpl. destruct (optim q) as [x | b | q_opt1 q_opt2 | q_opt1 q_opt2 |
                                    q_opt1 q_opt2 | q_opt];
        try (destruct (optim q') as [x' | b' | q'_opt1 q'_opt2 | q'_opt1 q'_opt2 |
                                  q'_opt1 q'_opt2 | q'_opt];
          try destruct b';
          simpl in *; rewrite IHq, IHq'; auto;
        try (destruct b; 
            [simpl in *; rewrite IHq, IHq'; reflexivity |
             destruct (optim q'); try destruct b;
              rewrite IHq, IHq'; reflexivity]);
        destruct (optim q') as [x' | b' | q'_opt1 q'_opt2 | q'_opt1 q'_opt2 |
                                  q'_opt1 q'_opt2 | q'_opt];
          try destruct b';
          simpl in *; rewrite IHq, IHq'; auto).
        + destruct_if b (optim q').
    - simpl. destruct (optim q) as [x | b | q_opt1 q_opt2 | q_opt1 q_opt2 |
                                    q_opt1 q_opt2 | q_opt];
      try (destruct b; 
            [simpl in *; rewrite IHq, IHq'; reflexivity |
             destruct (optim q'); try destruct b;
              rewrite IHq, IHq'; reflexivity]);
        destruct (optim q') as [x' | b' | q'_opt1 q'_opt2 | q'_opt1 q'_opt2 |
                                  q'_opt1 q'_opt2 | q'_opt];
          try destruct b';
          simpl in *; rewrite IHq, IHq'; auto.
    - simpl. destruct (optim q) as [x | b | q_opt1 q_opt2 | q_opt1 q_opt2 |
                                    q_opt1 q_opt2 | q_opt];
        try destruct b;
        rewrite IHq; reflexivity.
    Qed.