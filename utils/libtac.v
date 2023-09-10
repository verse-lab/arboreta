Global Tactic Notation "removehead" hyp(H) :=
  let qq := fresh "nobody_will_use_this" in
  let qq2 := fresh "nobody_will_use_this2" in
  match (type of H) with
  ?HH -> _ => enough HH as qq; 
    [ pose proof (H qq) as qq2; clear H; rename qq2 into H; clear qq | ]
  end
.

Global Tactic Notation "eqsolve" := 
  intuition congruence; intuition discriminate.

Global Tactic Notation "split_sync" hyp(H) := 
  let rec aux HH :=
  (match goal with
  | |- _ /\ _ =>
    match (type of HH) with
    | _ /\ _ => split; [ apply proj1 in HH | apply proj2 in HH ]; aux HH
    | _ => idtac
    end
  | _ => idtac
  end) in aux H.
