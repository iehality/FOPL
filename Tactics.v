Require Import Arith.
Require Import Lia.
Require Export FOPL.FOPL.
Require Export FOPL.Deduction.
Require Export FOPL.SetoidL.

Ltac Tpp :=
  match goal with
  | |- (?T ¦ ?p ||- _) => assert(T ¦ p ||- p);[auto|idtac]
  | _ => idtac
  end.

Ltac Tpqp :=
  match goal with
  | |- (?T ¦ ?p ¦ ?q ||- _) => assert(T ¦ p ¦ q ||- p);[auto|idtac]
  | _ => idtac
  end.

Lemma MP' {L : Lang} : forall T p q, (T ||- p [->] q) -> (T ||- p) -> (T ||- q).
Proof.
  intros.
  MP p.
  auto. auto.
Qed.

Ltac papply X :=
  match (type of X) with
  | ?T ||- ?p [->] ?q =>
    apply (@MP' _ _ p _ X) 
  | _ => idtac
  end.

Ltac foldeq := rewrite preq0.
Ltac foldeqh H := rewrite preq0 in H.
Ltac unfoldeq := rewrite <- preq0.
Ltac unfoldeqh H := rewrite <- preq0 in H.

Ltac SPECIALIZE2 H c d := apply fal_R2 with (t:=c) (s:=d) in H; simpl in H.

Ltac REWRITE X :=
  let U := fresh "T" in
  match (type of X) with
  | ?T ||- ?x[=]?y => 
    pose (U := T);
    rewrite -> preq0 in X;
    fold U in X;
    fold U;
    rewrite X at 1;
    rewrite <- preq0 in X;
    unfold U in X;
    unfold U;
    clear U
  | _ => idtac
  end.

Ltac REWRITE_r X :=
  let U := fresh "T" in
  match (type of X) with
  | ?T ||- ?x[=]?y => 
    pose (U := T);
    rewrite -> preq0 in X;
    fold U in X;
    fold U;
    rewrite <- X at 1;
    rewrite <- preq0 in X;
    unfold U in X;
    unfold U;
    clear U
  | _ => idtac
  end.

Ltac REW_at_1 :=
  let X := fresh "H" in
  match goal with
  | |- (?T ¦ ?p ||- _) => assert(X : T ¦ p ||- p);[auto|idtac]
  | _ => idtac
  end;
  let U := fresh "U" in
  match (type of X) with
  | ?T ||- ?x[=]?y => 
    pose (U := T);
    rewrite -> preq0 in X;
    fold U in X;
    fold U;
    rewrite X;
    rewrite <- preq0 in X;
    unfold U in X;
    unfold U;
    clear U
  | _ => assert(0=1)
  end;
  clear X.

Ltac REW_at_1r :=
  let X := fresh "H" in
  match goal with
  | |- (?T ¦ ?p ||- _) => assert(X : T ¦ p ||- p);[auto|idtac]
  | _ => idtac
  end;
  let U := fresh "U" in
  match (type of X) with
  | ?T ||- ?x[=]?y => 
    pose (U := T);
    rewrite -> preq0 in X;
    fold U in X;
    fold U;
    rewrite <- X;
    rewrite <- preq0 in X;
    unfold U in X;
    unfold U;
    clear U
  | _ => assert(0=1)
  end;
  clear X.

Ltac REW_at_2 :=
  let X := fresh "H" in
  match goal with
  | |- (?T ¦ ?p ¦ ?q ||- _) => assert(X : T ¦ p ¦ q ||- p);[auto|idtac]
  | _ => idtac
  end;
  let U := fresh "U" in
  match (type of X) with
  | ?T ||- ?x[=]?y => 
    pose (U := T);
    rewrite -> preq0 in X;
    fold U in X;
    fold U;
    rewrite X;
    rewrite <- preq0 in X;
    unfold U in X;
    unfold U;
    clear U
  | _ => assert(0=1)
  end;
  clear X.

Ltac REW_at_2r :=
  let X := fresh "H" in
  match goal with
  | |- (?T ¦ ?p ¦ ?q ||- _) => assert(X : T ¦ p ¦ q ||- p);[auto|idtac]
  | _ => idtac
  end;
  let U := fresh "U" in
  match (type of X) with
  | ?T ||- ?x[=]?y => 
    pose (U := T);
    rewrite -> preq0 in X;
    fold U in X;
    fold U;
    rewrite <- X;
    rewrite <- preq0 in X;
    unfold U in X;
    unfold U;
    clear U
  | _ => assert(0=1)
  end;
  clear X.