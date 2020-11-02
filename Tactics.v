Require Import Arith.
Require Import Lia.
Require Export FOPL.FOPL.
Require Export FOPL.Deduction.
Require Export FOPL.SetoidL.

Ltac Tpp :=
  match goal with
  | |- (?T :+ ?p ||- _) => assert(T :+ p ||- p);[AX|idtac]
  | _ => idtac
  end.

Ltac Tpqp :=
  match goal with
  | |- (?T :+ ?p :+ ?q ||- _) => assert(T :+ p :+ q ||- p);[AX|idtac]
  | _ => idtac
  end.

Ltac REWRITE X :=
  let U := fresh "T" in
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
    rewrite <- X;
    rewrite <- preq0 in X;
    unfold U in X;
    unfold U;
    clear U
  | _ => idtac
  end.

Ltac REW_at_1 :=
  let X := fresh "H" in
  match goal with
  | |- (?T :+ ?p ||- _) => assert(X : T :+ p ||- p);[AX|idtac]
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
  | |- (?T :+ ?p ||- _) => assert(X : T :+ p ||- p);[AX|idtac]
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
  | |- (?T :+ ?p :+ ?q ||- _) => assert(X : T :+ p :+ q ||- p);[AX|idtac]
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
  | |- (?T :+ ?p :+ ?q ||- _) => assert(X : T :+ p :+ q ||- p);[AX|idtac]
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