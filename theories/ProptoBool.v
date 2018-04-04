Require Import Bool ZArith Logic Hammer ReflectFact.

Ltac prop2bool :=
  repeat
    match goal with
    | [ |- forall _ : _ -> _, _] => intro
    | [ |- forall _ : Z, _] => intro
    | [ |- forall _ : bool, _] => intro
    | [ |- forall _ : Type, _] => intro
    | [ |- forall _ : Prop, _] => intro

    | [ |- context[ Z.lt _ _ ] ] => rewrite <- Z.ltb_lt
    | [ |- context[ Z.gt _ _ ] ] => rewrite Z.gt_lt_iff; rewrite <- Z.ltb_lt
    | [ |- context[ Z.le _ _ ] ] => rewrite <- Z.leb_le
    | [ |- context[ Z.ge _ _ ] ] => rewrite Z.ge_le_iff; rewrite <- Z.leb_le
    | [ |- context[ Z.eq _ _ ] ] => rewrite <- Z.eqb_eq


    | [ |- context[ @Logic.eq Z _ _ ] ] =>
      rewrite <- Z.eqb_eq

    | [ |- context[?G0 = true \/ ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true \/ G1 = true) (orb G0 G1));
      [ | apply orP]

    | [ |- context[?G0 = true -> ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true -> G1 = true) (implb G0 G1)); 
      [ | apply implyP]

    | [ |- context[?G0 = true /\ ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true /\ G1 = true) (andb G0 G1));
      [ | apply andP]

    | [ |- context[?G0 = true <-> ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true <-> G1 = true) (Bool.eqb G0 G1));
      [ | apply iffP]

    | [ |- context[ ~ ?G = true ] ] =>
      rewrite (@reflect_iff (~ G = true) (negb G));
      [ | apply negP]

    | [ |- context[ is_true ?G ] ] =>
      unfold is_true

    | [ |- context[ True ] ] => rewrite <- TrueB

    | [ |- context[ False ] ] => rewrite <- FalseB

    (* | [ |- _ : (CompDec _ )] => try easy *)
    end.


(*
Require Coq.Reals.RIneq.
Require Coq.Reals.Raxioms.
Require Coq.Reals.Rtrigo1.

Lemma cos_decreasing_1 :
  forall y x : Rdefinitions.R,
    Rdefinitions.Rlt x y ->
    Rdefinitions.Rle x Rtrigo1.PI ->
    Rdefinitions.Rge y 0 ->
    Rdefinitions.Rle y Rtrigo1.PI ->
    Rdefinitions.Rge x 0 ->
    Rdefinitions.Rlt (Rtrigo_def.cos y) (Rtrigo_def.cos x).
Proof.
  time hammer.
Qed.


Lemma example_prop: forall a b, ((a = true /\ b = true) \/ a = true) <->  a = true.
Proof. prop2bool. hammer. Qed.

Require ZArith.BinInt.

Lemma max_lub : forall m p k n : BinNums.Z,
                  BinInt.Z.ge p m -> BinInt.Z.le n p -> BinInt.Z.le (BinInt.Z.max n m) p.
Proof. hammer. Qed.
*)