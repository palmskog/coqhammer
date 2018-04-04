Require Import Bool ZArith Logic Hammer ReflectFact.

(* Require Import mathcomp.ssreflect.ssreflect.*)
Coercion is_true : bool >-> Sortclass.

Infix "-->" := implb (at level 60, right associativity) : bool_scope.
Infix "<-->" := Bool.eqb (at level 60, right associativity) : bool_scope.


Ltac bool2prop :=
  repeat
    match goal with
    | [ |- forall _ : Z, _] => intro
    | [ |- forall _ : bool, _] => intro
    | [ |- forall _ : Type, _] => intro
    | [ p: Type |-  context[ forall _ : ?t, _ ] ] => intro

  (*  | [ |- context[ Bool.eqb _ _ ] ]  => unfold is_true; rewrite equal_iff_eq *)
    | [ |- context[ Z.ltb _ _ ] ]  => unfold is_true; rewrite Z.ltb_lt
    | [ |- context[ Z.gtb _ _ ] ]  => unfold is_true; rewrite Z.gtb_lt
    | [ |- context[ Z.leb _ _ ] ]  => unfold is_true; rewrite Z.leb_le
    | [ |- context[ Z.geb _ _ ] ]  => unfold is_true; rewrite Z.geb_le
    | [ |- context[ Z.eqb _ _ ] ]  => unfold is_true; rewrite Z.eqb_eq
(*
    | [ |- context[ Nat.ltb _ _ ] ]  => unfold is_true; rewrite Nat.ltb_lt
    | [ |- context[ Nat.gtb _ _ ] ]  => unfold is_true; rewrite Nat.gtb_lt
    | [ |- context[ Nat.leb _ _ ] ]  => unfold is_true; rewrite Nat.leb_le
    | [ |- context[ Nat.geb _ _ ] ]  => unfold is_true; rewrite Nat.geb_le
    | [ |- context[ Nat.eqb _ _ ] ]  => unfold is_true; rewrite Nat.eqb_eq
*)

    | [ |- context[?G0 --> ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 = true -> G1 = true)  (G0 --> G1)); 
      [ | apply implyP]

    | [ |- context[?G0 || ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 = true \/ G1 = true) (G0 || G1)); 
      [ | apply orP]

    | [ |- context[?G0 && ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 = true /\ G1 = true) (G0 && G1)); 
      [ | apply andP]

    | [ |- context[?G0 <--> ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 = true <-> G1 = true) (G0 <--> G1)); 
      [ | apply iffP]

    | [ |- context[ negb ?G ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G <> true) (negb G)); 
      [ | apply negP]

    | [ |- context[ false = true ] ] => rewrite FalseB

    | [ |- context[ true = true ] ] => rewrite TrueB

end.


(*
Lemma example_bool: forall a b, ((a && b) || a) <-->  a.
Proof. bool2prop. hammer. Qed.

Lemma leq_pmull: forall m n: Z, Z.gtb n 0 -> Z.leb m (n * m).
Proof. time bool2prop; hammer.
*)