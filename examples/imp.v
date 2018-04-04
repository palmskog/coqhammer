(* This file contains a definition of a simple imperative programming
   language together with its operational semantics. Most definitions
   and lemma statements were translated into Coq from Isabelle/HOL
   statements present in the book:

   T. Nipkow, G. Klein, Concrete Semantics with Isabelle/HOL.

   This gives a rough idea of how the automation provided by "hammer"
   and our reconstruction tactics compares to the automation available
   in Isabelle/HOL. *)

From Hammer Require Import Hammer Reconstr.

Require Import String.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.

Set Universe Polymorphism.


Inductive aexpr :=
| Nval : nat -> aexpr
| Vval : string -> aexpr
| Aplus : aexpr -> aexpr -> aexpr.

Definition state := string -> nat.

Fixpoint aval (s : state) (e : aexpr) :=
  match e with
  | Nval n => n
  | Vval x => s x
  | Aplus x y => aval s x + aval s y
  end.

Fixpoint plus (e1 e2 : aexpr) :=
  match e1, e2 with
  | Nval n1, Nval n2 => Nval (n1 + n2)
  | Nval 0, _ => e2
  | _, Nval 0 => e1
  | _, _ => Aplus e1 e2
  end.

Lemma lem_aval_plus : forall s e1 e2, aval s (plus e1 e2) = aval s e1 + aval s e2.
Proof.
  induction e1; sauto.
Qed.

Fixpoint asimp (e : aexpr) :=
  match e with
  | Aplus x y => plus (asimp x) (asimp y)
  | _ => e
  end.

Lemma lem_aval_asimp : forall s e, aval s (asimp e) = aval s e.
Proof.
  induction e; sauto.
  Reconstr.htrivial Reconstr.AllHyps
                    (@lem_aval_plus)
                    Reconstr.Empty.
Qed.

Inductive bexpr :=
| Bval : bool -> bexpr
| Bnot : bexpr -> bexpr
| Band : bexpr -> bexpr -> bexpr
| Bless : aexpr -> aexpr -> bexpr.

Fixpoint bval (s : state) (e : bexpr) :=
  match e with
  | Bval b => b
  | Bnot e1 => negb (bval s e1)
  | Band e1 e2 => bval s e1 && bval s e2
  | Bless a1 a2 => aval s a1 <? aval s a2
  end.

Fixpoint not (e : bexpr) :=
  match e with
  | Bval true => Bval false
  | Bval false => Bval true
  | _ => Bnot e
  end.

Fixpoint and (e1 e2 : bexpr) :=
  match e1, e2 with
  | Bval true, _ => e2
  | _, Bval true => e1
  | Bval false, _ => Bval false
  | _, Bval false => Bval false
  | _, _ => Band e1 e2
  end.

Definition less (a1 a2 : aexpr) :=
  match a1, a2 with
  | Nval n1, Nval n2 => Bval (n1 <? n2)
  | _, _ => Bless a1 a2
  end.

Fixpoint bsimp (e : bexpr) :=
  match e with
  | Bnot e1 => not (bsimp e1)
  | Band e1 e2 => and (bsimp e1) (bsimp e2)
  | Bless a1 a2 => less a1 a2
  | _ => e
  end.

Lemma lem_bval_not : forall s e, bval s (not e) = negb (bval s e).
Proof.
  induction e; sauto.
Qed.

Lemma lem_bval_and : forall s e1 e2, bval s (and e1 e2) = bval s e1 && bval s e2.
Proof.
  induction e1; sauto.
Qed.

Lemma lem_bval_less : forall s a1 a2, bval s (less a1 a2) = (aval s a1 <? aval s a2).
Proof.
  induction a1; sauto.
Qed.

Lemma lem_bval_bsimp : forall s e, bval s (bsimp e) = bval s e.
Proof.
  induction e; sauto.
  Reconstr.htrivial Reconstr.AllHyps
                    (@lem_bval_not)
                    Reconstr.Empty.
  Reconstr.htrivial Reconstr.AllHyps
                    (@lem_bval_and)
                    Reconstr.Empty.
  Reconstr.hsimple Reconstr.AllHyps
                   (@lem_aval_asimp, @lem_bval_less)
                   (@Coq.Init.Nat.ltb, @Coq.Init.Nat.leb).
  Reconstr.heasy Reconstr.AllHyps
                 (@Coq.Arith.PeanoNat.Nat.ltb_antisym, @lem_bval_less, @lem_aval_asimp, @Coq.Arith.PeanoNat.Nat.leb_antisym)
                 (@Coq.Init.Nat.ltb).
Qed.

Inductive cmd :=
| Skip : cmd
| Assign : string -> aexpr -> cmd
| Seq : cmd -> cmd -> cmd
| If : bexpr -> cmd -> cmd -> cmd
| While : bexpr -> cmd -> cmd.

Definition update (s : state) x v y := if string_dec x y then v else s y.

Inductive big_step : cmd * state -> state -> Prop :=
| SkipSem : forall s, big_step (Skip, s) s
| AssignSem : forall s x a, big_step (Assign x a, s) (update s x (aval s a))
| SeqSem : forall c1 c2 s1 s2 s3, big_step (c1, s1) s2 -> big_step (c2, s2) s3 ->
                                  big_step (Seq c1 c2, s1) s3
| IfTrue : forall b c1 c2 s s', bval s b = true -> big_step (c1, s) s' ->
                                big_step (If b c1 c2, s) s'
| IfFalse : forall b c1 c2 s s', bval s b = false -> big_step (c2, s) s' ->
                                 big_step (If b c1 c2, s) s'
| WhileFalse : forall b c s, bval s b = false ->
                             big_step (While b c, s) s
| WhileTrue : forall b c s1 s2 s3,
    bval s1 b = true -> big_step (c, s1) s2 -> big_step (While b c, s2) s3 ->
    big_step (While b c, s1) s3.

Notation "A ==> B" := (big_step A B) (at level 80, no associativity).

Lemma lem_seq_assoc : forall c1 c2 c3 s s', (Seq c1 (Seq c2 c3), s) ==> s' <->
                                            (Seq (Seq c1 c2) c3, s) ==> s'.
Proof.
  sauto.
  Reconstr.hobvious Reconstr.AllHyps
                    (@SeqSem)
                    Reconstr.Empty.
  Reconstr.hobvious Reconstr.AllHyps
                    (@SeqSem)
                    Reconstr.Empty.

  Restart.

  pose SeqSem; scrush.
Qed.

Definition equiv_cmd (c1 c2 : cmd) := forall s s', (c1, s) ==> s' <-> (c2, s) ==> s'.

Notation "A ~~ B" := (equiv_cmd A B) (at level 70, no associativity).

Lemma lem_unfold_loop : forall b c, While b c ~~ If b (Seq c (While b c)) Skip.
Proof.
  unfold equiv_cmd; sauto.
  inversion H.
  Reconstr.htrivial (@H0, @H4)
                    (@SkipSem, @IfFalse)
                    Reconstr.Empty.
  Reconstr.hobvious (@H0, @H1, @H, @H6, @H5, @H3)
                    (@SeqSem, @IfTrue)
                    (@equiv_cmd).
  inversion H; sauto.
  Reconstr.hobvious (@H4, @H7, @H5)
                    (@WhileTrue)
                    Reconstr.Empty.
  Reconstr.htrivial (@H5)
                    (@WhileFalse)
                    Reconstr.Empty.

  Restart.

  unfold equiv_cmd.
  intros; split.
  intro H; inversion H; pose SkipSem; pose SeqSem; pose IfFalse; pose IfTrue; scrush.
  intro H; inversion H; pose WhileTrue; pose WhileFalse; scrush.
Qed.

Lemma lem_while_cong_aux : forall b c c' s s', (While b c, s) ==> s' -> c ~~ c' ->
                                               (While b c', s) ==> s'.
Proof.
  assert (forall p s', p ==> s' -> forall b c c' s, p = (While b c, s) -> c ~~ c' -> (While b c', s) ==> s').
  intros p s' H.
  induction H; sauto.
  pose WhileFalse; scrush.
  Reconstr.hexhaustive 1 Reconstr.AllHyps
                       (@WhileTrue)
                       (@equiv_cmd).
  scrush.
Qed.

Lemma lem_while_cong : forall b c c', c ~~ c' -> While b c ~~ While b c'.
Proof.
  intros; unfold equiv_cmd.
  Reconstr.hobvious Reconstr.AllHyps
                    (@lem_while_cong_aux)
                    (@equiv_cmd).
Qed.

Lemma lem_big_step_deterministic :
  forall c s s1 s2, (c, s) ==> s1 -> (c, s) ==> s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H.
  revert s2.
  induction H; try yelles 1.
  scrush.
  intros s0 H2; inversion H2; scrush.
Qed.

Inductive small_step : cmd * state -> cmd * state -> Prop :=
| AssignSemS : forall x a s, small_step (Assign x a, s) (Skip, update s x (aval s a))
| SeqSemS1 : forall c s, small_step (Seq Skip c, s) (c, s)
| SeqSemS2 : forall c1 c2 s c1' s', small_step (c1, s) (c1', s') ->
                                    small_step (Seq c1 c2, s) (Seq c1' c2, s')
| IfTrueS : forall b c1 c2 s, bval s b = true ->
                              small_step (If b c1 c2, s) (c1, s)
| IfFalseS : forall b c1 c2 s, bval s b = false ->
                               small_step (If b c1 c2, s) (c2, s)
| WhileS : forall b c s, small_step (While b c, s) (If b (Seq c (While b c)) Skip, s).

Notation "A --> B" := (small_step A B) (at level 80, no associativity).

Require Import Relations.

Ltac pose_rt := pose @rt_step; pose @rt_refl; pose @rt_trans.

Definition small_step_star := clos_refl_trans (cmd * state) small_step.

Hint Unfold small_step_star : yhints.

Notation "A -->* B" := (small_step_star A B) (at level 80, no associativity).

Lemma lem_small_step_deterministic :
  forall c s s1 s2, (c, s) --> s1 -> (c, s) --> s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H.
  revert s2.
  induction H; try yelles 1.
  scrush.
  intros s2 H2; inversion H2; scrush.
Qed.

Lemma lem_star_seq2 : forall c1 c2 s c1' s', (c1, s) -->* (c1', s') ->
                                             (Seq c1 c2, s) -->* (Seq c1' c2, s').
Proof.
  assert (forall p1 p2, p1 -->* p2 ->
                        forall c1 c2 s c1' s', p1 = (c1, s) -> p2 = (c1', s') ->
                                               (Seq c1 c2, s) -->* (Seq c1' c2, s')).
  intros p1 p2 H.
  induction H as [ | | ? y ]; try yelles 1.
  pose_rt; pose SeqSemS2; scrush.
  intros c1 c2 s c1' s' H1 H2; subst.
  destruct y as [ c0 s0 ].
  assert ((Seq c1 c2, s) -->* (Seq c0 c2, s0)) by scrush.
  assert ((Seq c0 c2, s0) -->* (Seq c1' c2, s')) by scrush.
  pose_rt; scrush.
  scrush.
Qed.

Lemma lem_seq_comp : forall c1 c2 s1 s2 s3, (c1, s1) -->* (Skip, s2) -> (c2, s2) -->* (Skip, s3) ->
                                            (Seq c1 c2, s1) -->* (Skip, s3).
Proof.
  intros c1 c2 s1 s2 s3 H1 H2.
  assert ((Seq c1 c2, s1) -->* (Seq Skip c2, s2)).
  pose lem_star_seq2; scrush.
  assert ((Seq Skip c2, s2) -->* (c2, s2)).
  pose_rt; scrush.
  pose_rt; scrush.
Qed.

Lemma lem_big_to_small : forall p s', p ==> s' -> p -->* (Skip, s').
Proof.
  intros p s' H.
  induction H as [ | | | | | | b c s1 s2 ]; try yelles 1.
  pose_rt; pose AssignSemS; scrush.
  Reconstr.hobvious Reconstr.AllHyps
		    (@lem_seq_comp)
		    Reconstr.Empty.
  pose_rt; pose IfTrueS; scrush.
  pose_rt; pose IfFalseS; scrush.
  pose_rt; pose WhileS; pose IfFalseS; scrush.
  assert ((While b c, s1) -->* (Seq c (While b c), s1)).
  pose_rt; pose WhileS; pose IfTrueS; scrush.
  assert ((Seq c (While b c), s1) -->* (Seq Skip (While b c), s2)).
  Reconstr.hobvious Reconstr.AllHyps
		    (@lem_star_seq2)
		    Reconstr.Empty.
  pose_rt; pose SeqSemS1; scrush.
Qed.

Lemma lem_small_to_big_aux : forall p p', p --> p' -> forall s, p' ==> s -> p ==> s.
Proof.
  intros p p' H.
  induction H; try yelles 1.
  Reconstr.hobvious Reconstr.Empty
		    (@big_step_ind, @Coq.Relations.Relation_Operators.rt_refl, @SeqSem, @SkipSem, @lem_big_to_small)
		    (@state).
  sauto.
  Reconstr.hobvious Reconstr.AllHyps
		    (@SeqSem)
		    Reconstr.Empty.
  Reconstr.htrivial Reconstr.AllHyps
		    (@IfTrue)
		    Reconstr.Empty.
  Reconstr.htrivial Reconstr.AllHyps
		    (@IfFalse)
		    Reconstr.Empty.
  Reconstr.htrivial Reconstr.Empty
		    (@lem_unfold_loop, @SkipSem)
		    (@equiv_cmd).
Qed.

Lemma lem_small_to_big_aux_2 : forall p p', p -->* p' -> forall s, p' ==> s -> p ==> s.
Proof.
  intros p p' H.
  induction H; sauto.
  Reconstr.hobvious Reconstr.AllHyps
		    (@lem_small_to_big_aux)
		    Reconstr.Empty.
Qed.

Lemma lem_small_to_big : forall p s, p -->* (Skip, s) -> p ==> s.
Proof.
  assert (forall p p', p -->* p' -> forall s, p' = (Skip, s) -> p ==> s).
  intros p p' H.
  induction H; sauto.
  Reconstr.hobvious Reconstr.AllHyps
		    (@cmd_ind, @small_step_ind, @SkipSem, @lem_small_to_big_aux)
		    Reconstr.Empty.
  Reconstr.hsimple Reconstr.AllHyps
		   (@lem_small_to_big_aux_2)
		   (@small_step_star, @Coq.Init.Datatypes.snd).
  scrush.
Qed.

Corollary cor_big_iff_small : forall p s, p ==> s <-> p -->* (Skip, s).
Proof.
  Reconstr.hobvious Reconstr.Empty
		    (@lem_small_to_big, @lem_big_to_small)
		    Reconstr.Empty.
Qed.


Section SM.

Require Import List.
Import ListNotations.

Inductive Instr: Type :=
  | LoadI: nat    -> Instr
  | Load : string -> Instr
  | Add  : Instr.

Definition stack {A} := list A.

Definition tl2 {A} (l: list A) := @tl A (@tl A l).
Definition hd2 {A} d (l: list A) := hd d (@tl A l).

Definition exec1 {d} (i: Instr) (s: state) (stk: @stack nat): @stack nat := 
  match i with
    | LoadI n => n :: stk
    | Load  x => s x :: stk
    | Add     => (hd2 d stk + hd d stk) :: tl2 stk
  end.

Fixpoint exec {d} (l: list Instr) (s: state) (stk: @stack nat): @stack nat :=
  match l with
   | [] => stk
   | x :: xs => @exec d xs s (@exec1 d x s stk)
  end.

Fixpoint comp (a: aexpr): list Instr :=
  match a with
    | Nval n => [LoadI n]
    | Vval x => [Load x]
    | Aplus a1 a2 => comp a1 ++ comp a2 ++ [Add]
  end.

Lemma helper: forall d is1 is2 s stk, @exec d (is1 ++ is2) s stk = @exec d is2 s (@exec d is1 s stk).
Proof. induction is1; sauto. Qed.

Lemma ststk: forall d a s stk, @exec d (comp a) s stk = (aval s a) :: stk.
Proof. induction a; sauto.
       do 2 rewrite helper.
       Reconstr.scrush (** hammer *).
Qed.

End SM.


Section HL.

Definition assn := state -> Prop.
Definition hoare_valid (P: assn) (c: cmd) (Q: assn): Prop :=
  forall s t, P s /\ big_step (c, s) t -> Q t.

Definition state_subst (s: state) (a: aexpr) (x: string): state := (update s x (aval s a)).
Definition entails (P Q: assn): Prop := forall s, P s -> Q s.


Notation "|- '{' P '}' c '{' Q '}'" := (hoare_valid P c Q) (at level 80, no associativity).
Notation "s [ a / x ]" := (state_subst s a x) (at level 80, no associativity).


Inductive hoare: assn -> cmd -> assn -> Prop :=
  | HSkip  : forall P c, hoare P c P
  | HAssign: forall P a x, hoare (fun s => P (state_subst s a x)) (Assign x a) P
  | HSeq   : forall P Q R c1 c2,  hoare P c1 Q -> hoare Q c2 R -> hoare P (Seq c1 c2) Q
  | HIf    : forall P Q b c1 c2,  hoare (fun s => P s /\ bval s b = true)  c1 Q ->
                                  hoare (fun s => P s /\ bval s b = false) c2 Q -> hoare P (If b c1 c2) Q
  | HWhile : forall P b c, hoare (fun s => P s /\ bval s b = true) c P ->
                           hoare P (While b c) (fun s => P s /\ bval s b = false)
  | HConseq: forall (P P' Q Q': assn) c, (entails P' P) -> hoare P c Q -> (entails Q Q') -> hoare P' c Q'.


(*
Fixpoint sum n: nat :=
  match n with
    | O   => 0
    | S m => n + sum m
  end. 

Variable x: string.
Variable n: nat.
Check  (hoare (fun s => s x = 5) Skip  (fun s => s x = sum n)).

Print update.
Compute (fun s => (update s "x" 5 "x")).
Check (hoare (fun s => ((update s "x" 5 "x") = 5)) Skip  (fun s => ((update s "x" 5 "x") = 5))).
*)

Lemma strengthen_pre: forall (P P' Q: assn) c, (entails P' P) -> hoare P c Q -> hoare P' c Q.
Proof.
	Reconstr.hsimple Reconstr.Empty
		(@HConseq)
		(@entails) (** hammer *).
Qed.

Lemma weaken_post: forall (P Q Q': assn) c, (entails Q Q') -> hoare P c Q -> hoare P c Q'.
Proof.
	Reconstr.hobvious Reconstr.Empty
		(@HConseq)
		(@entails) (** hammer *).
Qed.

Lemma While': forall b (P Q: assn) c, hoare (fun s => P s /\ bval s b = true) c P ->
                                      (forall s, P s /\ bval s b = false -> Q s) ->
                                      hoare P (While b c) Q.
Proof. intros.
       specialize (HWhile _ _ _ H); intros.
       specialize (weaken_post P (fun s : state => P s /\ bval s b = false) Q (While b c)); intros.
       Reconstr.scrush (** hammer *).
Qed.


Lemma Assign': forall (P Q: assn) a x, (forall s, P s -> Q (state_subst s a x)) -> hoare P (Assign x a) Q.
Proof. intros.
       specialize (strengthen_pre (fun s: state => Q (state_subst s a x)) P Q  (Assign x a) ); intros.
       Reconstr.scrush (** hammer *).
Qed.

Inductive hoareT: assn -> cmd -> assn -> Prop :=
  | HSkipT  : forall P c, hoareT P c P
  | HAssignT: forall P a x, hoareT (fun s => P (state_subst s a x)) (Assign x a) P
  | HSeqT   : forall P Q R c1 c2, hoareT P c1 Q -> hoare Q c2 R -> hoareT P (Seq c1 c2) Q
  | HIfT    : forall P Q b c1 c2, hoareT (fun s => P s /\ bval s b = true)  c1 Q ->
                                  hoareT (fun s => P s /\ bval s b = false) c2 Q -> hoareT P (If b c1 c2) Q
  | HWhileT : forall P b c (T: state -> nat -> Prop),
                 (forall n, hoareT (fun s => P s /\ bval s b = true /\ (T s n)) c (fun s => P s /\ (exists n', n' < n /\ (T s n')))) ->
                  hoareT P (While b c) (fun s => P s /\ bval s b = false)
  | HConseqT: forall (P P' Q Q': assn) c, (entails P' P) -> hoareT P c Q -> (entails Q Q') -> hoareT P' c Q'.

Lemma WhileT'_fun: forall b (P Q: assn) c (f: state -> nat), 
                     (forall n: nat, hoareT (fun s => P s /\ bval s b = true /\ n = f s) c (fun s => P s /\ f s < n)) ->
                     hoareT P (While b c) (fun s => P s /\ bval s b = false).
Proof. intros.
       specialize (HWhileT P b c (fun s n => n = f s)); intros.
       apply H0. intros.
       eapply HConseqT.
       - Reconstr.scrush (** hammer *).
       - Reconstr.scrush (** hammer *).
	     - Reconstr.hobvious Reconstr.Empty
		     Reconstr.Empty
		    (@HL.entails) (** hammer *).
Qed.

Lemma strengthen_preT: forall (P P' Q: assn) c, (entails P' P) -> hoareT P c Q -> hoareT P' c Q.
Proof.
	Reconstr.hobvious Reconstr.Empty
		(@HL.HConseqT)
		(@HL.entails) (** hammer *).
Qed.

Lemma weaken_postT: forall (P Q Q': assn) c, (entails Q Q') -> hoareT P c Q -> hoareT P c Q'.
Proof.
	Reconstr.hobvious Reconstr.Empty
		(@HL.HConseqT)
		(@HL.entails) (** hammer *).
Qed.

Lemma WhileT': forall b (P Q: assn) c (f: state -> nat), 
                 (forall n: nat, hoareT (fun s => P s /\ bval s b = true /\ n = f s) c (fun s => P s /\ f s < n)) ->
                 (forall s, P s /\ bval s b = false -> Q s) ->
                 hoareT P (While b c) Q.
Proof. Admitted.


End HL.



