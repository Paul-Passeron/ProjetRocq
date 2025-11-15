Require Import List.
Import ListNotations.

Require Import Stdlib.Arith.PeanoNat.
Import Nat.

Parameter A: Type.

Parameter A_eq_dec: forall (x y: A), {x=y} + {~x=y}.

Fixpoint repeat (x: A) (n: nat): list A :=
 match n with
  | 0  => []
  | S (n') => x::(repeat x n')
end.

Lemma repeat_sound1: forall (a: A) n,
  Forall (fun x => x=a) (repeat a n).
Proof.
induction n.
- unfold repeat. apply Forall_nil.
- simpl. apply Forall_cons.
  + reflexivity.
  + exact IHn.
Qed.

Lemma repeat_sound2: forall (a: A) n,
  length (repeat a n) = n.
Proof.
induction n.
- simpl. reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint split_p_aux (p: A -> bool) (l: list A) (acc: list A) := 
match l with
  | [] => (acc, [])
  | head::tail => match p head with
    | true => (acc, l)
    | false => split_p_aux p tail (acc ++ [head])
  end
end.

Definition split_p_acc (p: A -> bool) (l: list A)  := split_p_aux p l [].

Fixpoint split_p (p: A -> bool) (l: list A) :=
match l with
  | [] => ([], [])
  | head::tail => match p head with
    | true => ([], l)
    | false => let (left, right) := split_p p tail in (head::left, right)
  end
end.

Lemma split_p_first : forall (p : A -> bool) (l : list A),
Forall (fun x => p x = false) (fst (split_p p l)) .
Proof.
intros p.
induction l.
-simpl. apply Forall_nil.
- simpl. case (p a) eqn:Ha.
  + simpl. apply Forall_nil.
  + destruct (split_p p l) eqn:Hsplit. 
    simpl. 
    apply Forall_cons.
    * exact Ha.
    * simpl in IHl.
      exact IHl.
Qed.

Lemma split_p_snd : forall (p : A -> bool) (l l1 l2 : list A) x,
split_p p l = (l1, l2) -> head l2 = Some x -> p x = true.
Proof.
intros p l.
induction l as [| a l' IHl'].
- intros l1 l2 x Hsplit Hhead.
  simpl in Hsplit.
  injection Hsplit. intros H2 _.
  rewrite <- H2 in Hhead.
  discriminate Hhead.
 - intros l1 l2 x Hsplit Hhead.
    simpl in Hsplit.
    destruct (p a)eqn:Pa.
    + injection Hsplit as Hl1 Hl2.
      rewrite <- Hl2 in Hhead. 
      simpl in Hhead.
      inversion Hhead as [AeqX].
      rewrite <- AeqX.
      exact Pa.
    + destruct (split_p p l') as [left right] eqn:Hsplit'.
      injection Hsplit as Hl1 Hl2.
      eapply (IHl' left right).
      * reflexivity.
      * rewrite Hl2. exact Hhead.
Qed.



Lemma split_p_forall : forall (p : A -> bool) (l : list A),
Forall (fun x => p x = true) l -> split_p p l = ([], l).
Proof.
intros p. induction l.
- intros _. simpl. reflexivity.
- intro Hyp.
  simpl. 
  destruct (p a) eqn:Pa.
  + reflexivity.
  + destruct (split_p p l). 
    rewrite Forall_forall in Hyp.
    specialize (Hyp a). 
    simpl in Hyp. 
    assert (p a = true) as PaTrue.
    * apply Hyp. left. reflexivity.
    * rewrite PaTrue in Pa.
      discriminate Pa.
Qed.

Lemma split_p_forall_left : forall (p : A -> bool) (l : list A),
Forall (fun x => p x = false) l -> split_p p l = (l, []).
Proof. intros p. induction l.
- intro Hyp. simpl. reflexivity.
- intro Hyp. simpl. case (p a)eqn:Pa.
  + assert (p a = false) as PaFalse. {
      rewrite Forall_forall in Hyp.
      specialize (Hyp a).
      apply Hyp.
      simpl.
      left. reflexivity.
    }
    rewrite PaFalse in Pa.
    discriminate Pa.
  + destruct (split_p p l) as [left right] eqn:Hsplit.
    inversion Hyp.
    apply IHl in H2.
    injection H2 as HLeft HRight.
    rewrite HLeft. 
    rewrite HRight.
    reflexivity.
Qed.

Lemma split_p_append: forall (p: A -> bool) (l left right: list A),
split_p p l = (left, right) -> l = app left right.
Proof.
intros p. induction l.
- intros l r SplitHyp. simpl in SplitHyp. 
  injection SplitHyp as HL HR.
  rewrite <- HL.
  rewrite <- HR.
  reflexivity.
- intros left right SplitHyp.
  simpl in SplitHyp.
  destruct (p a) eqn:Pa.
  + injection SplitHyp as Empty Al. 
    rewrite <-Empty. 
    rewrite <- Al.
    reflexivity.
  + destruct (split_p p l) as [Left Right] eqn:Hsplit.
    specialize (IHl Left Right).
    assert (l = Left ++ Right).
    * apply IHl. reflexivity.
    * injection SplitHyp as ALeft RRight.
      rewrite <- RRight. 
      rewrite <- ALeft. 
      simpl.
      rewrite <- H.
      reflexivity.
Qed.

Require Import Lia.

Lemma split_p_length: forall (p: A -> bool) (l left right: list A),
split_p p l = (left, right) -> length left <= length l /\ length right <= length l.
intros p. induction l.
- intros left right SplitHyp.
  simpl in SplitHyp.
  injection SplitHyp as LEmpty REmpty.
  rewrite <- LEmpty.
  rewrite <- REmpty.
  simpl. lia.
- intros L R.
  simpl.
  destruct (p a) eqn:Pa.
  + intro H.
    split; injection H as LEmpty ReqAL. 
    * rewrite <- LEmpty.
      simpl.
      lia.
    * rewrite <- ReqAL.
      simpl.
      lia.
  + destruct (split_p p l) as [Left Right] eqn: HSplit.
    intro H. injection H as LeqAL REmpty. 
    specialize (IHl Left Right).
    assert(length Left <= length l /\
    length Right <= length l) as Rec.
      {
        apply IHl. 
        reflexivity.
      }
    destruct Rec as [RL RR].
    split.
    * rewrite <- LeqAL.
      simpl.
      apply Nat.succ_le_mono in RL.
      assumption.
    * rewrite <- REmpty.
      apply le_S.
      assumption.
Qed.

Require Import Stdlib.Classes.EquivDec.
Require Import Stdlib.Bool.Bool.


Definition split_occ (v: A) (l: list A) :=
  split_p (fun x => if A_eq_dec x v then true else false) l.

Lemma split_occ_first: forall (v: A) (l: list A),
Forall (fun x => ~(x = v)) (fst (split_occ v l)). 
Proof.
intros v.
induction l.
- simpl. apply Forall_nil.
- unfold split_occ.
  simpl.
  destruct (A_eq_dec a v) eqn:HAV.
  + simpl. apply Forall_nil.
  + destruct split_p as [Left Right] eqn: Hsplit.
    unfold split_occ in IHl.
    rewrite Hsplit in IHl.
    simpl in IHl.
    simpl.
    apply Forall_cons.
    * exact n.
    * exact IHl.
Qed.

Lemma split_occ_snd_starts_with_v: forall 
  (v: A) (l: list A), 
    snd (split_occ v l) = [] \/ (exists (l': list A), snd(split_occ v l) = v :: l').
Proof.
  intros v l.
  unfold split_occ.
  induction l.
  - simpl. left. reflexivity.
  - simpl. destruct (A_eq_dec a v) eqn:Hav.
    + right. exists l. rewrite e. reflexivity.
    + destruct (split_p (fun x => if A_eq_dec x v then true else false) l) eqn:Hsplit.
      exact IHl.
Qed.
      
(* Exercice 2 *)
(* Multi ensembles *)

Parameter T : Type.

Parameter T_eq_dec: forall (x y : T), {x=y} + {~x=y}.

Definition multiset := list (T*nat).

(* question 1 *)

Definition empty : multiset := ([]).

(* (*Count starts at 0 so that there is no room for invalid (a, 0) tuples*)
Definition singleton (x: T) : multiset := [(x, 0)]. *)

Definition singleton (t:T) : multiset := [(t,1)].

Fixpoint member (t:T) (m:multiset) : bool := match m with 
  |[] => false 
  |(x,_)::m' => if T_eq_dec x t then true
                else member t m'
end.

Fixpoint add (t:T) (n:nat) (m:multiset) : multiset := match m with
  |[] => [(t,n)]
  |(x,xn)::m' => if T_eq_dec x t then (x,xn+n)::m'
                 else (x,xn)::(add t n m')
end.

Fixpoint multiplicity (t:T) (m:multiset) : nat := match m with
  |[] => 0
  |(x,xn)::m' => if T_eq_dec x t then xn
                 else multiplicity t m'
end.

Fixpoint removeOne (t:T) (m:multiset) : multiset := match m with
  |[] => []
  |(x,xn)::m' => if T_eq_dec x t then
                     if xn=?1 then m'
                     else (x,xn-1)::m'
                 else (x,xn)::(removeOne t m')
end.

Fixpoint removeAll (t:T) (m:multiset) : multiset := match m with
  |[] => []
  |(x,xn)::m' => if T_eq_dec x t then m'
                 else (x,xn)::(removeAll t m')
end.

(* question 2a *)
Definition InMultiset (t:T) (m:multiset) : Prop := (member t m) = true.

(* question 2b *)
(*Definition wf (t:T) (m:multiset) : Prop := (member t m) -> (member t (removeAll t m))=false.*)

(* question 2c *)
(* question 3 *)
Lemma x_not_in_empty : forall x, ~ InMultiset x empty.
Proof.
intros. unfold not. intros. unfold InMultiset in H. simpl in H. discriminate.
Qed.

Lemma prop_2 : forall x y , InMultiset y (singleton x) <-> x = y.
Proof.
  intros.
  unfold InMultiset, singleton.
  simpl.
  destruct (T_eq_dec x y) as [Heq | Hneq].
  -split.
    +intros. exact Heq.
    +intros. reflexivity. 
  -split. 
    +intros. discriminate H.
    +intros. contradiction.
Qed.

Lemma prop_3 : forall x, multiplicity x (singleton x) = 1.
Proof.
  intros.
  unfold singleton.
  simpl.
  destruct (T_eq_dec x x) as [Heq | Hneq].
  -reflexivity.
  -contradiction.
Qed.