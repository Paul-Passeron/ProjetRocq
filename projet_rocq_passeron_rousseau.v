Require Import List.
Import ListNotations.

Require Import Coq.Arith.PeanoNat.
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

Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.


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

Fixpoint add (t:T) (n:nat) (m:multiset) : multiset :=
if n == 0 then m else 
match m with
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
Fixpoint wf (m: multiset) : Prop :=
  match m with
  | [] => True
  | (x, n) :: m' =>
      n > 0 /\
      (* x ne doit pas apparaître dans m' *)
      (forall y occ, In (y, occ) m' -> y <> x) /\
      (* le reste de la liste doit aussi être bien formé *)
      wf m'
  end.

(* question 2c *)

Lemma empty_wf: wf empty = True.
Proof.
  simpl.
  reflexivity.
Qed.

Require Import PeanoNat.
Require Import Coq.Logic.PropExtensionality.

Lemma singleton_wf: forall x: T, wf (singleton x) = True.
Proof.
  intro x.
  simpl.
  apply propositional_extensionality.
  split.
  intro H.
  - apply proj2 in H.
    apply proj2 in H.
    exact H.
  - split.
    + lia. 
    + split.
      * intros y n contr.
        contradiction.
      * exact H.
Qed.


(* Helper lemma: if x doesn't appear in a well-formed list, 
   then it doesn't appear after adding a different element *)
Lemma not_in_after_add_different : 
  forall x y n s, x <> y -> wf s -> 
  (forall z occ, In (z, occ) s -> z <> x) ->
  (forall z occ, In (z, occ) (add y n s) -> z <> x).
Proof.
  intros x y n s Hxy Hwf Hnot_in.
  induction s as [| [a an] s' IH].
  - simpl. destruct n.
    + intros z occ Hin. apply (Hnot_in z occ Hin).
    + simpl. intros z occ Hin.
      destruct Hin as [Heq | Hcontra].
      * inversion Heq. subst. symmetry. exact Hxy.
      * inversion Hcontra.
  - simpl in Hwf. 
    destruct Hwf as [Han_pos [Hnot_in_s' Hwf_s']].
    simpl. destruct n.
    + simpl. intros z occ Hin. apply (Hnot_in z occ Hin).
    + simpl. destruct (T_eq_dec a y) as [Hay | Hnay].
      * subst a. intros z occ [Heq | Hin'].
        -- inversion Heq. subst. symmetry. exact Hxy.
        -- apply (Hnot_in z occ). right. exact Hin'.
      * intros z occ [Heq | Hin'].
        -- inversion Heq. subst. 
           apply (Hnot_in z occ). left. reflexivity.
        -- apply (IH Hwf_s' 
          (fun w wocc Hw => Hnot_in w wocc (or_intror Hw)) z occ Hin').
Qed.

(* When adding to*)
Lemma add_to_empty_wf : forall x n, n > 0 -> wf [(x, n)].
Proof.
  intros x n Hn.
  simpl.
  split; [exact Hn | split].
  - intros y occ Hin. inversion Hin.
  - exact I.
Qed.


Lemma add_wf: forall (x: T) (n: nat) (s: multiset), wf s -> wf (add x n s).
Proof.
  intros x n s Hwf.
  induction s as [| [a an] s' IH].
  - simpl. destruct n.
    + simpl. exact Hwf.
    + simpl. apply add_to_empty_wf. lia.
  - simpl in Hwf.
    destruct Hwf as [Han_pos [Hnot_in_s' Hwf_s']].
    simpl. destruct n.
    + simpl. split; [exact Han_pos | split; [exact Hnot_in_s' | exact Hwf_s']].
    + simpl. destruct (T_eq_dec a x) as [Hax | Hnax].
      * subst a. simpl.
        split; [lia | split].
        -- exact Hnot_in_s'.
        -- exact Hwf_s'.
      * simpl. split; [exact Han_pos | split].
        -- intros y occ Hin_add.
           apply not_in_after_add_different with (x := a) (y := x) (n := S n) (s := s') in Hin_add.
           ++ exact Hin_add.
           ++ exact Hnax.
           ++ exact Hwf_s'.
           ++ exact Hnot_in_s'.
        -- apply IH. exact Hwf_s'.
Qed.

Lemma not_in_after_remove: 
  forall x y s occ, x <> y -> wf s ->
  In (y, occ) s -> In (y, occ) (removeOne x s).
Proof.
Admitted.

(* 
Lemma not_in_after_remove:
  forall (x y: T) (s: multiset), x <> y -> wf s -> 
  (forall (z: T) (occ: nat), In (z, occ) s -> z <> x) -> 
  (forall (z: T) (occ: nat), In (z, occ) (removeOne y s) -> z <> x).
Proof.
  intros x y s Hxy Hwf_s Hnot_in.
  induction s.
  - simpl. intros z occ contr. contradiction.
  - intros z occ.
    destruct a as [a an].
    simpl.
    destruct (T_eq_dec a y) as [Hay | Hnay].
    + destruct (an == 1) as [Han | Han].
      * rewrite Han.
        simpl.
        intro Hin.
        assert (H := Hwf_s).
        unfold wf in H.
        destruct H as [H0 [H1 H2]].
        assert (Hzoccin := Hnot_in z occ).
        simpl in Hzoccin.
        exact (Hzoccin ((or_intror (A := (a, an) === (z, occ)) (B := In (z, occ) s)) Hin)).
      * assert (an <> 1).
        assumption.
        rewrite <- Nat.eqb_neq in H.
        rewrite H.
        intro Hzoccin.
        subst y.
        destruct (T_eq_dec a z) as [Haz | Haz].
        -- subst z.
           symmetry.
           exact Hxy.
        -- simpl in Hzoccin.
           destruct Hzoccin as [Heq | Hin].
           injection Heq as H1 H2.
           contradiction.
           assert (Hz : In (z, occ) ((a, an) :: s)).
           simpl.
           right.
           assumption.
           exact ((Hnot_in z occ) Hz).
    + intro Hzin.
      destruct Hwf_s as [H0 [H1 H2]].

              

           


Admitted. *)



Lemma not_in_before_remove:
  forall (x y: T) (occ: nat) (s: multiset), x <> y -> wf s -> 
  (In (y, occ) (removeOne x s)) ->
  (In (y, occ) s).
Proof.
  intros x y occ s Hxy Hwfs HIn.
  induction s.
  - simpl in HIn. contradiction.
  - destruct a as [a an].
    simpl in Hwfs.
    destruct Hwfs as [H0 [H1 H2]].
    simpl.
    assert (H3 := IHs H2).
    right.
    destruct (an == 1) as [Heq1 | Hneq1].
    + simpl in HIn.
      rewrite Heq1 in HIn.
      simpl in HIn.
      destruct (T_eq_dec a x) as [Hax | Hax].
      * exact HIn.
      * assert (y <> a).
        -- admit.
        -- simpl in HIn. 
Admitted.

Lemma removeOne_wf: forall (s: multiset) (x: T), wf s -> wf (removeOne x s).
Proof.
  intros s x Hwf.
  induction s as [| [a an] s' IH].
  - simpl in *. exact Hwf.
  - simpl in Hwf. destruct Hwf as [Han_pos [Hnot_in_s' Hwf_s']].
    simpl.
    case (an == 1).
    + intro Han. rewrite Han.
      simpl.
      destruct (T_eq_dec a x) as [Hax | Hnax].
      * exact Hwf_s'.
      * simpl.
        split.
        lia.
        split.
        -- intros y occ Hin.
          destruct (T_eq_dec x y) as [Hxy | Hxy].
          ++ subst x. symmetry. exact Hnax.
          ++ exact (Hnot_in_s' y occ (not_in_before_remove x y occ s' Hxy Hwf_s' Hin)).
        -- exact (IH (Hwf_s')).
    + intro Han. 
      assert (an <> 1).
      assumption.
      destruct (T_eq_dec a x) as [Hax | Hnax].
      * assert(rewH:= H). rewrite <- Nat.eqb_neq in rewH.
        rewrite rewH.
        simpl.
        split.
        lia.
        split.
        -- exact Hnot_in_s'.
        -- exact Hwf_s'.
      * simpl.
        split.
        exact Han_pos.
        split.
        -- intros y occ HIn .
           assert (H' := Hnot_in_s' y occ).
           destruct (T_eq_dec x y).
           ++ rewrite e in Hnax.
              symmetry.
              exact Hnax.
           ++ exact (H' (not_in_before_remove x y occ s' n Hwf_s' HIn)).
        -- exact (IH Hwf_s'). 
Qed.


Lemma removeAll_wf: forall (s: multiset) (x: T), wf s -> wf (removeAll x s).
Proof.
Admitted.


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


Lemma prop_4 : forall x s, wf s -> (member x s = true <-> InMultiset x s).
Proof.
  intros.
  split; unfold InMultiset; intro; exact H0.
Qed.


Lemma prop_5 : forall x n s, n > 0 -> InMultiset x (add x n s).
Proof.
  intros.
  unfold InMultiset.
  destruct n as [| n'].
  - lia.
  - induction s as [| [y k] s' IH].
    + simpl. destruct (T_eq_dec x x) as [Heq|Hneq].
      * reflexivity.
      * contradiction.
    + simpl. destruct (T_eq_dec y x) as [Heq|Hneq].
      * simpl. subst y. destruct (T_eq_dec x x) as [Heq2|Hneq2].
        -- reflexivity.
        -- contradiction.
      * simpl. destruct (T_eq_dec y x) as [Heq2|Hneq2].
        -- contradiction.
        -- apply IH.
Qed.


Lemma prop_6 : forall x y n s, x <> y -> (InMultiset y (add x n s) <-> InMultiset y s).
(*Proof.
  intros.
  split.
  - unfold InMultiset. intro.
Admitted.*)
Proof.
  intros.
  split.
    - intro. induction s as [| [z k] s' IH]. destruct n.
      + simpl in H0. exact H0.
      + simpl in H0. assert (Hnz : S n <> 0) by discriminate. destruct (T_eq_dec x y) as [Heq | Hneq].
        * contradiction.
        * admit.
      + destruct (T_eq_dec x y) as [Heq | Hneq].
        * contradiction.
        * admit.
    - intro. induction s as [| [z k] s' IH]. destruct n.
      + simpl. exact H0.
      + unfold InMultiset. unfold InMultiset in H0.
Admitted.

(*Lemma prop_7_aux : forall x n s, In (x,n) s -> wf s -> n >= 1.
Proof.
  intros.
  induction s as [| [y m] s' IH].
  - simpl in H. contradiction. 
  - simpl in H. destruct H0 as [Hn [Hh1 Hh2]]. simpl in Hn. simpl in *. destruct H as [Heq | Hin']. 
    + inversion Heq. subst. exact Hn.
    + apply IH; assumption.
Qed.*)


Lemma prop_7 : forall x s, wf s -> (multiplicity x s = 0 <-> ~InMultiset x s).
Proof.
  intros.
  split.
  - intro. unfold not, InMultiset. intro. induction s as [| [y n] s' IH].
    + simpl in H0, H1. discriminate.
    + simpl in H0, H1. destruct (T_eq_dec y x) as [Heq | Hneq].
      * destruct H as [Hn [Hh1 Hh2]]. lia.
      * apply IH. destruct H as [Hn [Hh1 Hh2]].
        -- apply Hh2.  
        -- apply H0.
        -- apply H1.
  - intro. induction s as [| [y n] s' IH].
    + simpl. reflexivity.
    + simpl. destruct (T_eq_dec y x) as [Heq | Hneq].
      * subst y. destruct H as [Hn [Hh1 Hh2]].
Admitted.


Lemma prop_8 : forall x n s, multiplicity x (add x n s) = n + (multiplicity x s).
Proof.
  intros.
  induction s as [| [y k] s' IH].
  - simpl. destruct n.
    + simpl. reflexivity.
    + simpl. destruct (T_eq_dec x x) as [Heq | Hneq].
      * lia.
      * contradiction.
  - destruct n.
    + simpl. reflexivity.
    + simpl. destruct (T_eq_dec y x) as [Heq | Hneq].
      * subst y. simpl. destruct (T_eq_dec x x) as [Heq | Hneq].
        -- lia.
        -- contradiction.
      * simpl. destruct (T_eq_dec y x).
        -- contradiction.
        -- rewrite IH. reflexivity.
Qed.


Lemma prop_9 : forall x n y s, x <> y -> wf s -> multiplicity y (add x n s) = multiplicity y s.
Proof.
  intros x n y s Hxy Hwf. revert n. revert x y Hxy. induction s as [| [z k] s' IH]; intros.
  - simpl. destruct n.
    + reflexivity.
    + simpl.
      destruct (T_eq_dec x y) as [Heq | Hneq].
      * contradiction.
      * reflexivity.
  - simpl in Hwf. destruct Hwf as [Hk_pos [Hnot_in_s' Hwf_s']]. simpl. destruct n as [| n'].
    + simpl. destruct (T_eq_dec z y) as [Heq1 | Hneq1].
      * subst. destruct (T_eq_dec y x) as [Heq2 | Hneq2].
        -- symmetry in Heq2. contradiction.
        -- simpl. reflexivity.
      * destruct (T_eq_dec z y).
        -- contradiction.
        -- reflexivity.
    + simpl. destruct (T_eq_dec z x) as [Heq | Hneq].
      * subst. destruct (T_eq_dec x y) as [Heq2 | Hneq2].
        -- contradiction.
        -- simpl. destruct (T_eq_dec x y) as [Heq | Hneq].
          ++ contradiction.
          ++ reflexivity.
      * destruct (T_eq_dec z y) as [Heq2 | Hneq2].
        -- subst. simpl. destruct (T_eq_dec x y) as [Heq2 | Hneq2].
          ++ contradiction.
          ++ destruct (T_eq_dec y y) as [Heq3 | Hneq3].
            ** reflexivity.
            ** contradiction.
        -- simpl. destruct (T_eq_dec z y) as [Heq3 | Hneq3].
          ++ contradiction.
          ++ exact ((IH Hwf_s') x y Hxy (S n')).
Qed.
             

