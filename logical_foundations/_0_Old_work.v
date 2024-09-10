Module Bool.
Inductive bool : Type :=
| true
| false.

Definition boolNeg (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition boolAnd (b1: bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition boolOr (b1: bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(*Exerc�cio*)
Definition boolNand (b1: bool) (b2:bool) : bool :=
  match b1 with
  | true => boolNeg(b2)
  | false => b2
  end.

Example test_boolNand1: (boolNand true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_boolNand2: (boolNand false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_boolNand3: (boolNand false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_boolNand4: (boolNand true true) = false.
Proof. simpl. reflexivity. Qed.

Definition boolAnd3 (b1: bool) (b2: bool) (b3: bool) : bool :=
  match b1 with
  | true => (boolAnd b2 b3)
  | false => false
  end.

Example test_boolAnd3_1: (boolAnd3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_boolAnd3_2: (boolAnd3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_boolAnd3_3: (boolAnd3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_boolAnd3_4: (boolAnd3 true true false) = false.
Proof. simpl. reflexivity. Qed.

End Bool.

Check Bool.boolAnd.

Module Color.
Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).

Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isRed (c: color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Check primary red.

Compute (isRed (primary red)).

Compute (monochrome (primary blue)).

End Color.

Module Bit.
Inductive bit : Type :=
| B0
| B1.

Inductive nybble : Type :=
  | bits(b0 b1 b2 b3 : bit).

Check (bits B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B0 B0 B0 B0)).

End Bit.

Module NatPlayground.

  Inductive nat : Type :=
  | O
  | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n => n
    end.

  Compute (pred (S (S (S (S O))))).

End NatPlayground.


  
  Definition minustwo (n: nat) : nat :=
    match n with
    | O => O
    | (S O) => O
    |S (S n) => n
    end.

  Fixpoint evenb(n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S n => negb(evenb(n))
    end.

  Definition oddb(n:nat) : bool :=
    match n with
    | n => negb(evenb(n))
    end.

  Module NatPlayground2.

  Fixpoint plus (n1:nat) (n2:nat) : nat :=
    match n1 with
    | O => n2
    | S n => S (plus n n2)
    end.

  Fixpoint mult (n1 n2: nat) : nat :=
    match n1 with
    | O => O
    | S n => plus (mult n n2) n2
    end.

  Fixpoint minus (n1 n2: nat) : nat :=
    match n1, n2 with
    | O, _ => O
    | S _, O => n1
    | S n1', S n2' => minus n1' n2'
    end.

  Fixpoint exp (base power: nat) : nat :=
    match power with
    | O => 1
    | S n => mult (exp base n) base
    end.

  (* Exercicio *)
  Fixpoint factorial (n : nat) : nat :=
    match n with
    | O => 1
    | S O => 1
    | S n' => mult (factorial n') n
    end.

  Example test_factorial1: (factorial 3) = 6.
  Proof. simpl. reflexivity. Qed.

  Example test_factorial2: (factorial 5) = (mult 10 12).
  Proof. simpl. reflexivity. Qed.

  Notation "x + y" := (plus x y).

  Notation "x - y" := (minus x y).

  Notation "x * y" := (mult x y).

  Compute (10 * 30).

End NatPlayground2.

  Fixpoint eqb (n m: nat) : bool :=
    match n with
    | O => match m with
            | O => true
            | S m' => false
            end
    | S n' => match m with
              | O => false
              | S m' => eqb n' m'
              end
    end.

  Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' => match m with
              | O  => false
              | S m' => leb n' m'
              end
    end.

  Example test_leb1: leb 2 2 = true.
  Proof. simpl. reflexivity. Qed.

  Example test_leb2: leb 2 4 = true.
  Proof. simpl. reflexivity. Qed.

  Example test_leb3: leb 4 2 = false.
  Proof. simpl. reflexivity. Qed.

  Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
  Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

  Example test_leb3': (4 <=? 2) = false.
  Proof. simpl. reflexivity. Qed.

  Definition ltb (n m: nat) : bool :=
    match n with
    | O => match m with
           | O => false
           | S m' => true
           end
    | S n' => match m with
              | O => false
              | S m' => (n' <=? m') && (negb(n' =? m'))
              end
    end.

  Notation "x <? y" := (ltb x y) (at level 80) : nat_scope.

  Example test_ltb1: (ltb 2 2) = false.
  Proof. simpl. reflexivity. Qed.

  Example test_ltb2: (ltb 2 4) = true.
  Proof. simpl. reflexivity. Qed.

  Example test_ltb3: (ltb 4 2) = false.
  Proof. simpl. reflexivity. Qed.
  
  Theorem plus_O_n: forall n: nat, 0 + n = n.
  Proof.
    intros n. simpl. reflexivity. Qed.

  Theorem plus_1_l: forall n: nat, 1 + n = S n.
  Proof.
    intros n. simpl. reflexivity. Qed.

  Theorem mult_0_l: forall n: nat, 0 * n = 0.
  Proof.
    intros n. simpl. reflexivity. Qed.

  Theorem plus_id_example: forall n m: nat, n = m ->  n + n = m + m.

  Proof.
    intros n m.
    intros H.
    rewrite <- H.
    reflexivity.
    Qed.


  Theorem plus_id_exercise: forall n m o : nat,
      n = m -> m = o -> n + m = m + o.

  Proof.
    intros n m o.
    intros H.
    intros H1.
    rewrite -> H.
    rewrite <- H1.
    reflexivity.
  Qed.

  Check mult_n_O.
  Check mult_n_Sm.
  
  Theorem mult_n_0_m_0: forall p q: nat,
      (p * 0) + (q * 0) = 0.

  Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
  Qed.
  
  Theorem mult_n_1: forall p: nat, p * 1 = p.
      
  Proof.
    intros p.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
  Qed.

  Theorem plus_1_neq_0: forall n: nat,
      (n + 1) =? 0 = false.
  Proof.
    intros n. destruct n as [| n'] eqn:E.
    - simpl. reflexivity.
    - simpl. reflexivity. Qed.

  Theorem negb_involutive: forall b: bool, negb (negb b) = b.

  Proof.
    intros b. destruct b eqn:E.
    - reflexivity.
    - reflexivity. Qed.

  Theorem andb_commutative: forall b c : bool, andb b c = andb c b.
  Proof.
    intros b c. destruct b eqn: Eb.
    - destruct c eqn: Ec.
      + reflexivity.
      + reflexivity.
    - destruct c eqn: Ec.
      + reflexivity.
      + reflexivity.
  Qed.

  Theorem andb_true_elim2: forall b c : bool,
      (andb b c = true) -> (c = true).

  Proof.
    intros b c. destruct b eqn: Eb.
    - destruct c eqn: Ec.
      + simpl. reflexivity.
      + simpl. intros H. rewrite <- H. reflexivity.
    - destruct c eqn: Ec.
      + simpl. intros H. reflexivity.
      + simpl. intros H. rewrite <- H. reflexivity.
  Qed.

  Theorem zero_nbeq_plus_1: forall n: nat,
      0 =? (n + 1) = false.

  Proof.
    intros [| n].
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  (* Exercicios finais, sec�o 1 *)
  
  Theorem andb_eq_orb: forall b c : bool,
      (andb b c = orb b c) -> b = c.

  Proof.
    intros b c. destruct b eqn: Eb.
    - simpl. intros H. rewrite -> H. reflexivity.
    - simpl. intros H. rewrite <- H. reflexivity.
  Qed.

  Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

  Fixpoint incr (m : bin) : bin :=
    match m with
    | Z => B1 Z
    | B0 m' => B1 m'
    | B1 m' => B0 (incr m')
    end.

  Example test_bin_incr1: (incr(B1 Z)) = B0 (B1 Z).
  Proof. simpl. reflexivity. Qed.  

  Example test_bin_incr2: (incr(B0(B1 Z))) = B1 (B1 Z).
  Proof. simpl. reflexivity. Qed.

  Example test_bin_incr3: (incr(B1(B1(Z))) = B0(B0(B1 Z))).
  Proof. simpl. reflexivity. Qed.

  (* Ao achar um digito binario, e ir para "direita" est� se multiplicando
     n por 2 *)
  Fixpoint bin_to_nat (m: bin) : nat :=
    match m with
    | Z => O
    | B0 m' => 2 * (bin_to_nat m')
    | B1 m' => 1 + (2 * (bin_to_nat m'))
    end.

  Example test_bin_incr4: bin_to_nat (B0 (B1 Z)) = 2.
  Proof. simpl.  reflexivity. Qed.

  Example test_bin_incr5: bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
  Proof. simpl. reflexivity. Qed.

  Example test_bin_incr6:
    bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).

  Proof. simpl. reflexivity. Qed.

  (* Theorem mult_0_plus': forall n m: nat,
      (0 + n) * m  = n * m.
  Proof.
    intros n m.
    assert (H: 0 + n = n). {reflexivity.}
                           rewrite -> H. reflexivity.
  Qed. *)

  (* ja fiz *)
  Theorem plus_comm: forall n m : nat, n + m = m + n.
  Proof. (* n + m = m + n
            by induction on n:
            base case = 0 + m = m + 0, m = m, true
            supose n' + m = m + n'
            for S n'
            S n' + m = m + S n'
            S (n' + m) = m + S n'
            by induction hipoteses.
            S (m + n') = m + S n'
            S m' + n' = m + S n'
            m + n' = m + n', true.
            Qed.
          *)
    
  Admitted.

  
  Theorem plus_rearrange: forall n m p q : nat,
      (n + m) + (p + q) = (m + n) + (p + q).
  Proof.
    intros n m p q.
    assert (H: n + m = m + n).
    { rewrite -> plus_comm. reflexivity. }
    rewrite -> H. reflexivity.
  Qed.

  (*Thereom true = n =? n for any n,
    by induction on n.
    base case n = 0, 0 =? 0 = true.
    supose for (n' =? n') = true.
    S n' =? S n'
    we can simplify to n' =? n'
    by the induction hipoteses. = true.
   *)


  (* Ja fiz *)

  Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
  Proof. Admitted.

  Theorem plus_swap: forall n m p : nat,
      n + (m + p) = m + (n + p).

  Proof.
    intros n m p. rewrite -> plus_assoc. rewrite -> plus_assoc.
    assert (H: n + m = m + n).
    { rewrite -> plus_comm. reflexivity. }
    rewrite -> H. reflexivity.
  Qed.

  Theorem mult_O_r: forall n :nat, n * 0 = 0.
  Proof.
    intros n. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
  Qed.  

  Check (mult_n_Sm).
  Theorem mult_comm : forall n m : nat, m * n = n * m.
  Proof.
    intros n m. induction n as [|n' IH].
    (*n' = 0 *)
    - simpl. rewrite -> mult_O_r. reflexivity.
    (* n' = S n' *)
    - simpl. rewrite <- mult_n_Sm.
      rewrite -> IH. rewrite -> plus_comm. reflexivity.
  Qed.

  Check leb.

  Theorem leb_refl: forall n: nat,  true = ( n <=? n).

  Proof.
    intros n. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite <- IH. reflexivity.
  Qed.

  Theorem zero_nbeq_S: forall n: nat,
      0 =? (S n) = false.

  Proof.
    intros n. reflexivity.
  Qed.

  Theorem andb_false_r : forall b : bool,
      andb b false = false.

  Proof.
    intros b. destruct b eqn: Eb.
    - reflexivity.
    - reflexivity.
  Qed.


  Theorem plus_O_r: forall n: nat,
      n + 0 = n.
  Proof.
    intros n. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
  Qed.               

    
  Theorem ble_plus_const: forall n m: nat,
      n <=? (n + m) = true.

  Proof.
    intros n m. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
  Qed.

  Theorem ble_sub_const: forall n m p: nat,
      (p + n) <=? (p + m) = (n <=? m).

  Proof.
    intros n m p. induction p as [|p' IH].
    - simpl. reflexivity.
    - simpl. rewrite -> IH. reflexivity.
  Qed.
    
  Theorem ble_plus_2_const: forall n m p : nat,
      (((p + n) <=? (p + m)) = true) -> (n <=? m) = true.
  
  Proof.
    intros n m p. rewrite -> ble_sub_const. intros H.
    rewrite -> H. reflexivity.
  Qed.
          
  Theorem plus_ble_compat_l : forall n m p : nat,
      (n <=? m = true) -> (p + n) <=? (p + m) = true.
  
  Proof.
    intros n m p. intros H. rewrite -> ble_sub_const.
    rewrite -> H. reflexivity.
  Qed.

  Theorem S_nbeq_0: forall n : nat,
      (S n) =? 0 = false.

  Proof.
    intros n. simpl. reflexivity.
  Qed.

  Theorem mult_1_l: forall n: nat, 1 * n = n.
  Proof.
    intros n. simpl. rewrite -> plus_O_r. reflexivity.
  Qed.

  Theorem S_plus_const_eq_2_S: forall a b: nat,
      S(S(a + b)) = S a + S b.

  Proof.
    intros a b. induction a as [|a' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity. 
  Qed.                                     

  Theorem bin_to_nat_pres_incr: forall b : bin,
      (bin_to_nat (incr b)) = (S (bin_to_nat b)).
  
  Proof.
    intros b. induction b as [|b1' |b2' IH].
    - reflexivity.
    - reflexivity.
    - simpl. rewrite -> plus_O_r. rewrite -> plus_O_r.
      rewrite -> S_plus_const_eq_2_S. rewrite -> IH. reflexivity.
  Qed.

  (* Binary inverse exercise *)
  Fixpoint nat_to_bin (n: nat) : bin :=
    match n with
    | O => Z
    | S n' => incr(nat_to_bin n')
    end.


  Definition nat_bin_eq (n: nat) (b:bin) : bool :=
    match n with
    | O => (bin_to_nat b) =? O
    | S n' => (bin_to_nat b) =? S n'
    end.
      
  Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.

  Proof.
    intros n. induction n as [|n' IH].
    - reflexivity.
    - simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IH. reflexivity.
  Qed.

  Module lists.
  Inductive natprod : Type :=
  | pair (n1 n2 : nat).

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Definition swap_pair (p:natprod) : natprod :=
    match p with
    | ( x , y ) => ( y , x )
    end. 

  Theorem surjective_pairing' : forall (n m : nat),
      (n,m) = (fst(n,m), snd(n,m)).

  Proof. intros n m. reflexivity. Qed.

  Theorem surjective_pairing: forall (p : natprod),
      p = (fst p, snd p).

  Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall p : natprod,
      (snd p, fst p) = swap_pair p.

  Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  Theorem fst_swap_is_snd: forall p : natprod,
      fst (swap_pair p) = snd p.

  Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).

  Notation "[ ]" := nil.

  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => O
    | n :: r => S (length r)
    end.

  Fixpoint app (l1 l2: natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y) (right associativity, at level 60).

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h:: t => h
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | O :: t => nonzeros t
    | h :: t => h :: (nonzeros t)
    end.

  Example test_nonzeros: nonzeros[0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.

  Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.
 
  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => if(evenb h) then (oddmembers t) else h :: (oddmembers t)
    end.

  Definition countoddmembers (l:natlist) : nat :=
    match l with
    | nil => 0
    | h :: t => length(oddmembers l)
    end.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
    | nil, nil => nil
    | nil, _ => l2
    | _, nil => l1
    | h :: t, m :: n => h :: m :: alternate t n
    end.

  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. simpl. reflexivity. Qed.

  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof. simpl. reflexivity. Qed.

  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof. simpl. reflexivity. Qed.

  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof. simpl. reflexivity. Qed.

  Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => 0
    | h :: t => if h =? v then S(count v t) else count v t
    end.

  Definition sum (a b : bag) : bag :=
    match a with
    | nil => b
    | h :: t => a ++ b
    end.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. simpl. reflexivity. Qed.

  Definition add (v:nat) (s:bag) : bag :=
    match s with
    | nil => v :: nil
    | h :: t => v :: s
    end.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. simpl. reflexivity. Qed.

  Example test_add2:count 5 (add 1 [1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.

  Definition member (v:nat) (s:bag) : bool :=
    match s with
    | nil => false
    | h :: t => if negb (count v s <=? 0) then true else false
    end.

  Example test_member1: member 1 [1;4;1] = true.
  Proof. simpl. reflexivity. Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof. simpl. reflexivity. Qed.

  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t => if (h =? v) then t else h :: (remove_one v t) 
    end.

  Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  
  Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  
  Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. simpl. reflexivity. Qed.


  Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. simpl. reflexivity. Qed.

  Theorem nil_app: forall l: natlist,
      [] ++ l  = l.
  Proof. reflexivity. Qed.

  Theorem tl_length_pred: forall l:natlist,
      pred(length l) = length(tl l).

  Proof.
    intros l. destruct l as [|n l'].
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem app_assoc: forall l1 l2 l3: natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).

  Proof.
    intros l1 l2 l3. induction l1 as [|n l1' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
  Qed.

  Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem rev_length_firsttry : forall l : natlist,
      length (rev l) = length l.
  
  Proof.
    intros l. induction l as [| n l' IHl'].
    - (* l = nil *)
      reflexivity.
    - (* l = n :: l' *)
      (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
      simpl.
      (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
      rewrite <- IHl'.
      (* ... but now we can't go any further. *)
  Abort.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).

  Proof.
    intros l1 l2. induction l1 as[|n l1' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
  Qed.

  Theorem rev_length: forall l : natlist,
      length (rev l) = length l.

  Proof.
    intros l. induction l as [|n l' IH].
    - reflexivity.
    - simpl. rewrite -> app_length. rewrite <- IH. simpl. rewrite -> plus_comm.
      reflexivity.
  Qed.

  Search (_ + _ = _ + _).

  Theorem app_nil_r : forall l : natlist,
      l ++ [] = l.

  Proof.
    intros l. induction l as [|n l' IH].
    - reflexivity.
    - simpl. rewrite -> IH. reflexivity.
  Qed.

  Theorem rev_app_disr : forall l1 l2 : natlist,
      rev(l1 ++ l2) = rev l2 ++ rev l1.

  Proof.
    intros l1 l2. induction l1 as [|n l1' IH].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IH. rewrite -> app_assoc. reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev ( rev l ) = l.

  Proof.
    intros l. induction l as [|n l' IH].
    - reflexivity.
    - simpl. rewrite -> rev_app_disr. simpl. rewrite -> IH. reflexivity.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.

  Proof.
    intros l1 l2 l3 l4. rewrite -> app_assoc. rewrite -> app_assoc.
    reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).

  Proof.
    intros l1 l2. induction l1 as [|n l1' IH].
    - reflexivity.
    - simpl. destruct n eqn: En.
      + rewrite -> IH. reflexivity.
      + rewrite -> IH. simpl. reflexivity.
  Qed.

  Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1 with
    | nil => true
    | h :: t => match l2 with
                | nil => false
                | h' :: t' => if (h =? h') then andb true (eqblist t t') else
                                false
                end
    end.

  Example test_eqblist1 :
    (eqblist nil nil = true).
  Proof. simpl. reflexivity. Qed.

  Example test_eqblist2 :
    eqblist [1;2;3] [1;2;3] = true.
  Proof. simpl. reflexivity. Qed.

  Example test_eqblist3 :
    eqblist [1;2;3] [1;2;4] = false.
  Proof. simpl. reflexivity. Qed.

  Theorem eqblist_refl : forall l : natlist,
      true = eqblist l l.

  Proof.
    intros l. induction l as [|n l' IH].
    - reflexivity.
    - simpl. assert (H: n =? n = true).
      {
        induction n as [|n' IHn].
        + reflexivity.
        + simpl. rewrite -> IHn. reflexivity.
      }
      rewrite -> H. rewrite -> IH. reflexivity.
  Qed.

  Theorem count_member_nonzero : forall s : bag,
      1 <=? (count 1 (1 :: s)) = true.

  Proof.
    intros s. destruct s eqn: Es.
    - simpl. reflexivity.
    - simpl . reflexivity.
  Qed.

  Theorem leb_n_Sn : forall n,
      n <=? (S n) = true.
  Proof.
    intros n. induction n as [| n' IHn'].
    - (* 0 *)
      simpl. reflexivity.
    - (* S n' *)
      simpl. rewrite IHn'. reflexivity.
  Qed.

  Theorem remove_does_not_increase_count: forall (s : bag),
      (count 0 (remove_one 0 s)) <=? (count 0 s) = true.

  Proof.
    intros s. induction s as [|h t IH].
    - reflexivity.
    - simpl. destruct h eqn: Eh.
      + simpl. rewrite -> leb_n_Sn. reflexivity.
      + simpl. rewrite -> IH. reflexivity.
  Qed.

  Theorem append_nil_eq_nil: forall l : natlist,
      l ++ [] = nil -> l = nil.
  Proof.
    intros l. destruct l eqn: El.
    - intros H. reflexivity.
    - simpl. assert(A: n :: n0 ++ [] = n :: n0).
      { rewrite -> app_nil_r. reflexivity. }
      rewrite A. intros H. rewrite H. reflexivity.
  Qed.

  Theorem nil_eq_rev_nil: forall l : natlist,
      l = [] -> rev l = [].

  Proof.
    intros l. intros H. rewrite -> H. reflexivity.
  Qed.
                                                                                
  (* 4 stars *)
  Theorem rev_injective : forall l1 l2 : natlist,
      rev l1 = rev l2 -> l1 = l2.

  Proof.
    intros l1 l2. intros H. rewrite <- rev_involutive.
    rewrite <- H. rewrite rev_involutive. reflexivity.
  Qed.

  Inductive natoption : Type :=
  | Some (n : nat)
  | None.

   Fixpoint nth_bad (l:natlist) (n:nat) : natoption :=
    match l with
    | nil => None
    | a :: l' => match n with
                | 0 => Some a
                | S n' => nth_bad l' n'
                end
    end.

   Inductive id : Type :=
   | Id (n : nat).

   Definition eqb_id (x1 x2 : id) :=
     match x1, x2 with
     | Id n1, Id n2 => n1 =? n2
     end.

   Inductive partial_map : Type :=
   | empty
   | record (i : id) (v : nat) (m : partial_map).

   Definition update(d : partial_map) (x : id) (value : nat) : partial_map :=
     record x value d.

   Fixpoint find (x : id) (d : partial_map) : natoption :=
     match d with
     | empty => None
     | record y v d' => if eqb_id x y then Some v else find x d'
     end.

  End lists.

  Inductive boollist : Type :=
   | bool_nil
   | bool_cons (b : bool) (l : boollist).

   Inductive list (X:Type) : Type :=
   | nil
   | cons (x : X) (l : list X).

   Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
     match count with
     | 0 => nil X
     | S count' => cons X x (repeat X x count')
     end.

   Arguments nil {X}.
   Arguments cons {X} _ _.
   Arguments repeat {X} x count.

   Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

   Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
     match l1 with
     | nil => l2
     | cons h t => cons h (app t l2)
     end.
   
   Fixpoint rev {X:Type} (l:list X) : list X :=
     match l with
     | nil => nil
     | cons h t => app (rev t) (cons h nil)
     end.
   
   Fixpoint length {X : Type} (l : list X) : nat :=
     match l with
     | nil => 0
     | cons h l' => S (length l')
     end.

   Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
   Proof. reflexivity. Qed.

   Notation "x :: y" := (cons x y)(at level 60, right associativity).
   Notation "[ ]" := nil.
   Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
   Notation "x ++ y" := (app x y)(at level 60, right associativity).

   Theorem app_nil_r : forall (X:Type) (l:list X),
       l ++ [] = l.

   Proof.
     intros X l. induction l as [|n l' IH].
     - reflexivity.
     - simpl. rewrite -> IH. reflexivity.
   Qed.

   Theorem app_assoc : forall A(l m n : list A),
       l ++ m ++ n = ( l ++ m ) ++ n.

   Proof.
     intros A l m n. induction l as [|h l' IH].
     - reflexivity.
     - simpl. rewrite -> IH. reflexivity.
   Qed.

   Lemma app_length : forall (X:Type) (l1 l2 : list X),
       length(l1 ++ l2) = length l1 + length l2.

   Proof.
     intros X l1 l2. induction l1 as [|n l1' IH].
     - reflexivity.
     - simpl. rewrite -> IH. reflexivity.
   Qed.

   Theorem rev_app_distr: forall X(l1 l2 : list X),
       rev (l1 ++ l2) = rev l2 ++ rev l1.

   Proof.
     intros X l1 l2. induction l1 as [|n l1' IH].
     - simpl. rewrite -> app_nil_r. reflexivity.
     - simpl. rewrite -> IH. rewrite <- app_assoc. reflexivity.
   Qed.

   Theorem rev_involutive : forall X : Type, forall l : list X,
         rev ( rev l ) = l.

   Proof.
     intros X l. induction l as [|n l' IH].
     - reflexivity.
     - simpl. rewrite -> rev_app_distr. rewrite -> IH. reflexivity.
   Qed.

   Inductive prod (X Y : Type) : Type :=
   | pair (x : X) (y : Y).

   Arguments pair {X} {Y} _ _.

   Notation "( x , y )" := (pair x y).

   Notation "X * Y" := (prod X Y) : type_scope.

   Definition fst {X Y : Type} (p : X * Y) : X :=
     match p with
     | (x, y) => x
     end.

   Definition snd {X Y : Type} (p : X * Y) : Y :=
     match p with
     | (x, y) => y
     end.

   Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
     match lx, ly with
     | [], _ => []
     | _, [] => []
     | x :: tx, y :: ty => (x, y) :: (combine tx ty)
    end.

   Compute(combine [1;2] [false;false;true;true]).

   Fixpoint split {X Y: Type} (l : list (X * Y)) : (list X) * (list Y) :=
     match l with
     | [] => ([], [])
     | h :: t => ((fst h :: (fst(split t))), (snd h :: (snd(split t))))
     end.

   Example test_split: split [(1,false);(2,false)] = ([1;2],[false;false]).
   Proof. simpl. reflexivity. Qed.

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | nil => None
     | a :: l' => match n with
                 | O => Some a
                 | S n' => nth_error l' n'
                 end
     end.

   Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
     f (f (f n)).

   Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : (list X) :=
     match l with
     | [] => []
     | h :: t =>
         if test h then h :: (filter test t)
         else filter test t
     end.

   Definition filter_even_gt7 (l : list nat) : list nat :=
     filter (fun n => andb (evenb n) (negb(leb n 7))) l.

   Example test_filter_even_gt7_1 :
     filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].

   Proof. reflexivity. Qed.

   Example test_filter_even_gt7_2 :
     filter_even_gt7 [5;2;6;19;129] = [].

   Proof. reflexivity. Qed.

   Definition partition {X : Type} (test : X -> bool) (l : list X)
     : list X * list X :=
     ((filter test l),(filter (fun x' => negb(test x')) l)).

   Example test_partition1: partition oddb
                                      [1;2;3;4;5] = ([1;3;5], [2;4]).
   Proof. simpl. reflexivity. Qed.

   Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
   Proof. reflexivity. Qed.

   Fixpoint map {X Y: Type} (f:X -> Y) (l:list X) : (list Y) :=
     match l with
     | [] => []
     | h :: t => (f h) :: (map f t)
     end.

   Theorem map_app : forall (X Y: Type) (f : X -> Y) (l1 l2 : list X),
       map f (l1 ++ l2) = (map f l1) ++ (map f l2).

   Proof.
     intros X Y f l1 l2. induction l1 as [|n l1' IH].
     - reflexivity.
     - simpl. rewrite -> IH. reflexivity.
   Qed.
            
   Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
       map f (rev l) = rev (map f l).

   Proof.
     intros X Y f l. induction l as [|n l' IH].
     - reflexivity.
     - simpl. rewrite -> map_app. rewrite -> IH. reflexivity.
   Qed.

   Fixpoint flat_map { X Y : Type} (f: X -> list Y) (l: list X) : (list Y) :=
     match l with
     | [] => []
     | h :: t => (f h) ++ (flat_map f t)
     end.

   Example test_flat_map1:
     flat_map (fun n => [n;n;n]) [1;5;4]
     = [1; 1; 1; 5; 5; 5; 4; 4; 4].

   Proof. simpl. reflexivity. Qed.

   Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
     : option Y :=
     match xo with
     | None => None
     | Some x => Some (f x)
     end.

   Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
     : Y :=
     match l with
     |nil => b
     | h :: t => f h (fold f t b)
     end.

   Theorem silly1: forall (n m o p : nat),
       n = m -> [n;o] = [n;p] -> [n;o] = [m;p].

   Proof.
     intros n m o p eq1 eq2. rewrite <- eq1. apply eq2.
   Qed.

   Theorem silly2 : forall (n m o p : nat),
       n = m ->
       (n = m -> [n;o] = [m;p]) ->
       [n;o] = [m;p].
   
   Proof.
     intros n m o p eq1 eq2.
     apply eq2. apply eq1.  
   Qed.

   Theorem silly2a : forall (n m : nat),
       (n,n) = (m,m) ->
       (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) -> 
       [n] = [m].

     Proof.
       intros n m eq1 eq2. apply eq2. apply eq1.
     Qed.

     Theorem silly_ex :
       (forall n, evenb n = true -> oddb(S n) = true) ->
       evenb 2 = true -> oddb 3 = true.

     Proof.
       intros H1 H2. apply H1. apply H2.
     Qed.

     Theorem silly3_firsttry: forall (n : nat),
         true = (n =? 5) -> (S (S n)) =? 7 = true.

     Proof.
       intros n H. symmetry. simpl. apply H.
     Qed.

     Theorem rev_exercise1 : forall (l l' : list nat),
         l = rev l' -> l' = rev l.

     Proof.
       intros l l' H. rewrite H. symmetry. apply rev_involutive.
     Qed.

Example trans_eq_example : forall (a b c d e f : nat),
[a;b] = [c;d] ->
[c;d] = [e;f] ->
[a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2. rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(*acertar identac�o *)

Theorem trans_eq : forall (X:Type) (n m o : X),
    n = m -> m = o -> n = o.

Proof.
  intros X n m o eq1 eq2. rewrite eq1. rewrite eq2. reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->    
    [a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2. apply trans_eq with (m := [c;d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2. transitivity [c;d]. apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall ( n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).

Proof.
  intros n m o p eq1 eq2. transitivity m. apply eq2. apply eq1.
Qed.

Theorem S_injective : forall (n m : nat),
    S n = S m -> n = m.

Proof.
  intros n m H1. assert(H2: n = pred(S n)).
  { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
    S n = S m -> n = m.

Proof.
  intros n m H. injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
    [n; m] = [o; o] ->
    [n] = [m].

Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m o : nat),
    [n; m] = [o; o] ->    
    [n] = [m].

Proof.
  intros n m o H.
  injection H.
  intros H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    j = z :: l ->    
    x = y.

Proof.
  intros X x y z l j H1 H2. injection H1. rewrite H2. intros A B. rewrite B.
  injection A. intros C. symmetry. apply C.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n. destruct n as [|n'] eqn:E.
  - intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.

Proof.
  intros n contra. discriminate contra.
Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].

Proof.
  intros n m contra. discriminate contra.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.

Proof.
  intros X x y z l j H. discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.

Proof.
  intros A B f x y eq. rewrite eq. reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.

Proof.
  intros n m H. apply f_equal. apply H.
Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.

Proof. intros n m H. f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.
Qed.

Theorem eqb_true : forall n m,
    n =? m = true -> n = m.

Proof.
  intros n. induction n as [|n' IH].
  - intros m H. destruct m as [|m'] eqn: E.
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [|m'] eqn: E.
    + discriminate.
    + f_equal. apply IH. apply H.
Qed.

Theorem plus_Sn_Sm_then_n_m : forall n m,
    S n = S m -> n = m.
Proof.
  intros n. induction n as [|n' IH].
  - intros m H. destruct m as [|m'] eqn: E.
    + reflexivity.
    + discriminate.
  - intros m H. destruct m as [|m'] eqn: E.
    + discriminate.
    + injection H as H'. rewrite H'. reflexivity.
Qed.

Theorem plus_2Sn_2Sm_then_2n_2m : forall n m,
    S n + S n = S m + S m -> n + n = m + m.
Proof.
  intros n m. simpl. intros H. injection H as H'. rewrite <- plus_comm in H'.
  simpl in H'. symmetry in H'. rewrite -> plus_comm in H'. simpl in H'.
  injection H' as H''. symmetry in H''. apply H''.
Qed.  

Theorem plus_n_n_injective : forall n m,
    n + n = m + m -> n = m.

Proof.
  intros n. induction n as [|n' IH].
  - intros m H. destruct m as [|m'] eqn: E.
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [|m'] eqn: E.
    + discriminate.
    + f_equal. apply IH. apply plus_2Sn_2Sm_then_2n_2m in H. apply H.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.
Qed.

Fixpoint split' {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split' t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.
  

Check (1, 2).

Definition append_to_split' {X Y : Type} (a : (X * Y)) (l : (list X * list Y))
  : (list X * list Y) :=
  match l with
  | (x, y)  => (fst a :: x, snd a :: y)
  end.

Theorem append_n_to_split' :
  forall {X Y : Type} (a : (X * Y)) (l : list (X * Y)),
    split' (a :: l) = append_to_split' a (split' l).

Proof.
  intros X Y a l. destruct l.
  - destruct a. simpl. reflexivity.
  - destruct a. reflexivity.
Qed.

Notation "a ;+; l" := (append_to_split' a l) (at level 60, right associativity).

Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split' l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
   intros X Y l. induction l as [|n' l' IH].
   - intros l1 l2 H. simpl in H. injection H as A B.
     rewrite <- A. rewrite <- B. reflexivity.
   - intros l1 l2 H. simpl in H. destruct n' as [x y].
     destruct (split' l') as [xs' ys']. injection H. intros A B.
     rewrite <- A. rewrite <- B. simpl. rewrite IH.
     + reflexivity.
     + reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
       else false.
Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq. 
  destruct (n =? 3) eqn:Heqe3.
  apply eqb_true in Heqe3.
  rewrite -> Heqe3. reflexivity.
  destruct (n =? 5) eqn:Heqe5.
  apply eqb_true in Heqe5.
  rewrite Heqe5. reflexivity.
  discriminate eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b. destruct b eqn: Eb.
  - destruct (f true) eqn: Eft.
    + rewrite Eft. apply Eft.
    + destruct (f false) eqn: Eff.
      * apply Eft.
      * apply Eff.
  - destruct (f false) eqn: Eff1.
    + destruct (f true) eqn: Eft.
      * apply Eft.
      * apply Eff1.
    + rewrite -> Eff1. apply Eff1.
Qed.

Theorem eqb_n_n_eq_true : forall (n : nat),
    (n =? n) = true.
Proof.
  intros n. induction n as [|n IH].
  - reflexivity.
  - simpl. apply IH.
Qed.    
  
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n. induction n as [|n' IH].
  - intros m. destruct m.
    + reflexivity.
    + reflexivity.
  - intros m. destruct m.
    + reflexivity.
    + simpl. apply IH.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p eq1 eq2. apply eqb_true in eq1. apply eqb_true in eq2.
  rewrite eq1. rewrite eq2. apply eqb_n_n_eq_true.
Qed.

Theorem first_from_list : forall (X : Type) (a b : X) (l1 l2 : list X),
    a :: l1 = b :: l2 -> a = b.
Proof.
  intros X a b l1 l2 H. injection H as A B. apply A.
Qed.  
  
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.

Proof.
  intros X test x l lf. generalize dependent x. induction l as [|n' l' IH].
  - intros x H. simpl in H. discriminate H.
  - intros x H. simpl in H. destruct (test n') eqn: Etn.
    + apply first_from_list in H. rewrite H in Etn. apply Etn.
    + apply IH in H. apply H.
Qed.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  reflexivity. reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  apply HA.
  apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. split.
  - destruct n. reflexivity. discriminate.
  - destruct m. reflexivity. rewrite plus_comm in H. discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.

Proof.
  intros n m [Hm Hn]. rewrite Hm. rewrite Hn. reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
  intros n m H. apply and_exercise in H. destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split. apply HQ. apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).

Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.    

Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Check(not).

Fact not_implies_our_not : forall (P:Prop),
    ~P -> (forall (Q:Prop), P -> Q).
Proof.
 intros P H1 Q H2. destruct H1. apply H2.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not. intros contra. discriminate contra.
Qed.

Theorem not_False :
  ~False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q H. destruct H. unfold not in H0. apply H0 in H. destruct H.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G in H. destruct H.
Qed.  
  
Theorem contrapositive : forall (P Q : Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HQ. unfold not. intros P'. unfold not in HQ. apply H in P'.
  apply HQ in P'. destruct P'.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn: HE.
  - unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
  - reflexivity.
Qed.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.
Theorem disc : forall n, ~(O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.

