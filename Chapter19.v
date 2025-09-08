Require Import Imports QRT Prime Notations.

Require Export Chapter18.

Open Scope Z_scope.

Section section19_1.
  Import String.

  Fixpoint element_divides (z : Z) (l : list Z) : bool := 
  match l with 
  | [] => false
  | h :: t => if Z.eqb (Z.rem z h) 0 then true else element_divides z t
  end.

  Lemma Z_rem_0 : forall z : Z, Z.rem z 0 = z.
  Proof.
    intros z.
    unfold Z.rem, Z.quotrem. destruct z; reflexivity.
  Qed.

  Lemma element_divides_correct : forall z l, element_divides z l = true -> exists x, In x l /\ (x | z).
  Proof.
    intros z l H1. induction l as [| h t IH].
    - inversion H1.
    - simpl in H1. destruct (Z.rem z h =? 0) eqn:Heq.
      -- assert (h = 0 \/ h <> 0) as [H2 | H2]; assert (z = 0 \/ z <> 0) as [H3 | H3]; try lia; subst.
        * exists 0. split. left. reflexivity. apply Z.divide_0_r.
        * assert (Z.rem z 0 = z) as H4 by apply Z_rem_0. lia.
        * exists h. split. left. reflexivity. exists 0; lia.
        * exists h. split. left. reflexivity. apply Z.rem_divide; lia.
      -- apply IH in H1. destruct H1 as [x [H4 H5]]. exists x. split; [right | auto]; auto.
  Qed.

  Definition is_prime (z : Z) (first_primes : list Z) : list Z := 
    if z <? 2 then [] else
    if z =? 2 then [2] else
    if (element_divides z first_primes) then first_primes else z :: first_primes.

  Definition find_primes_le (n : nat) : list Z := 
    List.rev (fold_left (fun l z => is_prime z l) (Zseq_pos (seq 2 (n-1))) []).

  Fixpoint count_divisors (n p : Z) (count : nat) {struct count} : nat :=
    match count with
    | O => 0
    | S count' =>
      if (n mod p =? 0)%Z then S (count_divisors (n / p) p count')
      else 0
    end.

  Definition canonical_prime_factorization_list (n : nat) : list (Z * Z) := 
    let l := find_primes_le n in
    let l' := filter (fun x => Z.rem (Z.of_nat n) x =? 0) l in
    map (fun p => (p, Z.of_nat (count_divisors (Z.of_nat n) p (n)))) l'.

  Open Scope string_scope.

  Definition canonical_prime_factorization_string (n : nat) : string := 
    let l := canonical_prime_factorization_list n in
    let s := Z_to_string (Z.of_nat n) ++ " = " ++ fold_left (fun s p => s ++ Z_to_string (fst p) ++ "^" ++ Z_to_string (snd p) ++ "*") l "" in
    String.substring 0 (String.length s - 1) s.

  Close Scope string_scope.

  Compute canonical_prime_factorization_string 27.
  Compute canonical_prime_factorization_string 3072.
  Compute canonical_prime_factorization_string 60.

End section19_1.

Lemma lemma_19_2 : forall p l,
  Znt.prime p -> (p | fold_right Z.mul 1 l) -> exists x, In x l /\ (p | x).
Proof.
  apply theorem_19_6.
Qed.

Open Scope list_scope.

Lemma lemma_19_3 : forall n,
  n > 1 -> exists p, Znt.prime p /\ (p | n) /\ forall d, (d | n) -> d > 1 -> p <= d.
Proof.
  intros n H1. pose proof (theorem_19_9 n H1) as [l [[H2 [H3 H4]] H5]]. assert (length l = 0 \/ length l > 0)%nat as [H6 | H6] by lia.
  - rewrite length_zero_iff_nil in H6. subst. simpl in H1. lia.
  - exists (nth 0 l 0); split; [ | split].
    -- unfold prime_list in H2. rewrite Forall_forall in H2. assert (In (nth 0 l 0) l) as H7. { apply nth_In. lia. }
       specialize (H2 _ H7); apply H2.
    -- rewrite H4. destruct l; [simpl in *; lia | simpl; apply Z.divide_factor_l].
    -- intros d H7 H8. assert (nth 0 l 0 <= d \/ nth 0 l 0 > d) as [H9 | H9]; try lia.
       pose proof theorem_19_7 _ H8 as [p [H10 H11]]. pose proof Z.divide_trans _ _ _ H11 H7 as H12.
       rewrite H4 in H12. pose proof lemma_19_2 _ _ H10 H12 as [x [H13 H14]]. unfold prime_list in H2. 
       rewrite Forall_forall in H2. specialize (H2 _ H13). apply Znt.prime_alt in H2 as [H2_pos H2].
       assert (nth 0 l 0 <= x) as H15.
       {
          destruct l. simpl in *; lia. assert (x = z \/ x <> z) as [H15 | H15] by lia. simpl. lia.
          destruct H13 as [H13 | H13]; try lia. pose proof (Sorted_cons_In l _ _ H3 H13) as H16; simpl; lia. 
       }
       destruct H10 as [H10 _]. apply Z.divide_pos_le in H11; try lia. specialize (H2 p ltac:(lia)). tauto.
Qed.

Lemma lemma_19_4_a : forall p : Z,
  Znt.prime p -> p <> 3 -> p ≡ 1 (mod 3) \/ p ≡ -1 (mod 3).
Proof.
  intros p H1 H2. apply Znt.prime_alt in H1 as [H1 H3]. assert (p = 2 \/ p > 3) as [H4 | H4] by lia.
  - right. exists 1. lia.
  - unfold Zmod_equiv. assert (exists k, p = 3 * k \/ p = 3 * k + 1 \/ p = 3 * k + 2) as [k [H5 | [H5 | H5]]] by zforms.
    -- assert (3 | p) as H6. { subst; apply Z.divide_factor_l. } specialize (H3 3 ltac:(lia) H6). lia.
    -- left. exists k. lia.
    -- right. exists (k + 1). lia.
Qed.

Lemma lemma_19_4_b : forall l,
  (forall i, (0 <= i < length l)%nat -> nth i l 0 ≡ 1 (mod 3)) -> fold_right Z.mul 1 l ≡ 1 (mod 3).
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. exists 0. lia.
  - simpl. destruct t as [| h' t].
    -- simpl. rewrite Z.mul_1_r. apply (H1 0%nat). simpl. lia.
    -- assert (H2 : (forall i : ℕ, (0 <= i < length (h' :: t))%nat -> nth i (h' :: t) 0 ≡ 1 (mod 3))).
       {
          intros i H2. pose proof H1 as H3. specialize (H1 i ltac:(simpl in *; lia)).
          assert (i = 0 \/ i > 0)%nat as [H4 | H4] by lia.
          - subst. simpl. apply (H3 1%nat); simpl; lia.
          - apply (H3 (S i)). simpl in *; lia.
       }
       specialize (IH H2). specialize (H1 0%nat ltac:(simpl; lia)). simpl in H1. destruct IH as [k H3]. destruct H1 as [k' H4].
       replace (fold_right Z.mul 1 (h' :: t)) with (k * 3 + 1) by lia. replace h with (3 * k' + 1) by lia.
       replace ((3 * k' + 1) * (k * 3 + 1)) with (3 * (3 * k' * k + k' + k) + 1) by lia. exists (3 * k' * k + k' + k). lia.
Qed.

Lemma contra_3 : forall P Q R,
  (~P \/ ~Q \/ ~R) <-> ~ (P /\ Q /\ R).
Proof.
  intros P Q R. tauto.
Qed.

Lemma fold_right_cons : forall a l,
  fold_right Z.mul 1 (a :: l) = a * fold_right Z.mul 1 l.
Proof.
  intros a l. reflexivity.
Qed.

Lemma fold_right_Zmul_all_eq : forall l a,
  (length l > 0)%nat -> (forall x, In x l -> x = a) -> fold_right Z.mul 1 l = Zpower_nat a (length l).
Proof.
  intros l a H1 H2. induction l as [| h t IH].
  - simpl in H1. lia.
  - simpl. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
    -- rewrite length_zero_iff_nil in H3. subst. simpl. rewrite (H2 h); (simpl; lia).
    -- rewrite IH; try lia. 2 : { intros x H4. apply H2. right. auto. } rewrite (H2 h); (simpl; lia).
Qed.

Lemma a_divides_fold_right_Zmult_all_eq : forall l a,
  (length l > 0)%nat -> (forall x, In x l -> x = a) -> (a | fold_right Z.mul 1 l).
Proof.
  intros l a H1 H2. rewrite fold_right_Zmul_all_eq with (a := a); auto. exists (Zpower_nat a (length l - 1)). simpl.
  replace (length l) with (S (length l - 1)) at 1 by lia. rewrite Zpower_nat_succ_r. lia.
Qed.

Lemma in_divides_Zmul_fold_right : forall l a,
  In a l -> (a | fold_right Z.mul 1 l).
Proof.
  intros l a H1. induction l as [| h t IH].
  - simpl in H1. lia.
  - simpl. assert (h = a \/ In a t) as [H2 | H2] by auto.
    -- subst. exists (fold_right Z.mul 1 t). lia.
    -- apply IH in H2. destruct H2 as [x H2]. exists (x * h). lia.
Qed.

Lemma not_congruent_3n : forall n,
  ~(3 * n ≡ -1 (mod 3)).
Proof.
  intros n H1. unfold Zmod_equiv in H1. destruct H1 as [k H1]. lia.
Qed.

Lemma lemma_19_4_c : forall n,
  n > 1 -> n ≡ -1 (mod 3) -> exists p, (p | n) /\ Znt.prime p /\ p ≡ -1 (mod 3).
Proof.
  intros n H1 H2. pose proof classic (exists p, (p | n) /\ Znt.prime p /\ p ≡ -1 (mod 3)) as [H3 | H3]; auto.
  assert (H4 : forall p, (~(p | n) \/ ~Znt.prime p \/ ~p ≡ -1 (mod 3))). 
  { intros p. apply contra_3. intros [H4 [H5 H6]]. apply H3. exists p. tauto. }
  clear H3. rename H4 into H3. apply theorem_19_8 in H1 as [l [H4 H5]].
  pose proof classic ((forall i, (0 <= i < length l)%nat -> nth i l 0 ≡ 1 (mod 3))) as [H6 | H6].
  - apply lemma_19_4_b in H6. rewrite <- H5 in H6. exists (nth 0 l 0). destruct l; simpl in *; destruct H2 as [k H2]; try lia.
    destruct H6 as [j H6]; lia.
  - apply not_all_ex_not in H6 as [i H6]. apply imply_to_and in H6 as [H6 H7]. destruct l. simpl in *. lia.
    assert (nth i (z :: l) 0 <> 3) as H8.
    { 
      intros H8. assert (In (nth i (z :: l) 0) (z :: l)) as H9. { apply nth_In; lia. } 
      apply in_divides_Zmul_fold_right in H9 as [k H9]. rewrite H9, H8 in H5. rewrite Z.mul_comm in H5.
      rewrite H5 in H2. apply not_congruent_3n in H2. auto.
    }
    assert (In (nth i (z :: l) 0) (z :: l)) as H9. { apply nth_In; lia. }
    exists (nth i (z :: l) 0). split; [ | split].
    -- rewrite H5. apply in_divides_Zmul_fold_right; auto.
    -- unfold prime_list in H4. rewrite Forall_forall in H4. apply H4. auto.
    -- apply lemma_19_4_a in H8 as [H8 | H8]; try tauto. unfold prime_list in H4. rewrite Forall_forall in H4.
       apply H4; auto.
Qed.

Lemma lemma_19_4_d : forall l,
  prime_list l -> Forall (fun p => p ≡ -1 (mod 3)) l -> exists p, p ≡ -1 (mod 3) /\ ~ In p l.
Proof.
  intros l H1 H2. set (n := -1 + 3 * fold_right Z.mul 1 l). pose proof (prime_list_product_gt_1 l H1) as H3.
  assert (H4 : n > 1) by lia. apply lemma_19_4_c in H4 as [q [H5 [H6 H7]]].
  2 : { exists (fold_right Z.mul 1 l). lia. } exists q. split; auto. intros H8. apply in_divides_Zmul_fold_right in H8 as [k H8].
  apply Z.mul_cancel_l with (p := 3) in H8; try lia. replace (3 * fold_right Z.mul 1 l) with (n + 1) in H8 by lia.
  assert (q | 1) as H9. { apply Z.divide_add_cancel_r with (m := n). auto. exists (3 * k). lia. }
  destruct H6 as [H6 _]. destruct H9 as [j H9]. apply Z.eq_sym in H9. rewrite Z.mul_comm in H9. apply Znt.Zmult_one in H9; try lia.
Qed.