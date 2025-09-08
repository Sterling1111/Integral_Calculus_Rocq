Require Import Imports Sets Relations Notations Functions.
Import SetNotations RelationNotations.
Require Export Chapter19.

Open Scope R_scope.
Set Printing Coercions.

Section section_20_3.
  Let R := ❴ (x, y) ∈ ℝ ⨯ ℝ | x * y < 0 ❵.

  Lemma lemma_20_3_c_1 : ~ Reflexive R.
  Proof.
    unfold R, mk_relation, Reflexive. intros H1. specialize (H1 1). lra.
  Qed. 

  Lemma lemma_20_3_c_2 : Symmetric R.
  Proof.
    unfold Symmetric, R, mk_relation. intros x y H1. lra.
  Qed.

  Lemma lemma_20_3_c_3 : ~ Transitive R.
  Proof.
    unfold Transitive, R, mk_relation. intros H1. specialize (H1 (-1) 1 (-1)). lra.
  Qed.

  Lemma lemma_20_c_c_4 : ~ Antisymmetric R.
  Proof.
    unfold Antisymmetric, R, mk_relation. intros H1. specialize (H1 1 (-1)). lra.
  Qed.
End section_20_3.

Section section_20_4.
  Let R := ❴ (x, y) ∈ ℝ ⨯ ℝ | exists z, IZR z = x - y ❵.

  Lemma lemma_20_4_c_1 : Reflexive R.
  Proof.
    unfold Reflexive, R, mk_relation. intros x. exists 0%Z. lra.
  Qed.

  Lemma lemma_20_4_c_2 : Symmetric R.
  Proof.
    unfold Symmetric, R, mk_relation. intros x y [z H1]. exists (-z)%Z. rewrite opp_IZR. lra.
  Qed.

  Lemma lemma_20_4_c_3 : Transitive R.
  Proof.
    unfold Transitive, R, mk_relation. intros x y z [m H1] [n H2]. exists (m + n)%Z. rewrite plus_IZR. lra.
  Qed.

  Lemma lemma_20_4_c_4 : ~Antisymmetric R.
  Proof.
    unfold Antisymmetric, R, mk_relation. intros H1. specialize (H1 1 2 ltac:(exists (-1)%Z; lra) ltac:(exists 1%Z; lra)). lra.
  Qed.
End section_20_4.

Section section_20_5.
  Open Scope Z_scope.
  Let R := ❴ (a, b) ∈ ℤ ⨯ ℤ | Z.Even (a - b) ❵.

  Lemma lemma_20_5_b_1 : Reflexive R.
  Proof.
    unfold Reflexive, R, mk_relation. intros x. exists 0%Z. rewrite Z.sub_diag. lia.
  Qed.

  Lemma lemma_20_5_b_2 : Symmetric R.
  Proof.
    unfold Symmetric, R, mk_relation. intros x y [z H1]. exists (-z)%Z. lia.
  Qed.

  Lemma lemma_20_5_b_3 : Transitive R.
  Proof.
    unfold Transitive, R, mk_relation. intros x y z [m H1] [n H2]. exists (m + n)%Z. lia.
  Qed.

  Lemma lemma_20_5_c : ~ Antisymmetric R.
  Proof.
    unfold Antisymmetric, R, mk_relation. intros H1. specialize (H1 4 2 ltac:(exists 1%Z; lia) ltac:(exists (-1)%Z; lia)). lia.
  Qed.

  Lemma lemma_20_5_d : forall b, 
    R 1 b <-> Z.Odd b.
  Proof.
    unfold R, mk_relation. intros b. split; intros H1.
    - apply even_minus_Z in H1 as [[[k H1] _] | H1]; [lia | tauto].
    - apply even_minus_Z. right. split; auto. exists 0. lia.
  Qed.
End section_20_5.

(*
Section section_20_6.
  Let A : Ensemble ℝ := ⦃ 1, 2, 3 ⦄.
  Let Ra : Relation ℝ ℝ := ⦃ (1, 1), (2, 2), (3, 3) ⦄.

  Lemma lemma_20_6_a : Reflexive_On Ra A.
  Proof.
    unfold Reflexive_On, Ra, A. intros x H1. rewrite <- x_y_In_implies_rel. rewrite ens_rel_ens_id.
    destruct_all_finitesets; autoset. simpl in *. unfold Ensembles.In in *. destruct_all_finitesets; autoset.
  Qed.

End section_20_6.
*)

Definition disjoint_pieces {A} (P : Ensemble (Ensemble A)) : Prop :=
  forall E1 E2, E1 ∈ P -> E2 ∈ P -> E1 ⋂ E2 = ∅.
Definition nonempty_pieces {A} (P : Ensemble (Ensemble A)) : Prop :=
  forall E, E ∈ P -> E ≠ ∅.
Definition covering {A} (P : Ensemble (Ensemble A)) : Prop :=
  forall x : A, exists E, E ∈ P /\ x ∈ E.
Definition partition {A} (E : Ensemble (Ensemble A)) : Prop :=
  disjoint_pieces E /\ nonempty_pieces E /\ covering E.