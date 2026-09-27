import Mathlib
import Submission.Work.EKLComp.Core

/-!
# Submodularity of the Shannon entropy form `negMulLog`

For a nonnegative function `w : ι → κ → ρ → ℝ` with total mass `1`, the Shannon-entropy
submodularity inequality `H(X,Y,Z) + H(X) ≤ H(X,Y) + H(X,Z)` reads

  `∑ᵢⱼₖ negMulLog (w i j k) + ∑ᵢ negMulLog (∑ⱼₖ w i j k)
     ≤ ∑ᵢⱼ negMulLog (∑ₖ w i j k) + ∑ᵢₖ negMulLog (∑ⱼ w i j k)`.

It is the nonnegativity of the conditional mutual information
`I(Y ; Z | X) = ∑ᵢⱼₖ w i j k · log (w i j k · pᵢ / (pᵢⱼ · pᵢₖ))`, which is a single
application of the finite Gibbs inequality `Core.sum_mul_log_div_nonneg` to the joint
distribution and the "conditionally independent" distribution
`x ↦ pᵢⱼ · pᵢₖ / pᵢ`.
-/

namespace Work.EKLComp

open Finset

/-- `negMulLog` of a finite total mass equals the sum of the contributions of its atoms. -/
private lemma negMulLog_sum_eq {α : Type*} [Fintype α] (f : α → ℝ) :
    Real.negMulLog (∑ a, f a) = ∑ a, f a * (-Real.log (∑ b, f b)) := by
  rw [Real.negMulLog, ← Finset.sum_mul]
  ring

/-- The pointwise identity behind the conditional mutual information: for
`0 ≤ P ≤ M₁, M₂, M₃`,
`P log P + P log M₁ - P log M₂ - P log M₃ = P log (P / (M₂ M₃ / M₁))`. -/
private lemma key_id {P M1 M2 M3 : ℝ} (hP : 0 ≤ P) (h1 : P ≤ M1) (h2 : P ≤ M2)
    (h3 : P ≤ M3) :
    P * (-Real.log M2) + P * (-Real.log M3) - Real.negMulLog P - P * (-Real.log M1)
      = P * Real.log (P / (M2 * M3 / M1)) := by
  rcases eq_or_lt_of_le hP with hP0 | hPpos
  · rw [← hP0]; simp [Real.negMulLog]
  · have hM1 : 0 < M1 := lt_of_lt_of_le hPpos h1
    have hM2 : 0 < M2 := lt_of_lt_of_le hPpos h2
    have hM3 : 0 < M3 := lt_of_lt_of_le hPpos h3
    rw [Real.negMulLog, div_div_eq_mul_div,
        Real.log_div (ne_of_gt (mul_pos hPpos hM1)) (ne_of_gt (mul_pos hM2 hM3)),
        Real.log_mul (ne_of_gt hPpos) (ne_of_gt hM1),
        Real.log_mul (ne_of_gt hM2) (ne_of_gt hM3)]
    ring

/-- Factorising a double sum of a product divided by a constant. -/
private lemma sum_sum_mul_div {α β : Type*} [Fintype α] [Fintype β]
    (a : α → ℝ) (b : β → ℝ) (c : ℝ) :
    (∑ i, ∑ j, a i * b j / c) = (∑ i, a i) * (∑ j, b j) / c := by
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_div, ← Finset.mul_sum]

/-- **Submodularity of `Real.negMulLog` over a triple product.** -/
theorem negMulLog_sum_submodular {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (w : ι → κ → ρ → ℝ) (hw : ∀ i j k, 0 ≤ w i j k)
    (hsum : ∑ i, ∑ j, ∑ k, w i j k = 1) :
    (∑ i, ∑ j, ∑ k, Real.negMulLog (w i j k))
        + (∑ i, Real.negMulLog (∑ j, ∑ k, w i j k))
      ≤ (∑ i, ∑ j, Real.negMulLog (∑ k, w i j k))
        + (∑ i, ∑ k, Real.negMulLog (∑ j, w i j k)) := by
  classical
  -- Rewrite each of the four entropy sums as a sum over `ι × κ × ρ` using the
  -- appropriate marginal as a weight.
  have e1 : (∑ i, ∑ j, ∑ k, Real.negMulLog (w i j k))
      = ∑ x : ι × κ × ρ, Real.negMulLog (w x.1 x.2.1 x.2.2) := by
    symm; simp only [Fintype.sum_prod_type]
  have e2 : (∑ i, Real.negMulLog (∑ j, ∑ k, w i j k))
      = ∑ x : ι × κ × ρ, w x.1 x.2.1 x.2.2 * (-Real.log (∑ j, ∑ k, w x.1 j k)) := by
    symm
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    rw [negMulLog_sum_eq (f := fun j => ∑ k, w i j k)]
    simp only [← Finset.sum_mul]
  have e3 : (∑ i, ∑ j, Real.negMulLog (∑ k, w i j k))
      = ∑ x : ι × κ × ρ, w x.1 x.2.1 x.2.2 * (-Real.log (∑ k, w x.1 x.2.1 k)) := by
    symm
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [negMulLog_sum_eq]
  have e4 : (∑ i, ∑ k, Real.negMulLog (∑ j, w i j k))
      = ∑ x : ι × κ × ρ, w x.1 x.2.1 x.2.2 * (-Real.log (∑ j, w x.1 j x.2.2)) := by
    symm
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [negMulLog_sum_eq]
  -- Nonnegativity of the marginals and of the joint weight.
  have hM1nn : ∀ x : ι × κ × ρ, 0 ≤ ∑ j, ∑ k, w x.1 j k :=
    fun x => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hw x.1 j k))
  have hM2nn : ∀ x : ι × κ × ρ, 0 ≤ ∑ k, w x.1 x.2.1 k :=
    fun x => Finset.sum_nonneg (fun k _ => hw x.1 x.2.1 k)
  have hM3nn : ∀ x : ι × κ × ρ, 0 ≤ ∑ j, w x.1 j x.2.2 :=
    fun x => Finset.sum_nonneg (fun j _ => hw x.1 j x.2.2)
  have hPnn : ∀ x : ι × κ × ρ, 0 ≤ w x.1 x.2.1 x.2.2 := fun x => hw x.1 x.2.1 x.2.2
  -- The joint weight is bounded by each marginal.
  have hM1ge : ∀ x : ι × κ × ρ,
      w x.1 x.2.1 x.2.2 ≤ ∑ j, ∑ k, w x.1 j k := fun x =>
    le_trans (Finset.single_le_sum (fun k _ => hw x.1 x.2.1 k) (Finset.mem_univ x.2.2))
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun k _ => hw x.1 j k))
        (Finset.mem_univ x.2.1))
  have hM2ge : ∀ x : ι × κ × ρ,
      w x.1 x.2.1 x.2.2 ≤ ∑ k, w x.1 x.2.1 k :=
    fun x => Finset.single_le_sum (fun k _ => hw x.1 x.2.1 k) (Finset.mem_univ x.2.2)
  have hM3ge : ∀ x : ι × κ × ρ,
      w x.1 x.2.1 x.2.2 ≤ ∑ j, w x.1 j x.2.2 :=
    fun x => Finset.single_le_sum (fun j _ => hw x.1 j x.2.2) (Finset.mem_univ x.2.1)
  -- The two weights `P` and `Q = M₂ M₃ / M₁` are probability distributions on `ι × κ × ρ`.
  have hPsum : (∑ x : ι × κ × ρ, w x.1 x.2.1 x.2.2) = 1 := by
    simp only [Fintype.sum_prod_type]; exact hsum
  have hQsum : (∑ x : ι × κ × ρ,
        (∑ k, w x.1 x.2.1 k) * (∑ j, w x.1 j x.2.2) / (∑ j, ∑ k, w x.1 j k)) = 1 := by
    simp only [Fintype.sum_prod_type]
    have key : ∀ i, (∑ j, ∑ k, (∑ k', w i j k') * (∑ j', w i j' k) / (∑ j', ∑ k', w i j' k'))
          = ∑ j, ∑ k, w i j k := by
      intro i
      rw [sum_sum_mul_div]
      have hA : (∑ j, ∑ k', w i j k') = ∑ j, ∑ k, w i j k := rfl
      have hB : (∑ k, ∑ j', w i j' k) = ∑ j, ∑ k, w i j k := Finset.sum_comm
      have hC : (∑ j', ∑ k', w i j' k') = ∑ j, ∑ k, w i j k := rfl
      rw [hA, hB, hC]
      exact mul_self_div_self _
    calc ∑ i, (∑ j, ∑ k, (∑ k', w i j k') * (∑ j', w i j' k) / (∑ j', ∑ k', w i j' k'))
        = ∑ i, ∑ j, ∑ k, w i j k := Finset.sum_congr rfl (fun i _ => key i)
      _ = 1 := hsum
  have hQnn : ∀ x : ι × κ × ρ,
      0 ≤ (∑ k, w x.1 x.2.1 k) * (∑ j, w x.1 j x.2.2) / (∑ j, ∑ k, w x.1 j k) :=
    fun x => div_nonneg (mul_nonneg (hM2nn x) (hM3nn x)) (hM1nn x)
  have hpos : ∀ x : ι × κ × ρ, 0 < w x.1 x.2.1 x.2.2 →
      0 < (∑ k, w x.1 x.2.1 k) * (∑ j, w x.1 j x.2.2) / (∑ j, ∑ k, w x.1 j k) := fun x hx =>
    div_pos (mul_pos (lt_of_lt_of_le hx (hM2ge x)) (lt_of_lt_of_le hx (hM3ge x)))
      (lt_of_lt_of_le hx (hM1ge x))
  -- Gibbs' inequality: the (conditional) mutual information is nonnegative.
  have hgibbs : 0 ≤ ∑ x : ι × κ × ρ, w x.1 x.2.1 x.2.2 *
      Real.log (w x.1 x.2.1 x.2.2 /
        ((∑ k, w x.1 x.2.1 k) * (∑ j, w x.1 j x.2.2) / (∑ j, ∑ k, w x.1 j k))) :=
    Core.sum_mul_log_div_nonneg
      (fun x : ι × κ × ρ => w x.1 x.2.1 x.2.2)
      (fun x : ι × κ × ρ => (∑ k, w x.1 x.2.1 k) * (∑ j, w x.1 j x.2.2) / (∑ j, ∑ k, w x.1 j k))
      hPnn hQnn (hPsum.trans hQsum.symm) hpos
  -- Identify the difference of the two sides of the target with that mutual information.
  have hid : (∑ i, ∑ j, Real.negMulLog (∑ k, w i j k))
        + (∑ i, ∑ k, Real.negMulLog (∑ j, w i j k))
        - (∑ i, ∑ j, ∑ k, Real.negMulLog (w i j k))
        - (∑ i, Real.negMulLog (∑ j, ∑ k, w i j k))
      = ∑ x : ι × κ × ρ, w x.1 x.2.1 x.2.2 *
          Real.log (w x.1 x.2.1 x.2.2 /
            ((∑ k, w x.1 x.2.1 k) * (∑ j, w x.1 j x.2.2) / (∑ j, ∑ k, w x.1 j k))) := by
    rw [e1, e2, e3, e4]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    exact key_id (hPnn x) (hM1ge x) (hM2ge x) (hM3ge x)
  have hDnn : 0 ≤ (∑ i, ∑ j, Real.negMulLog (∑ k, w i j k))
        + (∑ i, ∑ k, Real.negMulLog (∑ j, w i j k))
        - (∑ i, ∑ j, ∑ k, Real.negMulLog (w i j k))
        - (∑ i, Real.negMulLog (∑ j, ∑ k, w i j k)) := by
    rw [hid]; exact hgibbs
  linarith [hDnn]

end Work.EKLComp
