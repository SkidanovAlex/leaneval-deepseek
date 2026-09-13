/-
# The Harnack inequality for the small-perturbation equation (Savin, Theorem 1.1)

This file contains the *non-uniform* form of Savin's Harnack inequality, derived from the uniform
form `harnack_uniform` of `Submission.Savin.HarnackUniform` (where the constant depends on the base
`A` only through the bound `2 trOp (cofOp A) / c ≤ Y`).  All the helper lemmas live in
`Submission.Savin.HarnackUniform` and remain available through this import.
-/
import Submission.Savin.HarnackUniform

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- **Savin's Harnack inequality** for the small-perturbation equation (Theorem 1.1 of
*Small perturbation solutions for elliptic equations*, CPDE 32 (2007)). -/
theorem harnack {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1) (htrA : 0 < trOp A)
    {c c' : ℝ} (hc : 0 < c) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {p M : ℝ} (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℝ⁴ → ℝ) (ε Λ : ℝ), 0 < ε → 0 < Λ →
      ContDiffOn ℝ 2 Φ (ball 0 (5 / 2)) →
      (∀ x ∈ ball 0 (5 / 2), s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball 0 (5 / 2), 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball 0 (5 / 2), 0 ≤ Φ x) → (∀ x ∈ ball 0 (5 / 2), Φ x ≤ Λ) → Φ 0 ≤ ε →
      768 * Λ * 2 ^ (2 * p + 4) ≤ c → 1536 * ε * M ≤ c →
      ∀ x ∈ closedBall 0 (1 / 6), Φ x ≤ C * ε := by
  have hc'pos : 0 < c' := by
    have h1 := hcq (stdB4 0)
    have h2 := hcq' (stdB4 0)
    have h3 : ‖stdB4 0‖ = 1 := stdB4.orthonormal.1 0
    simp only [h3, one_pow, mul_one] at h1 h2
    linarith
  have htrCo : 0 ≤ trOp (cofOp A) := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2, hc]
  have hYnn : 0 ≤ 2 * trOp (cofOp A) / c := div_nonneg (by linarith [htrCo]) hc.le
  obtain ⟨C, hCpos, hC⟩ :=
    harnack_uniform (Y := 2 * trOp (cofOp A) / c) hc hc'pos hYnn hp hM1 hM hpbig
  exact ⟨C, hCpos, hC A hA hA1 htrA hcq hcq' le_rfl⟩

end

end Submission
