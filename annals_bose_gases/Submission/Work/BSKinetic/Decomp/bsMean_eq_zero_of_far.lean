import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic.Decomp

open MeasureTheory
open Submission.BoseGases

/-- A point of the centred cube `acube ℓ` (`ℓ > 0`) has norm at most `ℓ`: its coordinates are
bounded by `ℓ/2`, so `‖z‖² ≤ 3·(ℓ/2)² ≤ ℓ²`. -/
private lemma norm_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ acube ℓ) : ‖z‖ ≤ ℓ := by
  have hcomp : ∀ m : Fin 3, ‖z m‖ ≤ ℓ / 2 := by
    intro m
    have h := (mem_acube_iff ℓ z).mp hz m
    rw [Set.mem_Icc] at h
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hsq : ‖z‖ ^ 2 ≤ ℓ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖z i‖ ^ 2 ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2
      _ = 3 * (ℓ / 2) ^ 2 := by simp
      _ ≤ ℓ ^ 2 := by nlinarith [sq_nonneg ℓ]
  have h2 := sq_le_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg z), abs_of_nonneg (le_of_lt hℓ)] at h2
  exact h2

/-- If `ψ` vanishes outside the ball of radius `R` and `u` is so far away that the whole moving
box `Λ(u) = ℓu + acube ℓ` lies outside that ball (`R + ℓ ≤ ℓ‖u‖`), then the box mean of `ψ`
vanishes.  Indeed every `z ∈ acube ℓ` satisfies `‖z‖ ≤ ℓ`, hence
`‖ℓu + z‖ ≥ ℓ‖u‖ - ‖z‖ ≥ ℓ‖u‖ - ℓ ≥ R`, so `ψ (ℓu + z) = 0` throughout the box. -/
theorem bsMean_eq_zero_of_far {ℓ R : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ∀ x, R ≤ ‖x‖ → ψ x = 0) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : R + ℓ ≤ ℓ * ‖u‖) :
    Work.BSKinetic.bsMean ℓ u ψ = 0 := by
  unfold Work.BSKinetic.bsMean
  have hInt : ∫ z in acube ℓ, ψ (ℓ • u + z) = 0 := by
    have hcong : ∫ z in acube ℓ, ψ (ℓ • u + z) = ∫ z in acube ℓ, (0 : ℝ) := by
      apply setIntegral_congr_fun (acube_measurable ℓ)
      intro z hz
      apply hψ
      have hzℓ : ‖z‖ ≤ ℓ := norm_le_of_mem_acube hℓ hz
      have h1 : ‖ℓ • u‖ = ℓ * ‖u‖ := by
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt hℓ)]
      have h2 : ‖ℓ • u‖ - ‖z‖ ≤ ‖ℓ • u + z‖ := by
        have h := norm_sub_le (ℓ • u + z) z
        simp only [add_sub_cancel_right] at h
        linarith
      calc R ≤ ℓ * ‖u‖ - ℓ := by linarith
        _ = ‖ℓ • u‖ - ℓ := by rw [h1]
        _ ≤ ‖ℓ • u‖ - ‖z‖ := by linarith
        _ ≤ ‖ℓ • u + z‖ := h2
    rw [hcong]
    simp
  rw [hInt, mul_zero]

end Work.BSKinetic.Decomp
