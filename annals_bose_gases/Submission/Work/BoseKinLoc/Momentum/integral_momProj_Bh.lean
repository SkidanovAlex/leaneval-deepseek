import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseKinLoc.Momentum.boxHat_eq_cubFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.integral_momProj_Bh`

The `p`-integral of the sliding symbol.  In the `boxHat` normalisation

  `Bh ℓ q p = boxHat ℓ (q − p) − ℓ⁻³ boxHat ℓ p · boxHat ℓ q`,

and with the dilation law `boxHat ℓ r = ℓ³ · cubFT (ℓ • r)` (`boxHat_eq_cubFT`) this becomes

  `Bh ℓ q p = ℓ³ · (cubFT (ℓ•q − ℓ•p) − cubFT (ℓ•p) · cubFT (ℓ•q))`.

Since `cubFT` is even (`cubFT_sub_comm`), the square equals `ℓ⁶` times the scale-free block
`(cubFT (w − ℓ•q) − cubFT (ℓ•q) · cubFT w)²` evaluated at `w = ℓ • p`.  The `p`-cut-off
`momProj ℓ d p = 1_{(d²ℓ)⁻¹,∞)}(‖p‖)` is exactly the indicator of
`{(d²)⁻¹ < ‖·‖}` pulled back along `p ↦ ℓ • p` (`ℓ > 0`), so the change of variables
`w = ℓ • p` (Jacobian `ℓ³`, `Measure.integral_comp_smul_of_nonneg`) turns the `p`-integral into
the `w`-integral over the exterior of the ball of radius `d⁻²`, with the net factor
`ℓ⁶ · ℓ⁻³ = ℓ³`.

Every step is unconditional: the Bochner-integral change of variables
`Measure.integral_comp_smul_of_nonneg` needs no integrability hypothesis, and
`integral_const_mul` / `integral_indicator` are likewise unconditional, so the identity holds
as stated for all `q`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

set_option autoImplicit false
set_option linter.unusedVariables false

theorem integral_momProj_Bh (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) (q : EuclideanSpace ℝ (Fin 3)) : ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p * (Work.BoseKinLoc.Momentum.Bh ℓ q p) ^ 2 = ℓ ^ 3 * ∫ w in {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖}, (Work.BoseKinLoc.Momentum.cubFT (w - ℓ • q) - Work.BoseKinLoc.Momentum.cubFT (ℓ • q) * Work.BoseKinLoc.Momentum.cubFT w) ^ 2 := by
  -- The pointwise identity: the integrand is `ℓ⁶` times the (indicator of the exterior set
  -- composed with `p ↦ ℓ • p`) applied to the scale-free block.
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p * (Bh ℓ q p) ^ 2
      = ℓ ^ 6 * (Set.indicator {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖}
          (fun w => (cubFT (w - ℓ • q) - cubFT (ℓ • q) * cubFT w) ^ 2)) (ℓ • p) := by
    intro p
    -- dilation law for the sliding symbol
    have hBh : Bh ℓ q p
        = ℓ ^ 3 * (cubFT (ℓ • q - ℓ • p) - cubFT (ℓ • p) * cubFT (ℓ • q)) := by
      unfold Bh
      rw [boxHat_eq_cubFT hℓ (q - p), boxHat_eq_cubFT hℓ p, boxHat_eq_cubFT hℓ q, smul_sub]
      have h3 : (ℓ ^ 3)⁻¹ * ℓ ^ 3 = 1 := inv_mul_cancel₀ (pow_ne_zero 3 hℓ.ne')
      rw [← mul_assoc, ← mul_assoc, h3, one_mul]
      ring
    -- evenness of `cubFT` identifies the block at `ℓ • p` with the one appearing in `hBh`
    have hH : (cubFT (ℓ • p - ℓ • q) - cubFT (ℓ • q) * cubFT (ℓ • p)) ^ 2
        = (cubFT (ℓ • q - ℓ • p) - cubFT (ℓ • p) * cubFT (ℓ • q)) ^ 2 := by
      rw [cubFT_sub_comm (ℓ • p) (ℓ • q)]
      ring
    -- the two cut-offs agree: `‖ℓ•p‖ = ℓ‖p‖` and `ℓ * (d²ℓ)⁻¹ = (d²)⁻¹`
    have hkey : ℓ * (d ^ 2 * ℓ)⁻¹ = (d ^ 2)⁻¹ := by
      rw [mul_inv]; field_simp
    by_cases hp : (d ^ 2 * ℓ)⁻¹ < ‖p‖
    · have hmem : ℓ • p ∈ {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖} := by
        show (d ^ 2)⁻¹ < ‖ℓ • p‖
        rw [norm_smul, Real.norm_of_nonneg hℓ.le, ← hkey]
        exact mul_lt_mul_of_pos_left hp hℓ
      rw [momProj, if_pos hp, Set.indicator_of_mem hmem, hBh, hH]
      ring
    · have hnot : ℓ • p ∉ {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖} := by
        show ¬ ((d ^ 2)⁻¹ < ‖ℓ • p‖)
        rw [norm_smul, Real.norm_of_nonneg hℓ.le, ← hkey]
        exact not_lt.mpr (mul_le_mul_of_nonneg_left (le_of_not_gt hp) hℓ.le)
      rw [momProj, if_neg hp, Set.indicator_of_notMem hnot]
      simp
  calc ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p * (Bh ℓ q p) ^ 2
      = ∫ p : EuclideanSpace ℝ (Fin 3), ℓ ^ 6 * (Set.indicator {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖}
          (fun w => (cubFT (w - ℓ • q) - cubFT (ℓ • q) * cubFT w) ^ 2)) (ℓ • p) := by
          refine integral_congr_ae ?_
          filter_upwards with p
          exact hpt p
    _ = ℓ ^ 6 * ∫ p : EuclideanSpace ℝ (Fin 3), (Set.indicator {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖}
          (fun w => (cubFT (w - ℓ • q) - cubFT (ℓ • q) * cubFT w) ^ 2)) (ℓ • p) := by
          rw [integral_const_mul]
    _ = ℓ ^ 6 * ((ℓ ^ 3)⁻¹ * ∫ w : EuclideanSpace ℝ (Fin 3), (Set.indicator {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖}
          (fun w => (cubFT (w - ℓ • q) - cubFT (ℓ • q) * cubFT w) ^ 2)) w) := by
          rw [Measure.integral_comp_smul_of_nonneg volume _ ℓ (hR := hℓ.le),
              finrank_euclideanSpace_fin, smul_eq_mul]
    _ = ℓ ^ 3 * ∫ w : EuclideanSpace ℝ (Fin 3), (Set.indicator {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖}
          (fun w => (cubFT (w - ℓ • q) - cubFT (ℓ • q) * cubFT w) ^ 2)) w := by
          have h6 : ℓ ^ 6 * (ℓ ^ 3)⁻¹ = ℓ ^ 3 := by field_simp
          rw [← mul_assoc, h6]
    _ = ℓ ^ 3 * ∫ w in {q' : EuclideanSpace ℝ (Fin 3) | (d ^ 2)⁻¹ < ‖q'‖},
          (cubFT (w - ℓ • q) - cubFT (ℓ • q) * cubFT w) ^ 2 := by
          rw [MeasureTheory.integral_indicator
            (measurableSet_lt measurable_const continuous_norm.measurable)]

end Work.BoseKinLoc.Momentum
