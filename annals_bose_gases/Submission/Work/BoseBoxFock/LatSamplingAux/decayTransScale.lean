import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSamplingAux

/-- **Weighted decay is preserved by an affine rescaling of the argument.**
If `F` decays faster than every polynomial (‖F y‖ ≤ C_n (1+‖y‖)^{-n} for all `n`),
then for every `z` and every `ℓ > 0` the function `x ↦ ‖F (z + ℓ • x)‖` decays at
least like `(1 + ‖x‖)^{-4}` uniformly.  The point of the lemma is the uniformity in
`ℓ > 0` (which may be arbitrarily small) and in the shift `z`: the weight `(1+‖x‖)^4`
is absorbed by the `n = 4` decay estimate at `z + ℓ • x`, using that
`1 + ‖x‖ ≤ (1 + ℓ⁻¹ (1 + ‖z‖)) (1 + ‖z + ℓ • x‖)`. -/
theorem decayTransScale {ℓ : ℝ} (hℓ : 0 < ℓ) {F : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hFdec : ∀ n : ℕ, ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin 3), ‖F y‖ ≤ C * (1 + ‖y‖) ^ (-(n : ℤ)))
    (z : EuclideanSpace ℝ (Fin 3)) :
    ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), (1 + ‖x‖) ^ 4 * ‖F (z + ℓ • x)‖ ≤ C := by
  -- the `n = 4` decay estimate, written with an inverse instead of a negative integer power
  obtain ⟨C4, hC4⟩ := hFdec 4
  have hC4' : ∀ y : EuclideanSpace ℝ (Fin 3), ‖F y‖ ≤ C4 * ((1 + ‖y‖) ^ 4)⁻¹ := by
    intro y
    have h := hC4 y
    simp only [zpow_neg] at h
    exact h
  -- `C4` is nonnegative (evaluate at the origin)
  have hC4nn : 0 ≤ C4 := by
    have h := hC4 0
    simp only [zpow_neg, norm_zero] at h
    linarith [norm_nonneg (F 0)]
  have ha : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  -- the linear growth comparison: `1 + ‖x‖ ≤ M * (1 + ‖z + ℓ • x‖)`
  have hmain : ∀ x : EuclideanSpace ℝ (Fin 3),
      1 + ‖x‖ ≤ (1 + ℓ⁻¹ * (1 + ‖z‖)) * (1 + ‖z + ℓ • x‖) := by
    intro x
    have hx : ℓ⁻¹ • ((z + ℓ • x) - z) = x := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hℓ.ne', one_smul]
    have hxnorm : ‖x‖ ≤ ℓ⁻¹ * (‖z + ℓ • x‖ + ‖z‖) := by
      calc ‖x‖ = ‖ℓ⁻¹ • ((z + ℓ • x) - z)‖ := by rw [hx]
        _ = ‖ℓ⁻¹‖ * ‖(z + ℓ • x) - z‖ := norm_smul _ _
        _ = ℓ⁻¹ * ‖(z + ℓ • x) - z‖ := by rw [Real.norm_of_nonneg ha]
        _ ≤ ℓ⁻¹ * (‖z + ℓ • x‖ + ‖z‖) :=
              mul_le_mul_of_nonneg_left (norm_sub_le _ _) ha
    have ht : 0 ≤ ‖z + ℓ • x‖ := norm_nonneg _
    have hz : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [hxnorm, ha, ht, hz, mul_nonneg ha hz, mul_nonneg (mul_nonneg ha hz) ht,
      mul_nonneg ha ht]
  refine ⟨C4 * (1 + ℓ⁻¹ * (1 + ‖z‖)) ^ 4, ?_⟩
  intro x
  have hstep := hmain x
  have hs : 0 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  set M := 1 + ℓ⁻¹ * (1 + ‖z‖) with hM
  set t := 1 + ‖z + ℓ • x‖ with ht
  have htpos : 0 < t := by rw [ht]; linarith [norm_nonneg (z + ℓ • x)]
  -- the weight is dominated by `M ^ 4 * t ^ 4`
  have hs4 : (1 + ‖x‖) ^ 4 ≤ M ^ 4 * t ^ 4 := by
    have h1 : (1 + ‖x‖) ^ 4 ≤ (M * t) ^ 4 := by
      apply pow_le_pow_left₀ hs
      rw [hM, ht]; exact hstep
    rwa [mul_pow] at h1
  have hfin : (1 + ‖x‖) ^ 4 * (t ^ 4)⁻¹ ≤ M ^ 4 := by
    have h2 := mul_le_mul_of_nonneg_right hs4 (inv_nonneg.mpr (pow_nonneg htpos.le 4))
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos htpos 4)), mul_one] at h2
  have h4 := hC4' (z + ℓ • x)
  rw [← ht] at h4
  calc (1 + ‖x‖) ^ 4 * ‖F (z + ℓ • x)‖
      ≤ (1 + ‖x‖) ^ 4 * (C4 * (t ^ 4)⁻¹) := mul_le_mul_of_nonneg_left h4 (pow_nonneg hs 4)
    _ = C4 * ((1 + ‖x‖) ^ 4 * (t ^ 4)⁻¹) := by ring
    _ ≤ C4 * M ^ 4 := mul_le_mul_of_nonneg_left hfin hC4nn

end Work.BoseBoxFock.LatSamplingAux
