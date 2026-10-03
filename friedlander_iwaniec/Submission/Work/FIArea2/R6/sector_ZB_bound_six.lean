import Mathlib
import Submission.Work.FIArea2.Count.ZAc_bound_eight
import Submission.Work.FIArea2.Count.ZBc_bound_eight
import Submission.Work.FIArea2.Count.sec9_Z_defs

set_option autoImplicit false

namespace Work.FIArea2.R6

open Work.FIArea2.Count

/-- **The sector bound for `ZB` at threshold `thr = ϑ √N`.**

The two halves of `ZB` (`= ZAc + ZBc`, split according to `Re Λ ≠ 0` vs `Re Λ = 0`) are each
bounded by `Work.FIArea2.Count.ZAc_bound_eight` / `Work.FIArea2.Count.ZBc_bound_eight` with the
parameter `ϑ` replaced by `ϑ²`, because `√(ϑ² · Nr) = ϑ √Nr`.  Since `(ϑ²)^{-1/2} = ϑ^{-1}`, this
gives exactly the stated factor `ϑ⁻¹`. -/
theorem sector_ZB_bound_six :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (h1 h2 : ℤ) (thr Nr ϑ : ℝ) (Dm : ℕ),
      0 < ϑ → ϑ ≤ 1 → 1 ≤ Nr → 0 ≤ R → thr = ϑ * Real.sqrt Nr →
      (2 * (R : ℝ) + 1) ≤ 8 * Real.sqrt Nr → 1 ≤ Dm →
      (h1 ≠ 0 ∨ h2 ≠ 0) →
      (∀ r1 ∈ Finset.Icc (-R) R, ∀ s1 ∈ Finset.Icc (-R) R, ∀ r2 ∈ Finset.Icc (-R) R,
        ∀ s2 ∈ Finset.Icc (-R) R, Work.FIArea2.Count.cdg h1 h2 r1 s1 r2 s2 ≤ Dm) →
      Work.FIArea2.Count.ZB R h1 h2 thr
        ≤ C * ϑ⁻¹ * (Real.log (Nr + 2)) ^ (8 : ℕ) * Work.FIArea2.Count.UB R h1 h2 := by
  obtain ⟨CA, hCApos, hCA⟩ := ZAc_bound_eight
  obtain ⟨CB, hCBpos, hCB⟩ := ZBc_bound_eight
  refine ⟨CA + CB, by positivity, ?_⟩
  intro R h1 h2 thr Nr ϑ Dm hϑpos hϑle hNr hR0 hthr h2R hDm1 hne hcdg
  -- Rescale the parameter `ϑ` to `ϑ²`, so that `√(ϑ² Nr) = ϑ √Nr = thr`.
  have hϑ2pos : (0 : ℝ) < ϑ ^ 2 := pow_pos hϑpos 2
  have hϑ2nn : (0 : ℝ) ≤ ϑ ^ 2 := hϑ2pos.le
  have hϑ2le : ϑ ^ 2 ≤ 1 := pow_le_one₀ hϑpos.le hϑle
  have hsq : (ϑ ^ 2) ^ (-(1 : ℝ) / 2) = ϑ⁻¹ := by
    rw [← Real.rpow_natCast_mul hϑpos.le 2 (-(1 : ℝ) / 2)]
    rw [show ((2 : ℕ) : ℝ) * (-(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  have hthr2 : thr = Real.sqrt (ϑ ^ 2 * Nr) := by
    rw [hthr, Real.sqrt_mul hϑ2nn Nr, Real.sqrt_sq hϑpos.le]
  have hA := hCA R h1 h2 thr Nr (ϑ ^ 2) Dm hϑ2pos hϑ2le hNr hR0 hthr2 h2R hDm1 hcdg
  have hB := hCB R h1 h2 thr Nr (ϑ ^ 2) Dm hϑ2pos hϑ2le hNr hR0 hthr2 h2R hDm1 hne hcdg
  rw [hsq] at hA hB
  rw [ZB_eq_ZAc_add_ZBc]
  calc ZAc R h1 h2 thr + ZBc R h1 h2 thr
      ≤ CA * ϑ⁻¹ * (Real.log (Nr + 2)) ^ (8 : ℕ) * UB R h1 h2
        + CB * ϑ⁻¹ * (Real.log (Nr + 2)) ^ (8 : ℕ) * UB R h1 h2 := add_le_add hA hB
    _ = (CA + CB) * ϑ⁻¹ * (Real.log (Nr + 2)) ^ (8 : ℕ) * UB R h1 h2 := by ring

end Work.FIArea2.R6
