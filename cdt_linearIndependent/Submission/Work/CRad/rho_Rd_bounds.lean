import Mathlib
import Submission.Work.CRad.deps

namespace Work.CRad

/-- The quantity `ρ_a = a - √(a²-1)` (`beukersRho`) satisfies the two estimates
needed for the radius bookkeeping in the `CRad` area:

* the product `ρ_a·(2√(a²-1) - 1 - ρ_a)` is bounded below by the numerical
  constant `26√2 - 36` (attained at `a = 3`), and
* `2√(a²-1) - 1 - ρ_a > 1`.

Both are for `a ≥ 3`.  The key point is the hyperbolic identity
`ρ_a·(2√(a²-1) - 1 - ρ_a) = 1 - ρ_a - 2ρ_a²`, together with the range bound
`0 < ρ_a ≤ 3 - 2√2`. -/
theorem rho_Rd_bounds (a : ℝ) (ha : 3 ≤ a) :
    26 * Real.sqrt 2 - 36 ≤ Submission.CDT.beukersRho a *
        (2 * Real.sqrt (a ^ 2 - 1) - 1 - Submission.CDT.beukersRho a) ∧
      (1 : ℝ) < 2 * Real.sqrt (a ^ 2 - 1) - 1 - Submission.CDT.beukersRho a := by
  set ρ := Submission.CDT.beukersRho a with hρdef
  have hpos : 0 < ρ := by rw [hρdef]; exact Submission.CDT.beukers_rho_pos a ha
  have hs : a - ρ = Real.sqrt (a ^ 2 - 1) := by
    rw [hρdef]; unfold Submission.CDT.beukersRho; ring
  have hinv : 2 * a - ρ = ρ⁻¹ := by
    rw [hρdef]; exact Submission.CDT.beukers_two_mul_sub_eq_inv a ha
  have hadd : ρ + 2 < 2 * Real.sqrt (a ^ 2 - 1) := by
    rw [hρdef]; exact Submission.CDT.beukers_rho_add_two_lt_two_sqrt a ha
  have hρne : ρ ≠ 0 := ne_of_gt hpos
  -- The hyperbolic identity behind the product term.
  have hident : ρ * (2 * Real.sqrt (a ^ 2 - 1) - 1 - ρ) = 1 - 2 * ρ ^ 2 - ρ := by
    have h1 : 2 * Real.sqrt (a ^ 2 - 1) - 1 - ρ = ρ⁻¹ - 2 * ρ - 1 := by
      have h2 : 2 * Real.sqrt (a ^ 2 - 1) = 2 * (a - ρ) := by rw [hs]
      rw [h2, ← hinv]; ring
    rw [h1, mul_sub, mul_sub, mul_one, mul_inv_cancel₀ hρne]; ring
  -- `√(a²-1) ≥ 2√2` for `a ≥ 3`.
  have h2sqrt2_le : 2 * Real.sqrt 2 ≤ Real.sqrt (a ^ 2 - 1) := by
    rw [Real.le_sqrt (by positivity) (by nlinarith [sq_nonneg a])]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsum_ge : 3 + 2 * Real.sqrt 2 ≤ a + Real.sqrt (a ^ 2 - 1) := by
    linarith [ha, h2sqrt2_le]
  have h3 : (3 + 2 * Real.sqrt 2)⁻¹ = 3 - 2 * Real.sqrt 2 := by
    have hh : (3 + 2 * Real.sqrt 2) * (3 - 2 * Real.sqrt 2) = 1 := by
      have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [h2]
    exact inv_eq_of_mul_eq_one_right hh
  -- Range bound on `ρ_a`.
  have hρle : ρ ≤ 3 - 2 * Real.sqrt 2 := by
    have hρinv : ρ = (a + Real.sqrt (a ^ 2 - 1))⁻¹ := by
      have hh : ρ⁻¹ = a + Real.sqrt (a ^ 2 - 1) := by rw [← hinv, ← hs]; ring
      rw [← hh, inv_inv]
    have hAs : 0 < a + Real.sqrt (a ^ 2 - 1) := by
      have := Real.sqrt_nonneg (a ^ 2 - 1); linarith
    have hB : 0 < 3 + 2 * Real.sqrt 2 := by positivity
    rw [hρinv, ← h3]
    exact (inv_le_inv₀ hAs hB).2 hsum_ge
  -- The numerical constant is exactly the bound at `a = 3`.
  have hnum : 1 - 2 * (3 - 2 * Real.sqrt 2) ^ 2 - (3 - 2 * Real.sqrt 2)
      = 26 * Real.sqrt 2 - 36 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hfinal : 1 - 2 * (3 - 2 * Real.sqrt 2) ^ 2 - (3 - 2 * Real.sqrt 2)
      ≤ 1 - 2 * ρ ^ 2 - ρ := by
    have hρsq : ρ ^ 2 ≤ (3 - 2 * Real.sqrt 2) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hpos) hρle 2
    nlinarith [hρle, hρsq]
  constructor
  · calc 26 * Real.sqrt 2 - 36
        = 1 - 2 * (3 - 2 * Real.sqrt 2) ^ 2 - (3 - 2 * Real.sqrt 2) := hnum.symm
      _ ≤ 1 - 2 * ρ ^ 2 - ρ := hfinal
      _ = ρ * (2 * Real.sqrt (a ^ 2 - 1) - 1 - ρ) := hident.symm
  · linarith [hadd]

end Work.CRad
