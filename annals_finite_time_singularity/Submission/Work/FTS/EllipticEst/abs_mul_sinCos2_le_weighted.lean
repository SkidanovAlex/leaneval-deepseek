/-
Work module for the Elgindi finite-time singularity project.

# Pointwise absorption of the angular weight `sin θ cos²θ` by the radial weight

On the angular domain `θ ∈ [0,π/2]` one has `sin θ cos²θ ≤ 1`, while the radial weight
`w(z) = (1+z)²/z²` satisfies `w(z) ≥ 1` for `z > 0` and the angular factor
`sin(2θ)^{η/2}` is at most `1`.  Hence, whenever `sin(2θ) ≠ 0`, the coefficient
`w(z)/sin(2θ)^{η/2}` is at least `1`, and the elementary inequality
`|a| ≤ a² + 1` (AM–GM for `|a|` and `1`) absorbs `|a · sinθcos²θ|` into
`(a · w(z)/sin(2θ)^{η/2})² + 1`.  The degenerate angles `sin(2θ) = 0` (i.e. `θ = 0`
and `θ = π/2`) are trivial because there `sin θ cos²θ = 0` and Lean's totalised
division gives `w(z)/0 = 0`, so the right hand side is `1`.

This is the pointwise estimate that controls the `i = 0`, `j = 0` term of the weighted
`H^k` integrand against the `L²((z,θ))` norms; see `Work.Spaces.HkIntegrand`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real

/-- On `[0,π/2]` the angular profile `sin θ cos²θ` lies in `[0,1]`. -/
lemma abs_sinCos2_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := hθ.2
  have hpi := Real.pi_pos
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hθ1
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by nlinarith
  have hc1 : Work.Elliptic.sinCos2 θ ≤ 1 := by
    rw [Work.Elliptic.sinCos2]
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul hsin1 hcos2 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hc0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.sinCos2]; positivity
  rw [abs_of_nonneg hc0]; exact hc1

/-- The radial weight `w(z) = (1+z)²/z²` is at least `1` for `z > 0`. -/
lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (by positivity)]
  nlinarith

/-- The requested estimate: on the angular domain, `|f θ · sinθcos²θ|` is absorbed by the
square of `f θ` times the weight `w(z)/sin(2θ)^{η/2}`, plus the constant `1`. -/
theorem abs_mul_sinCos2_le_weighted {f : ℝ → ℝ} {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |f θ * Work.Elliptic.sinCos2 θ|
      ≤ (f θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := hθ.2
  have hcabs : |Work.Elliptic.sinCos2 θ| ≤ 1 := abs_sinCos2_le_one hθ
  have hsin2_nonneg : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have hw : 1 ≤ Work.Spaces.w z := one_le_w hz
  have heta2 : 0 ≤ Work.Spaces.eta / 2 := by norm_num [Work.Spaces.eta]
  have heta2' : Work.Spaces.eta / 2 ≠ 0 := by norm_num [Work.Spaces.eta]
  by_cases h0 : Real.sin (2 * θ) = 0
  · -- degenerate angles: `sin(2θ) = 0` forces `sinθcos²θ = 0`, and the weight is `0`
    have hs0 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [h0]; exact Real.zero_rpow heta2'
    have hcz : Work.Elliptic.sinCos2 θ = 0 := by
      have h1 : Real.sin θ * Real.cos θ = 0 := by
        have h2 := Real.sin_two_mul θ
        rw [h0] at h2
        linarith
      rw [Work.Elliptic.sinCos2]
      calc Real.sin θ * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) * Real.cos θ := by ring
        _ = 0 := by rw [h1, zero_mul]
    rw [hcz, mul_zero, abs_zero, hs0, div_zero, mul_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num
  · -- non-degenerate angles: the weight is at least `1`
    have hs_pos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne hsin2_nonneg (Ne.symm h0)) _
    have hs_le : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hsin2_nonneg (Real.sin_le_one _) heta2
    have hW : 1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
      rw [one_le_div hs_pos]
      exact le_trans hs_le hw
    have hW2 : 1 ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
      one_le_pow₀ hW
    -- `|f θ · sinθcos²θ| ≤ |f θ|`
    have hLHS : |f θ * Work.Elliptic.sinCos2 θ| ≤ |f θ| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hcabs
    -- `|f θ| ≤ (f θ · W)² + 1`
    have hstep : |f θ|
        ≤ (f θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
      have h1 : (f θ) ^ 2
          ≤ (f θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow]
        nlinarith [sq_nonneg (f θ), hW2]
      nlinarith [sq_abs (f θ), sq_nonneg (|f θ| - 1 / 2), h1]
    linarith

end Work.FTS.EllipticEst
