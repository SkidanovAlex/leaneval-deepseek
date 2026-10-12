import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6Est.RadialDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The radial `τ̃`-difference bound

`r² − τ̃(r) ≤ 2r(c₁ + ε_T c₂)` for `r ≥ 0`, `0 ≤ c₁ ≤ c₂`, `0 ≤ ε_T ≤ 1`, **with
no upper bound on `c₂`**: FS's second kinetic cutoff is
`c₂ = ½(K_ℓds)^{-1}(μ/ρ_z)^{1/2} = ½X^{-11/2}√(μ/ρ_z) → ∞` at FS's parameters
(`X = (μa³)^{1/323} → 0`), so a hypothesis `c₂ ≤ 1` would make the regime
uninhabitable there.  Three cases:

* `r < c₁`: both clamps are inactive, `τ̃ = 0`, and `r ≤ 2c₁` gives the bound;
* `c₁ ≤ r < c₂`: only the first clamp is active and
  `r² − τ̃ = 2c₁r − c₁² + ε_T(r−c₁)² ≤ 2c₁r + ε_T r² ≤ 2r(c₁+ε_Tc₂)` since `r ≤ 2c₂`;
* `c₂ ≤ r`: both clamps are active and the identity
  `2r(c₁+ε_Tc₂) − (r² − τ̃) = c₁² + ε_T(2rc₁ + (c₂−c₁)(c₂+c₁)) ≥ 0` holds exactly.
-/

namespace Work.BoseB6Est

/-- The radial estimate `r² − τ̃(r) ≤ 2r(c₁ + ε_T c₂)` for `r ≥ 0`, with no
hypothesis relating `c₂` to `1` or to `r`. -/
theorem radialTauDiffBound {εT c1 c2 r : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1)
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (hr0 : 0 ≤ r) :
    r ^ 2 - Work.BoseB6.fsTau εT c1 c2 r ≤ 2 * r * (c1 + εT * c2) := by
  have hc2 : 0 ≤ c2 := le_trans hc1 hc12
  rcases lt_or_ge r c1 with h1 | h1
  · -- r < c₁: both clamps inactive
    rw [Work.BoseB6.fsTau, abs_of_nonneg hr0,
      max_eq_right (by linarith : r - c1 ≤ 0), max_eq_right (by linarith : r - c2 ≤ 0)]
    have hzero : (1 - εT) * 0 ^ 2 + εT * 0 ^ 2 = (0 : ℝ) := by norm_num
    rw [hzero, sub_zero]
    have h2 : r ^ 2 ≤ 2 * r * c1 := by nlinarith [hc1, hr0, h1]
    have h3 : 0 ≤ 2 * r * (εT * c2) := by positivity
    nlinarith
  · rcases lt_or_ge r c2 with h2 | h2
    · -- c₁ ≤ r < c₂: only the first clamp is active
      rw [Work.BoseB6.fsTau, abs_of_nonneg hr0, max_eq_left (by linarith : 0 ≤ r - c1),
        max_eq_right (by linarith : r - c2 ≤ 0)]
      have hzero : εT * 0 ^ 2 = (0 : ℝ) := by norm_num
      rw [hzero, add_zero]
      have key : 2 * r * (c1 + εT * c2) - (r ^ 2 - (1 - εT) * (r - c1) ^ 2)
          = εT * (2 * r * (c1 + c2) - r ^ 2 - c1 ^ 2) + c1 ^ 2 := by ring
      have hA : 0 ≤ εT * (2 * r * (c1 + c2) - r ^ 2 - c1 ^ 2) := by
        have hh : 0 ≤ 2 * r * (c1 + c2) - r ^ 2 - c1 ^ 2 := by nlinarith [h1, h2]
        exact mul_nonneg hε0 hh
      have hB : 0 ≤ c1 ^ 2 := sq_nonneg c1
      linarith [key, hA, hB]
    · -- c₂ ≤ r: both clamps active
      rw [Work.BoseB6.fsTau, abs_of_nonneg hr0, max_eq_left (by linarith : 0 ≤ r - c1),
        max_eq_left (by linarith : 0 ≤ r - c2)]
      have key : 2 * r * (c1 + εT * c2)
          - (r ^ 2 - ((1 - εT) * (r - c1) ^ 2 + εT * (r - c2) ^ 2))
          = c1 ^ 2 + εT * (2 * r * c1 + (c2 - c1) * (c2 + c1)) := by ring
      have hc : 0 ≤ 2 * r * c1 + (c2 - c1) * (c2 + c1) := by
        have hh : 0 ≤ (c2 - c1) * (c2 + c1) := mul_nonneg (by linarith) (by linarith)
        nlinarith [mul_nonneg hr0 hc1]
      nlinarith [key, hc, hε0, sq_nonneg c1, mul_nonneg hε0 hc]

end Work.BoseB6Est
