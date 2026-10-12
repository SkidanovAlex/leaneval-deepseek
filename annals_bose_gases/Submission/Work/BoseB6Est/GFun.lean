import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6Est.RadialDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — FS's Bogoliubov bracket as a function of `(τ, b)`

FS's `lem:BogIntegral` compares the radial integrand

  `gFun τ b r = (τ+b) − √((τ+b)²−b²) − b²/(2r²)`

at `(τ, b) = (τ̃(r), β(r))` (the physical kernel) with its value at the model
point `(τ, b) = (r², 8π)`.  This module only introduces that function and the
elementary algebraic identities that make the comparison a two-variable
*increment* estimate:

* `fsGR_eq_gFun`, `fsG0R_eq_gFun` — the physical integrand and the model
  integrand are `gFun` at the two parameter pairs;
* `gFun_eq_phi` — `gFun τ b r = b²(1/D − 1/(2r²))`, `D = (τ+b) + √(τ²+2τb)`
  (`0 ≤ τ`, `0 ≤ b`), which is what makes the `1/r²` singularities of the two
  pieces cancel;
* `gFun_zero` — at `τ = 0` the bracket is `b − b²/(2r²)`;
* `gFun_zero_diff` — the exact `τ = 0` increment.

The *increment estimates* (`gFun_tau_diff`, `gFun_beta_diff_lin`,
`gFun_beta_diff_sq`) are the subject of the sibling modules `GTau`, `GBeta`;
the kernel facts are in `BetaClose`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB6Est

/-- FS's Bogoliubov bracket `(τ+b) − √((τ+b)²−b²) − b²/(2r²)` as a function of
the pair `(τ, b)` at radius `r`. -/
def gFun (τ b r : ℝ) : ℝ :=
  τ + b - Real.sqrt ((τ + b) ^ 2 - b ^ 2) - b ^ 2 / (2 * r ^ 2)

/-- The physical radial integrand is `gFun` at `(τ̃(r), β(r))`. -/
theorem fsGR_eq_gFun (K : FsKernel) (εT c1 c2 r : ℝ) :
    fsGR K εT c1 c2 r = gFun (Work.BoseB6.fsTau εT c1 c2 r) (K.β r) r := rfl

/-- The model radial integrand is `gFun` at `(r², 8π)`. -/
theorem fsG0R_eq_gFun (r : ℝ) : fsG0R r = gFun (r ^ 2) (8 * Real.pi) r := rfl

/-- `α − √(α²−b²) = b²/(α + √(α²−b²))` for `0 ≤ b ≤ α`. -/
lemma sq_sub_sqrt_eq_div {α b : ℝ} (hb : 0 ≤ b) (hbα : b ≤ α) :
    α - Real.sqrt (α ^ 2 - b ^ 2) = b ^ 2 / (α + Real.sqrt (α ^ 2 - b ^ 2)) := by
  have hα0 : 0 ≤ α := le_trans hb hbα
  have hs2 : Real.sqrt (α ^ 2 - b ^ 2) ^ 2 = α ^ 2 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ Real.sqrt (α ^ 2 - b ^ 2) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le (add_nonneg hα0 hs0) with h | h
  · have hα : α = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [hα, hb0]
  · rw [eq_div_iff (ne_of_gt h)]
    nlinarith [hs2]

/-- **The `D`-form of the bracket**: `gFun τ b r = b²(1/D − 1/(2r²))` with
`D = (τ+b) + √(τ²+2τb)`, for `τ, b ≥ 0`. -/
theorem gFun_eq_phi {τ b r : ℝ} (hτ : 0 ≤ τ) (hb : 0 ≤ b) :
    gFun τ b r
      = b ^ 2 * (1 / ((τ + b) + Real.sqrt (τ ^ 2 + 2 * τ * b)) - 1 / (2 * r ^ 2)) := by
  have hkey : (τ + b) - Real.sqrt ((τ + b) ^ 2 - b ^ 2)
      = b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) :=
    sq_sub_sqrt_eq_div hb (by linarith)
  have hrad : (τ + b) ^ 2 - b ^ 2 = τ ^ 2 + 2 * τ * b := by ring
  rw [gFun, hkey, hrad]
  ring

/-- At `τ = 0` the bracket is `b − b²/(2r²)`. -/
theorem gFun_zero (b r : ℝ) : gFun 0 b r = b - b ^ 2 / (2 * r ^ 2) := by
  rw [gFun]
  simp only [zero_add, sub_self, Real.sqrt_zero, sub_zero]

/-- The exact `τ = 0` increment: `gFun 0 b r − gFun 0 b' r = (b−b')(1 − (b+b')/(2r²))`. -/
theorem gFun_zero_diff (b b' r : ℝ) :
    gFun 0 b r - gFun 0 b' r = (b - b') * (1 - (b + b') / (2 * r ^ 2)) := by
  rw [gFun_zero, gFun_zero]
  ring

/-- The size of the `τ = 0` increment. -/
theorem gFun_zero_diff_abs_le {b b' r : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') (hr : 0 < r) :
    |gFun 0 b r - gFun 0 b' r| ≤ |b - b'| * (1 + (b + b') / (2 * r ^ 2)) := by
  rw [gFun_zero_diff, abs_mul]
  have h2 : 0 ≤ (b + b') / (2 * r ^ 2) := by positivity
  have h3 : |1 - (b + b') / (2 * r ^ 2)| ≤ 1 + (b + b') / (2 * r ^ 2) := by
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)

end Work.BoseB6Est
