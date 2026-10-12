import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Task: prove a one-dimensional elementary integral

GOAL (`shell_integral_sqrt_one`): for real `r > 0`, `s > 0`,

    (∫ t in Set.Icc (-1 : ℝ) 1, (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * t))⁻¹)
        = 2 / max r s

This is the classical identity
`∫_{-1}^{1} dt / √(r² + s² − 2rs·t) = 2 / max(r,s)` (the potential of a
uniform spherical shell).  Note the integrand is the pointwise inverse of
`Real.sqrt`: at a point where the argument vanishes (`r = s` and `t = 1`) the
value is `0⁻¹ = 0` by `inv_zero`, which matches the improper-integral value.

HOW TO PROVE (any route that works; suggestions):
1. Reduce the set integral over `Set.Icc (-1) 1` to the interval integral
   `∫ t in (-1 : ℝ)..1, ...` via
   `intervalIntegral.integral_of_le` (for `a ≤ b` the interval integral equals
   the Lebesgue integral over `Set.Icc a b`).
2. Substitution `u = r²+s²−2rs t`: use
   `intervalIntegral.integral_comp_mul_add` /
   `smul_integral_comp_mul_add` (substitution `f (c*x + d)` with
   `c = -2*r*s`, `d = r^2+s^2`), to rewrite the integral as an integral of
   `u ↦ u ^ (-(1/2))` (i.e. `1/√u`) between `(r-s)^2` and `(r+s)^2`.
   Equivalently keep `Real.sqrt` and use the derivative/FTC route.
3. Evaluate `∫ u in a..b, u ^ r` with `r = -1/2` via
   `intervalIntegral.integral_rpow`:
   `∫ x in a..b, x ^ r = (b ^ (r+1) - a ^ (r+1)) / (r + 1)` (valid for
   `-1 < r`, here `r+1 = 1/2`; note `a = (r-s)^2 ≥ 0`, so the endpoint
   `a = 0` is allowed).
4. Simplify `(r+s)^2 ^ (1/2) = r + s` and `(r-s)^2 ^ (1/2) = |r - s|`
   (`Real.sqrt_sq_eq_abs` / `Real.sq_sqrt`; or `Real.rpow` lemmas) and finish
   with the identity
   `((r+s) - |r-s|) / (r*s) = 2 / max r s` (case split on `r ≤ s` vs
   `s ≤ r`; use `abs_of_nonneg` / `abs_of_nonpos` and `max_eq_left` /
   `max_eq_right`; `nlinarith` will close the algebra).

If the FTC/derivative route is easier for you (`Real.hasDerivAt_sqrt`,
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`), use that.

The exact statement to prove:
```
lemma shell_integral_sqrt_one {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ t in Set.Icc (-1 : ℝ) 1, (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * t))⁻¹) =
      2 / max r s
```

You may add helper lemmas in this file.  Do not change the statement.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real Interval

/-- For `x ≥ 0`, `(√x)⁻¹ = x ^ (-1/2)` (real power). -/
lemma shell_one_dim_sqrt_inv_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_neg hx (1 / 2 : ℝ)).symm

/-- The (improper, for `a = 0`) integral `∫ u in a..b, (√u)⁻¹ = 2(√b - √a)`
for `0 ≤ a ≤ b`.  This is valid even for `a = 0` by the convention
`0⁻¹ = 0`, and is proved via `intervalIntegral.integral_rpow` with
exponent `-1/2`. -/
lemma shell_one_dim_integral_inv_sqrt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, (Real.sqrt u)⁻¹ = 2 * (Real.sqrt b - Real.sqrt a) := by
  have hcongr : ∫ u in a..b, (Real.sqrt u)⁻¹ = ∫ u in a..b, u ^ (-(1 / 2 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply shell_one_dim_sqrt_inv_eq_rpow_neg_half
    rw [Set.uIcc_of_le hab] at hx
    exact le_trans ha hx.1
  rw [hcongr]
  rw [integral_rpow (a := a) (b := b) (r := -(1 / 2 : ℝ)) (Or.inl (by norm_num : -1 < -(1/2:ℝ)))]
  norm_num
  conv_rhs => simp only [Real.sqrt_eq_rpow]
  ring

/-- `∫_{-1}^{1} dt / √(r²+s²−2rs t) = 2/max r s` for `r,s > 0`. -/
lemma shell_integral_sqrt_one {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ t in Set.Icc (-1 : ℝ) 1, (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * t))⁻¹) =
      2 / max r s := by
  -- Reduce the set integral over `Icc (-1) 1` to the interval integral `-1..1`.
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  let F : ℝ → ℝ := fun t => (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * t))⁻¹
  let G : ℝ → ℝ := fun u => (Real.sqrt u)⁻¹
  let c : ℝ := -2 * r * s
  let d : ℝ := r ^ 2 + s ^ 2
  change (∫ t in (-1 : ℝ)..1, F t) = 2 / max r s
  have harg : ∀ t : ℝ, c * t + d = r ^ 2 + s ^ 2 - 2 * r * s * t := by
    intro t
    simp [c, d]
    ring
  have hF : F = fun t => G (c * t + d) := by
    funext t
    dsimp [F, G]
    rw [← harg t]
  have hc : c ≠ 0 := by
    dsimp [c]
    nlinarith
  have hb1 : c * (-1) + d = (r + s) ^ 2 := by
    simp [c, d]
    ring
  have hb2 : c * 1 + d = (r - s) ^ 2 := by
    simp [c, d]
    ring
  have hc₁ : c⁻¹ = -(2 * r * s)⁻¹ := by
    dsimp [c]
    rw [← inv_neg]
    congr 1
    ring
  have hnonneg : 0 ≤ (r - s) ^ 2 := sq_nonneg (r - s)
  have hmono : (r - s) ^ 2 ≤ (r + s) ^ 2 := by
    nlinarith [mul_pos hr hs]
  calc
    (∫ t in (-1 : ℝ)..1, F t)
        = ∫ t in (-1 : ℝ)..1, G (c * t + d) := by rw [hF]
    _ = c⁻¹ * (∫ x in c * (-1) + d..c * 1 + d, G x) := by
          rw [intervalIntegral.integral_comp_mul_add G hc d]
          simp only [smul_eq_mul]
    _ = c⁻¹ * (∫ x in (r + s) ^ 2..(r - s) ^ 2, G x) := by rw [hb1, hb2]
    _ = c⁻¹ * (-(∫ x in (r - s) ^ 2..(r + s) ^ 2, G x)) := by
          rw [intervalIntegral.integral_symm ((r - s) ^ 2) ((r + s) ^ 2)]
    _ = (2 * r * s)⁻¹ * (∫ x in (r - s) ^ 2..(r + s) ^ 2, G x) := by
          rw [hc₁]
          ring
    _ = (2 * r * s)⁻¹ * (2 * (Real.sqrt ((r + s) ^ 2) - Real.sqrt ((r - s) ^ 2))) := by
          rw [shell_one_dim_integral_inv_sqrt hnonneg hmono]
    _ = (2 * r * s)⁻¹ * (2 * ((r + s) - |r - s|)) := by
          rw [Real.sqrt_sq_eq_abs (x := r + s)]
          rw [Real.sqrt_sq_eq_abs (x := r - s)]
          rw [abs_of_pos (by positivity : 0 < r + s)]
    _ = 2 / max r s := by
          rcases le_total r s with hle | hle
          · rw [max_eq_right hle]
            rw [abs_of_nonpos (sub_nonpos.mpr hle)]
            field_simp [hr.ne', hs.ne']
            ring
          · rw [max_eq_left hle]
            rw [abs_of_nonneg (sub_nonneg.mpr hle)]
            field_simp [hr.ne', hs.ne']
            ring

end Submission.BoseGases
