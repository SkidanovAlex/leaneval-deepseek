/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the compactly supported weighted Agmon inequality

This module contains the shared definitions and elementary facts used by
`Work.FTS.EllipticEst.Blocks.DzAgmonCompact` (the weighted Agmon–Nirenberg inequality for
`D = z ∂_z` on the half-line, compactly supported case) and by the lemmas surrounding it.

The weight of the paper is `w(z) = (1+z)²/z²` (`Work.Spaces.w`); the Agmon inequality is
stated against the *squared* weight `ρ = w²`, which we package as `W2`.  In closed form
`W2 z = (1+z)⁴/z⁴`, so `ρ` is smooth on `(0,∞)` and positive there.

Contents:

* `W2` — the weight `ρ = w²`, with `W2_eq` (its closed form `(1+z)⁴/z⁴`), `W2_nonneg`,
  `W2_pos`, `W2_contDiffOn`;
* `deriv_W2_mul_sq`, `abs_deriv_W2_mul_sq_le` — the derivative of the auxiliary factor
  `z ↦ ρ(z)·z²` and the bound `|(ρz²)'| ≤ (2/z)·ρz²` valid for `z > 0` (this is the
  `(ρz²)'/(ρz²) = 2(z-1)/(z(1+z))` of the route, whose absolute value is `≤ 2/z`);
* `integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off` — the integrability criterion for
  functions that are continuous on a compact interval `[a,b]` and vanish outside it: they
  are `IntegrableOn (0,∞)`.  Every integrand appearing in the Agmon estimate has this
  shape, so this is the single integrability lemma the estimate needs.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## The squared radial weight `ρ = w²` -/

/-- The square of Elgindi's radial weight, `ρ(z) = w(z)²` with `w(z) = (1+z)²/z²`. -/
def W2 (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The closed form of the weight: `ρ(z) = (1+z)⁴/z⁴` (true for every `z`, both sides being
Lean's junk value `0` at `z = 0`). -/
theorem W2_eq (z : ℝ) : W2 z = (1 + z) ^ 4 / z ^ 4 := by
  simp only [W2, Work.Spaces.w, div_pow]
  ring

theorem W2_nonneg (z : ℝ) : 0 ≤ W2 z := by rw [W2_eq]; positivity

theorem W2_pos {z : ℝ} (hz : 0 < z) : 0 < W2 z := by
  rw [W2_eq]; exact div_pos (by positivity) (by positivity)

/-- The weight `ρ` is smooth on `(0,∞)` (indeed analytic there). -/
theorem W2_contDiffOn : ContDiffOn ℝ ⊤ W2 (Set.Ioi (0 : ℝ)) := by
  have h : W2 = fun z : ℝ => (1 + z) ^ 4 / z ^ 4 := funext W2_eq
  rw [h]
  exact ContDiffOn.div (by fun_prop) (by fun_prop)
    (fun z hz => pow_ne_zero 4 (ne_of_gt hz))

/-! ## The derivative of `ρ(z)·z²` -/

/-- The logarithmic derivative of `z ↦ ρ(z)z² = (1+z)⁴/z²` is `2(z-1)/(z(1+z))`. -/
theorem deriv_W2_mul_sq {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => W2 y * y ^ 2) z
      = (2 * (z - 1) / (z * (1 + z))) * (W2 z * z ^ 2) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hfun : (fun y : ℝ => W2 y * y ^ 2) = fun y : ℝ => (1 + y) ^ 4 / y ^ 2 := by
    funext y
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num [W2, Work.Spaces.w]
    · rw [W2_eq]
      field_simp
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 4) z := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) z := by fun_prop
  have hd3 : (fun y : ℝ => y ^ 2) z ≠ 0 := by simpa using pow_ne_zero 2 hz0
  rw [show (fun y : ℝ => (1 + y) ^ 4 / y ^ 2)
      = (fun y : ℝ => (1 + y) ^ 4) / (fun y : ℝ => y ^ 2) from rfl]
  rw [deriv_div hd1 hd2 hd3]
  have hv1 : deriv (fun y : ℝ => (1 + y) ^ 4) z = 4 * (1 + z) ^ 3 := by
    change deriv ((fun y : ℝ => 1 + y) ^ 4) z = 4 * (1 + z) ^ 3
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => 1 + y) z)]
    simp
  have hv2 : deriv (fun y : ℝ => y ^ 2) z = 2 * z := by
    change deriv ((fun y : ℝ => y) ^ 2) z = 2 * z
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y) z)]
    simp
  rw [hv1, hv2, W2_eq]
  field_simp
  ring

/-- The bound `|(ρz²)'| ≤ (2/z)·ρz²` for `z > 0`, i.e. `|2(z-1)/(z(1+z))| ≤ 2/z`. -/
theorem abs_deriv_W2_mul_sq_le {z : ℝ} (hz : 0 < z) :
    |deriv (fun y : ℝ => W2 y * y ^ 2) z| ≤ 2 / z * (W2 z * z ^ 2) := by
  rw [deriv_W2_mul_sq hz, abs_mul]
  have h2 : |2 * (z - 1) / (z * (1 + z))| ≤ 2 / z := by
    have hz1 : (0 : ℝ) < z * (1 + z) := by positivity
    rw [abs_div, abs_of_pos hz1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_div_iff₀ hz1 hz]
    have habs : |z - 1| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
    have key := mul_le_mul_of_nonneg_right
      (show 2 * |z - 1| ≤ 2 * (1 + z) by linarith) (le_of_lt hz)
    nlinarith [key]
  have h3 : 0 ≤ W2 z * z ^ 2 := mul_nonneg (W2_nonneg z) (sq_nonneg z)
  calc |2 * (z - 1) / (z * (1 + z))| * |W2 z * z ^ 2|
      ≤ (2 / z) * (W2 z * z ^ 2) := by
        rw [abs_of_nonneg h3]
        exact mul_le_mul_of_nonneg_right h2 h3
    _ = 2 / z * (W2 z * z ^ 2) := rfl

/-! ## An integrability criterion for functions supported in a compact interval -/

/-- A function which is continuous on `[a,b]` and vanishes outside `[a,b]` is integrable on
`(0,∞)`.  (`∫` over a compact set of a continuous function is finite, and the function
agrees with it off `[a,b]`.) -/
theorem integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) (h0 : ∀ z, z ∉ Set.Icc a b → g z = 0) :
    IntegrableOn g (Set.Ioi (0 : ℝ)) :=
  (hg.integrableOn_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi (fun z hz => h0 z hz.2)

end

end Work.FTS.EllipticEst.Blocks
