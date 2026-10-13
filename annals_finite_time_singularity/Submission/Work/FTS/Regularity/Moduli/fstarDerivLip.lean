/-
# Lipschitz regularity of the derivative of the profile `F_*(z) = 2z/(1+z)²`

The profile of the fundamental model has `deriv F_*(z) = 2(1-z)/(1+z)³`
(`Work.FM.deriv_Fstar`).  Its derivative (i.e. the second derivative of `F_*`) is
`4(z-2)/(1+z)⁴`, whose absolute value is bounded by `8` on `[0,∞)` — the bound is
attained at `z = 0` and nowhere else, so the Lipschitz constant `8` of
`deriv F_*` on `[0,∞)` is optimal.

The proof is the mean value theorem on the convex set `[0,∞)`
(`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`), applied to the explicit
function `z ↦ 2(1-z)/(1+z)³`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity.Moduli

open Set

/-- The second derivative of the profile `F_*`: the function `2(1-z)/(1+z)³` is
differentiable on `[0,∞)` with derivative `4(z-2)/(1+z)⁴`. -/
private lemma hasDerivAt_derivFstar (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => 2 * (1 - y) / (1 + y) ^ 3) (4 * (x - 2) / (1 + x) ^ 4) x := by
  have hnum : HasDerivAt (fun y : ℝ => 2 * (1 - y)) (-2) x := by
    have h : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) x).const_sub 1
    convert h.const_mul 2 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 3) (3 * (1 + x) ^ 2) x := by
    have h := (Work.FM.hasDerivAt_add_const 1 x).pow 3
    convert h using 1
    ring
  have hne : (1 + x) ^ 3 ≠ 0 := by
    have h1 : (0 : ℝ) < 1 + x := by linarith
    positivity
  have hdiv := hnum.div hden hne
  convert hdiv using 1
  have h1 : (1 + x) ≠ 0 := by linarith
  field_simp
  ring

/-- The bound `|4(z-2)/(1+z)⁴| ≤ 8` for `z ≥ 0`, i.e. `|z-2| ≤ 2(1+z)⁴`. -/
private lemma norm_secondDerivFstar_le (x : ℝ) (hx : 0 ≤ x) :
    ‖4 * (x - 2) / (1 + x) ^ 4‖ ≤ 8 := by
  have hpow : (1 + x) ≤ (1 + x) ^ 4 := by
    have h := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + x) (by norm_num : 1 ≤ 4)
    simpa using h
  have h4 : |x - 2| ≤ 2 * (1 + x) ^ 4 := by
    rw [abs_le]
    constructor <;> nlinarith [hpow, hx]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + x) ^ 4),
    div_le_iff₀ (by positivity : (0 : ℝ) < (1 + x) ^ 4), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  linarith

/-- `deriv F_*` is Lipschitz with constant `8` on `[0,∞)`: the fundamental model's
profile derivative cannot oscillate faster than this on the physical range of the
self-similar variable. -/
lemma fstarDerivLip {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') : |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'| ≤ 8 * |z - z'| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => 2 * (1 - y) / (1 + y) ^ 3)
    (f' := fun y : ℝ => 4 * (y - 2) / (1 + y) ^ 4)
    (s := Set.Ici 0) (C := 8) (x := z') (y := z)
    (fun y hy => (hasDerivAt_derivFstar y hy).hasDerivWithinAt)
    (fun y hy => norm_secondDerivFstar_le y hy)
    (convex_Ici 0) hz' hz
  rw [Work.FM.deriv_Fstar z (by linarith), Work.FM.deriv_Fstar z' (by linarith)]
  simpa [Real.norm_eq_abs] using h

end Work.FTS.Regularity.Moduli
