/-
# The angular gap-Wirtinger development: shared vocabulary

This file fixes the objects and elementary calculus facts used by the proof of

  `Work.FTS.EllipticEst.ang_gap_wirtinger`

(Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates'; the sharp
gap-Wirtinger inequality `16 ∫ h² ≤ ∫ h'²` for `h` vanishing at the endpoints of
`[0,π/2]` with `∫ h sin 2θ = 0`).

The route used here is the second one in the statement's documentation: the
primitive `G θ = ∫₀^θ h s sin(2s) ds` and its quotient `V = G/sin 2θ`, for which
the three exact identities

* `∫_I Q² = ∫_I h'² - 4 ∫_I h²`   with `Q = h' - 2 cot(2θ) h`  (completion of squares),
* `12 ∫_I V² ≤ ∫_I h²`                                        (weighted Hardy),
* `∫_I h² = - ∫_I V · Q`                                       (integration by parts),

together with the Cauchy–Schwarz inequality `(∫ VQ)² ≤ (∫ V²)(∫ Q²)` give
`12 ∫ h² ≤ ∫ Q² = ∫ h'² - 4 ∫ h²`, i.e. `16 ∫ h² ≤ ∫ h'²`.

This file contains only definitions and the elementary facts about `cot(2θ)`
that all three identities need.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

set_option autoImplicit false

/-- `sin (2θ)`, the weight of the angular problem. -/
def angS (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- `cos (2θ)`. -/
def angC (θ : ℝ) : ℝ := Real.cos (2 * θ)

/-- The primitive `G θ = ∫₀^θ h s · sin (2s) ds` of `h · sin 2θ`. -/
def angG (h : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ s in (0 : ℝ)..θ, h s * Real.sin (2 * s)

/-- `V = G / sin 2θ`, the `K`-variable of the weighted problem. -/
def angV (h : ℝ → ℝ) (θ : ℝ) : ℝ := angG h θ / Real.sin (2 * θ)

/-- `Q = h' - 2 cot(2θ) · h = sin 2θ · (h / sin 2θ)'`. -/
def angQ (h : ℝ → ℝ) (θ : ℝ) : ℝ := deriv h θ - 2 * Real.cot (2 * θ) * h θ

/-- The antiderivative of the completion-of-squares identity: `Φ_D = -2 h² cot 2θ`. -/
def angPhiD (h : ℝ → ℝ) (θ : ℝ) : ℝ := -2 * (h θ) ^ 2 * Real.cot (2 * θ)

/-- The antiderivative of the weighted Hardy identity: `Φ_H = 6 V² cot 2θ = 6 G² cos2θ / sin³2θ`. -/
def angPhiH (h : ℝ → ℝ) (θ : ℝ) : ℝ := 6 * (angV h θ) ^ 2 * Real.cot (2 * θ)

/-- The antiderivative of the integration-by-parts identity: `Φ_C = V · h = G h / sin 2θ`. -/
def angPhiC (h : ℝ → ℝ) (θ : ℝ) : ℝ := angV h θ * h θ

/-! ## Elementary facts about `sin (2θ)` and `cot (2θ)` on `(0, π/2)` -/

/-- On `(0, π/2)`, `sin (2θ) > 0`. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The derivative of `θ ↦ cot (2θ)` on `(0, π/2)`. -/
theorem hasDerivAt_cot_two (x : ℝ) (hx : x ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ : ℝ => Real.cot (2 * θ)) (-2 * (1 + (Real.cot (2 * x)) ^ 2)) x := by
  have hsinpos : 0 < Real.sin (2 * x) := sin_two_pos hx
  have hsin : Real.sin (2 * x) ≠ 0 := ne_of_gt hsinpos
  have h1 : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-(2 * Real.sin (2 * x))) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_cos (2 * x)).comp x (hasDerivAt_const_mul (x := x) (2 : ℝ))
  have h2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * x)).comp x (hasDerivAt_const_mul (x := x) (2 : ℝ))
  have h3 := h1.div h2 hsin
  have hfun : (fun θ : ℝ => Real.cot (2 * θ))
      = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) := by
    funext θ; rw [Real.cot_eq_cos_div_sin]
  rw [hfun]
  refine h3.congr_deriv ?_
  have hcot : Real.cot (2 * x) = Real.cos (2 * x) / Real.sin (2 * x) := Real.cot_eq_cos_div_sin (2 * x)
  rw [hcot]
  field_simp
  ring_nf

/-- On `(0, π/2)`, `|cot (2θ)| ≤ 1/sin (2θ)`. -/
theorem abs_cot_two_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Real.cot (2 * θ)| ≤ 1 / Real.sin (2 * θ) := by
  have hsinpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinpos]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsinpos.le

end Work.FTS.EllipticEst.AngGap
