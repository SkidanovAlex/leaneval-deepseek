import Submission.Work.Smooth.Jordan.Defs

/-!
# The winding integral and the index of a smooth plane curve

For a `C¹` closed curve `c : ℝ → ℂ` (a `SmoothPlaneCurve`) and a point `x ∉ ` its trace, the
**winding integral** is the contour integral

`wind c x = (2πi)⁻¹ ∮ dz/(z - x) = (2πi)⁻¹ ∫₀^{2π} γ'(t)/(γ(t) - x) dt`,

and the **index** `ind c x : ℤ` is that complex number, which is an integer
(`Work.Smooth.Jordan.wind_mem_int`).  For `x` on the trace the index is set to `0`; every
statement about it carries the hypothesis `x ∉ trace c`.

This is the definition of the winding number of a curve around a point which the chapter uses
throughout; it is *not* the topological (degree) definition, but for `C¹` curves the two agree, and
the analytic definition is the one which supports the elementary proofs of integrality, local
constancy and vanishing at infinity collected here.

## Main definitions

* `windingIntegrand c x` — the function `t ↦ γ'(t)/(γ(t) - x)`;
* `windingPrimitive c x t` — `∫₀^t γ'(s)/(γ(s) - x) ds`;
* `wind c x` — the winding integral `(2πi)⁻¹ ∫₀^{2π} γ'(t)/(γ(t) - x) dt`;
* `ind c x` — the index as an integer.

## Main results

* `Work.Smooth.Jordan.wind_mem_int` — `wind c x` is an integer for `x ∉ trace c`;
* `Work.Smooth.Jordan.ind_spec` — `(ind c x : ℂ) = wind c x` whenever the latter is an integer;
* `Work.Smooth.Jordan.continuous_windingIntegrand`;
* the primitive/proof ingredients (`windingPrimitive_hasDerivAt`,
  `windingPrimitive_const_exp`, `windingPrimitive_int`) are in the sibling modules of this
  directory.
-/

open Set
open Classical

namespace Work.Smooth.Jordan

noncomputable section

/-- The integrand `t ↦ γ'(t)/(γ(t) - x)` of the winding integral. -/
def windingIntegrand (c : SmoothPlaneCurve) (x : ℂ) : ℝ → ℂ :=
  fun t => deriv c.γ t / (c.γ t - x)

@[simp] theorem windingIntegrand_apply (c : SmoothPlaneCurve) (x : ℂ) (t : ℝ) :
    windingIntegrand c x t = deriv c.γ t / (c.γ t - x) := rfl

/-- The primitive `t ↦ ∫₀^t γ'(s)/(γ(s) - x) ds` of the integrand. -/
noncomputable def windingPrimitive (c : SmoothPlaneCurve) (x : ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, windingIntegrand c x s

@[simp] theorem windingPrimitive_zero (c : SmoothPlaneCurve) (x : ℂ) :
    windingPrimitive c x 0 = 0 :=
  intervalIntegral.integral_same

/-- The integrand is continuous off the trace of the curve. -/
theorem continuous_windingIntegrand (c : SmoothPlaneCurve) {x : ℂ} (hx : x ∉ c.trace) :
    Continuous (windingIntegrand c x) := by
  refine c.continuous_deriv.div (c.cont.sub continuous_const) (fun t => ?_)
  simp only [sub_ne_zero]
  exact fun h => hx (h ▸ c.mem_trace t)

/-- The **winding integral** of a `C¹` closed curve around a point: `(2πi)⁻¹∮ dz/(z - x)`. -/
noncomputable def wind (c : SmoothPlaneCurve) (x : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * windingPrimitive c x (2 * Real.pi)

@[simp] theorem wind_def (c : SmoothPlaneCurve) (x : ℂ) :
    wind c x = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * windingPrimitive c x (2 * Real.pi) := rfl

/-- The **index** (winding number) of a `C¹` closed curve around a point, as an integer.

For `x` off the trace, `(ind c x : ℂ)` is the winding integral `wind c x`
(`Work.Smooth.Jordan.wind_mem_int`, `Work.Smooth.Jordan.ind_spec`).  On the trace the index is set
to `0`; every statement about it carries the hypothesis `x ∉ trace c`. -/
noncomputable def ind (c : SmoothPlaneCurve) (x : ℂ) : ℤ :=
  if h : ∃ k : ℤ, wind c x = (k : ℂ) then Classical.choose h else 0

/-- Characterising property of `ind`: it is the integer whose cast is the winding integral,
whenever the winding integral is an integer. -/
theorem ind_spec (c : SmoothPlaneCurve) {x : ℂ} (h : ∃ k : ℤ, wind c x = (k : ℂ)) :
    (ind c x : ℂ) = wind c x := by
  rw [ind, dif_pos h]
  exact (Classical.choose_spec h).symm

end

end Work.Smooth.Jordan
