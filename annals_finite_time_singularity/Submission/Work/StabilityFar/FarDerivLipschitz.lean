/-
# `Work.StabilityFar.FarDerivLipschitz` — the `x`-Lipschitz bound for `Dₓu` in the far region

`St4` consumes the hypothesis that `x ↦ fderiv ℝ (u(·,t)) x` is Lipschitz on the far region
(`FarDerivLipschitz`).  This module *derives* it from the vorticity data: the second-order
Biot–Savart estimate `Work.StabilityFar.Decay.farField_fderiv_sub_le` (Lipschitz bound for the
derivative of `BS ω` on `{2R ≤ ‖x‖}`, uniform in `t`) together with the slicewise identification
`u(·,t) = BS(ω(·,t))`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Decay
import Submission.Work.StabilityFar.Decay.farField_fderiv_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-- **`FarDerivLipschitz` from the vorticity data.**  For a vorticity whose slices are measurable,
bounded by `M` and supported in `B(0,R)`, the spatial derivative of `u = BS ω` is Lipschitz on
`{2R < ‖x‖}` with a constant uniform in `t ∈ window T`. -/
theorem farDerivLipschitz_of_biotSavart {ω u : R3 → ℝ → R3} {R M T : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hbs : IsBiotSavartSlice u ω T) (hbdd : SlicesBounded ω M T) (hsupp : SlicesSupported ω R T)
    (hmeas : SlicesMeasurable ω T) :
    ∃ A : ℝ, 0 ≤ A ∧ FarDerivLipschitz A (2 * R) T u := by
  obtain ⟨A, hA, hb⟩ := Decay.farField_fderiv_sub_le hR hM hmeas hbdd hsupp
  refine ⟨A, hA, fun t ht x y hx hy => ?_⟩
  have hfun : (u · t) = fun z => Work.LWP.biotSavart (fun w => ω w t) z :=
    funext (fun z => hbs t ht z)
  rw [hfun]
  exact hb t ht x y hx.le hy.le

end Work.StabilityFar
