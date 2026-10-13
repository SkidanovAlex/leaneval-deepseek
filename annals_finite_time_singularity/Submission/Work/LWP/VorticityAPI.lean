/-
# `Work.LWP.VorticityAPI` — the curl as a bounded linear function of the derivative

`vorticity u x = ∑ i, e i ⨯₃ (fderiv ℝ u x (e i))`.  The right-hand side is a *fixed bounded
linear* function of the linear map `fderiv ℝ u x`; this module isolates that function and derives
the two consequences used by the local existence argument:

* `Work.LWP.isBoundedFun_vorticity`  — `Du` bounded ⟹ `ω` bounded;
* `Work.LWP.holder_vorticity`        — `Du` `α`-Hölder ⟹ `ω` `α`-Hölder.

Both are immediate from `‖ω x - ω y‖ ≤ 3 ‖Du x - Du y‖` and `‖ω x‖ ≤ 3 ‖Du x‖`
(`Work.LWP.norm_vorticity_le`), the factor `3 = card (Fin 3)` being the price of the three-term
curl.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

open scoped Matrix

/-- The curl, as a function of the derivative alone:
`T ↦ WithLp.toLp 2 (∑ i, e i ⨯₃ T (e i))`. -/
noncomputable def curlLinear (T : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (T (FiniteTimeSingularity.e i)))

/-- `vorticity u` is `curlLinear` post-composed with `fderiv ℝ u`. -/
lemma vorticity_eq_curlLinear (u : R3 → R3) :
    vorticity u = curlLinear ∘ fderiv ℝ u := by
  funext x
  rfl

end Work.LWP
