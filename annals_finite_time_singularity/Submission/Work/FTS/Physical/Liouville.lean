/-
# `Work.FTS.Physical.Liouville` — the div-curl identification

The paper constructs the velocity as the stream-function field `psiField Φ` of the fake-time
solution, and proves that it solves the Euler vorticity equation.  To transfer this to the physical
Biot–Savart velocity `BS ω` one needs to know that the two agree.  The classical argument is
div-curl uniqueness: two `C¹` divergence-free fields of sublinear growth with the same curl differ
by an odd sublinear harmonic field, which vanishes.

This module reduces that identification to the analytic input `DivCurlLiouville` of `Defs.lean`,
which is stated directly in the "two fields with the same curl" form so that no linearity lemmas
for `div` and `vorticity` are needed.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

/-- **Div-curl uniqueness.**  Two `C¹`, divergence-free fields of sublinear growth whose curls
agree (`∇×u = ∇×v`) and whose difference is odd are equal.  This is the statement that the curl is
injective on the odd sublinear divergence-free fields, and it is the identification step of the
physical reconstruction: it shows that the paper's stream-function field equals the Biot–Savart
field of the physical vorticity.

The proof is a direct application of the input `DivCurlLiouville`. -/
theorem eq_of_curl_eq (hLiou : DivCurlLiouville) {u v : R3 → R3}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hdivu : div u = 0) (hdivv : div v = 0)
    (hcurl : ∀ x : R3, vorticity u x = vorticity v x)
    (husub : Sublinear u) (hvsub : Sublinear v) (hodd : IsOdd (u - v)) :
    u = v :=
  funext (fun x => hLiou u v hu hv (fun y => congrFun hdivu y) (fun y => congrFun hdivv y)
    (fun y => hcurl y) husub hvsub hodd x)

end Work.FTS.Physical
