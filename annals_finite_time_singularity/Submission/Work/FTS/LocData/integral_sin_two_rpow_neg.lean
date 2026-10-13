import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- The angular singularity `sin(2θ)^{-p}` of the weights is integrable on `Iθ = [0,π/2]`
for `0 < p < 1`, with an explicit bound `100/(1-p)` for its integral.

This is the case `q = -p ∈ (-1,0)` of `Work.Spaces.sin_two_rpow`, which controls
`sin(2θ)^q` on `Iθ` by the endpoint majorant `(π/4)^q (θ^q + (π/2-θ)^q)`. -/
theorem integral_sin_two_rpow_neg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-p)) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-p) ≤ 100 / (1 - p) := by
  have h := Work.Spaces.sin_two_rpow (-p) (by linarith) (by linarith)
  simpa only [neg_add_eq_sub] using h

end Work.FTS.LocData
