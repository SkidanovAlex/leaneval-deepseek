import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace Commons.Analysis.Complex

theorem sqrt_analyticAt {z : ℂ} (hz : z ∈ Complex.slitPlane) : AnalyticAt ℂ Complex.sqrt z := by
  -- `Complex.sqrt w` is by definition `w ^ (2⁻¹ : ℂ)` (complex power).
  -- Complex power is analytic in the base at points of the slit plane
  -- (Mathlib: `AnalyticAt.cpow`), so we apply that to `w ↦ w` and the
  -- constant exponent `w ↦ 2⁻¹`.
  change AnalyticAt ℂ (fun w : ℂ => w ^ (2⁻¹ : ℂ)) z
  apply AnalyticAt.cpow
  · exact analyticAt_id
  · exact analyticAt_const
  · exact hz

end Commons.Analysis.Complex