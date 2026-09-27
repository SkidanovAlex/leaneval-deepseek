import Mathlib

namespace Work.Mostow

/-- The linear interpolation between the identity and a `C¹` map is `C¹`. -/
theorem contDiffInterp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ContDiff ℝ 1 (fun y => (1 - t) • y + t • f y) := by
  have h1 : ContDiff ℝ 1 (fun y : E => (1 - t) • y) := contDiff_id.const_smul (1 - t)
  have h2 : ContDiff ℝ 1 (fun y : E => t • f y) := hf.const_smul t
  exact h1.add h2

end Work.Mostow
