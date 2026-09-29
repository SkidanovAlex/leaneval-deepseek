import Mathlib.Analysis.RCLike.Sqrt

namespace Commons.Analysis.Complex

lemma sq_sqrt_of_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (Complex.sqrt z) ^ 2 = z := by
  simp [Complex.sqrt]

end Commons.Analysis.Complex