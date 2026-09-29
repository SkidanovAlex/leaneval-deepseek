import Mathlib.Analysis.RCLike.Sqrt

namespace Commons.Analysis.Complex

lemma sqrt_ne_zero_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.sqrt z ≠ 0 := by
  rw [sqrt_eq_exp (Complex.slitPlane_ne_zero hz)]
  exact Complex.exp_ne_zero _

end Commons.Analysis.Complex