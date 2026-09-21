import Mathlib

namespace Commons.Geometry.Ulam

/-- If the support of `f` lies in `s`, then `f` vanishes outside `s`. -/
lemma support_subset_iff_zero_of_not_mem {f : ℝ → ℝ} {s : Set ℝ}
    (h : Function.support f ⊆ s) {x : ℝ} (hx : x ∉ s) : f x = 0 := by
  by_contra hf
  exact hx (h (by simpa [Function.mem_support] using hf))

end Commons.Geometry.Ulam
