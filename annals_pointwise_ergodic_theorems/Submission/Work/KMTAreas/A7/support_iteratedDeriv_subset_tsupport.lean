import Mathlib

namespace Work.KMTAreas.A7

/-- The support of the `n`-th iterated derivative of `f : ℝ → ℂ` is contained in the
topological support of `f`.  Indeed, `tsupport f = closure (support f)` is closed, so its
complement is open, and on it `f` vanishes identically; hence so do all of its iterated
derivatives. -/
theorem support_iteratedDeriv_subset_tsupport (f : ℝ → ℂ) (n : ℕ) :
    Function.support (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simpa using subset_tsupport f
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact (support_deriv_subset (f := iteratedDeriv k f)).trans
        (closure_minimal ih (isClosed_tsupport f))

end Work.KMTAreas.A7
