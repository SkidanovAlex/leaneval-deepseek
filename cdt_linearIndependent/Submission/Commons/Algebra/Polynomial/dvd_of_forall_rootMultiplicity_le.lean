import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace Commons.Algebra.Polynomial

/-- If `q` is a nonzero polynomial over an algebraically closed field and every root
multiplicity of `q` is bounded by the corresponding root multiplicity of `Q`, then `q ∣ Q`. -/
theorem dvd_of_forall_rootMultiplicity_le {K : Type*} [Field K] [IsAlgClosed K]
    {q Q : Polynomial K} (hq : q ≠ 0)
    (h : ∀ α : K, Polynomial.rootMultiplicity α q ≤ Polynomial.rootMultiplicity α Q) :
    q ∣ Q := by
  classical
  refine Polynomial.Splits.dvd_of_roots_le_roots (IsAlgClosed.splits q) hq ?_
  rw [Multiset.le_iff_count]
  intro a
  rw [Polynomial.count_roots, Polynomial.count_roots]
  exact h a

end Commons.Algebra.Polynomial