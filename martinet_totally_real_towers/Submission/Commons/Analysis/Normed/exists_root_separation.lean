import Mathlib
import Submission.Commons.Analysis.Normed.exists_separation_of_finite

namespace Commons.Analysis.Normed

lemma exists_root_separation {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (f : Polynomial K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x : L⦄, x ∈ Polynomial.rootSet f L → ∀ ⦃y : L⦄, y ∈ Polynomial.rootSet f L →
      x ≠ y → δ ≤ ‖x - y‖ := by
  exact exists_separation_of_finite (Polynomial.rootSet f L) (Polynomial.rootSet_finite f L)

end Commons.Analysis.Normed
