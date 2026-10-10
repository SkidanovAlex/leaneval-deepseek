import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Field.Basic
import Submission.Commons.Analysis.Normed.exists_separation_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Normed

lemma exists_root_separation {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (f : Polynomial K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x : L⦄, x ∈ Polynomial.rootSet f L → ∀ ⦃y : L⦄, y ∈ Polynomial.rootSet f L →
      x ≠ y → δ ≤ ‖x - y‖ := by
  exact exists_separation_of_finite (Polynomial.rootSet f L) (Polynomial.rootSet_finite f L)

end Commons.Analysis.Normed
