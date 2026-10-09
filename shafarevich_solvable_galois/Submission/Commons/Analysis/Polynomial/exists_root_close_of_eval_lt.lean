import Mathlib
import Submission.Commons.Analysis.Polynomial.eval_norm_ge_of_factorization_far
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

/-- If `g = leadingCoeff * ∏ (X - β)` over a multiset `m` of roots and
`‖g.eval α‖ < ‖leadingCoeff‖ * η ^ m.card`, then some root `β ∈ m` satisfies
`‖α - β‖ < η`. This is the contrapositive of `eval_norm_ge_of_factorization_far`. -/
lemma exists_root_close_of_eval_lt {L : Type*} [NormedField L] (g : Polynomial L)
    {α : L} {η : ℝ} (hη : 0 < η) (m : Multiset L)
    (hfac : g = Polynomial.C g.leadingCoeff *
      (Multiset.map (fun β : L => Polynomial.X - Polynomial.C β) m).prod)
    (hlt : ‖g.eval α‖ < ‖g.leadingCoeff‖ * η ^ m.card) :
    ∃ β : L, β ∈ m ∧ ‖α - β‖ < η := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hge := eval_norm_ge_of_factorization_far (g := g) (η := η) hη.le m hfac h
  exact absurd hge (not_le.mpr hlt)

end Commons.Analysis.Polynomial
