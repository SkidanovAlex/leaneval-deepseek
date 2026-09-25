import Mathlib
import Submission.Commons.Analysis.Polynomial.eval_prod_X_sub_C
import Submission.Commons.Analysis.Polynomial.norm_multiset_prod
import Submission.Commons.Analysis.Polynomial.norm_prod_sub_ge

namespace Commons.Analysis.Polynomial

lemma eval_norm_ge_of_factorization_far {L : Type*} [NormedField L] (g : Polynomial L)
    {c : L} {α : L} {η : ℝ} (hη : 0 ≤ η) (m : Multiset L)
    (hfac : g = Polynomial.C c *
      (Multiset.map (fun β : L => Polynomial.X - Polynomial.C β) m).prod)
    (hfar : ∀ β ∈ m, η ≤ ‖α - β‖) :
    ‖c‖ * η ^ m.card ≤ ‖g.eval α‖ := by
  have h1 : g.eval α = c * (Multiset.map (fun β : L => α - β) m).prod := by
    rw [hfac, Polynomial.eval_mul, Polynomial.eval_C, eval_prod_X_sub_C]
  have hprod : (Multiset.map (fun z : L => ‖z‖)
        (Multiset.map (fun β : L => α - β) m)).prod
      = (Multiset.map (fun β : L => ‖α - β‖) m).prod := by
    rw [Multiset.map_map]
    rfl
  rw [h1, norm_mul, norm_multiset_prod, hprod]
  exact mul_le_mul_of_nonneg_left (norm_prod_sub_ge α η hη m hfar) (norm_nonneg c)

end Commons.Analysis.Polynomial
