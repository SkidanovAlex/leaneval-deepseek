import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Prob.Basic
import Submission.Work.Deep.Prob.Spaces

namespace Work.Deep.Prob.Spaces

open scoped BigOperators

/-- Under the uniform measure on a nonempty finite type, the probability of an event `A` is
its cardinality divided by the cardinality of the sample space. -/
theorem uniform_prob_ncard {Ω : Type*} [Fintype Ω] [Nonempty Ω] (A : Set Ω) :
    (FinProbSpace.uniform Ω).prob A = (A.ncard : ℝ) / (Fintype.card Ω : ℝ) := by
  classical
  -- The uniform mass is `(Fintype.card Ω)⁻¹`, so the probability of `A` is
  -- `(number of elements of A) · (Fintype.card Ω)⁻¹`.
  have hF : (Finset.univ.filter (fun ω : Ω => ω ∈ A)).card = A.ncard := by
    rw [Set.ncard_eq_toFinset_card A A.toFinite]
    congr 1
    ext x
    simp
  rw [FinProbSpace.prob]
  simp only [FinProbSpace.uniform_mass, Set.indicator_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hF]
  rw [div_eq_mul_inv]

end Work.Deep.Prob.Spaces
