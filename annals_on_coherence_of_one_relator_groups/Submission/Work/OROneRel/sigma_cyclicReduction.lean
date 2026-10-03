import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate

namespace Work.OROneRel

/-- `sigma t` is invariant under cyclic reduction: `cyclicReduction w` is conjugate to `w`,
and `sigma t` is a homomorphism into the abelian group `Multiplicative ℤ`. -/
theorem sigma_cyclicReduction {α : Type*} (w : FreeGroup α) (t : α) :
    Work.OROneRel.sigma t (Work.OROneRel.cyclicReduction w) = Work.OROneRel.sigma t w := by
  have h := cyclicConjugator_mul_cyclicReduction_mul_inv w
  conv_rhs => rw [← h]
  simp only [map_mul, map_inv]
  rw [mul_comm (sigma t (cyclicConjugator w)) (sigma t (cyclicReduction w))]
  simp

end Work.OROneRel
