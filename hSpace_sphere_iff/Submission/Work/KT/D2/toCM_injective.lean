import Mathlib
import Submission.Work.KT.D2.Winding

namespace Work.KT.D2

theorem toCM_injective (N : ℕ)
    (M M' : Matrix (Fin N) (Fin N) (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))))
    (h : ∀ x, Work.KT.D2.toCM N M x = Work.KT.D2.toCM N M' x) : M = M' := by
  funext i j
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  have hx : Work.KT.D2.toCM N M x i j = Work.KT.D2.toCM N M' x i j := by rw [h x]
  simpa [Work.KT.D2.toCM_apply, evalAt] using hx

end Work.KT.D2
