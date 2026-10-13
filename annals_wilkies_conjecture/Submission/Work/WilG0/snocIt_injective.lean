import Mathlib
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd

namespace Work.WilG0

theorem snocIt_injective (n m : ℕ) :
    Function.Injective (fun p : (Fin n → ℝ) × (Fin m → ℝ) => snocIt n m p.1 p.2) := by
  intro p q h
  change snocIt n m p.1 p.2 = snocIt n m q.1 q.2 at h
  have hx : p.1 = q.1 := by
    funext i
    rw [← snocIt_castAdd n m p.1 p.2 i, h, snocIt_castAdd n m q.1 q.2 i]
  have hw : p.2 = q.2 := by
    funext j
    rw [← snocIt_natAdd n m p.1 p.2 j, h, snocIt_natAdd n m q.1 q.2 j]
  exact Prod.ext hx hw

end Work.WilG0
