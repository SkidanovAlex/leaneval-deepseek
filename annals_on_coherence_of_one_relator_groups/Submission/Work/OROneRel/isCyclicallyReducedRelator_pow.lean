import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- Powers of a cyclically reduced relator are cyclically reduced: if the reduced word of `r` is
cyclically reduced, then the concatenation of `n` copies of it is already reduced (its cyclic
reduction is itself), hence equals the reduced word of `r ^ n`. -/
theorem isCyclicallyReducedRelator_pow {α : Type u} {r : FreeGroup α}
    (h : Work.OROneRel.IsCyclicallyReducedRelator r) (n : ℕ) :
    Work.OROneRel.IsCyclicallyReducedRelator (r ^ n) := by
  classical
  unfold Work.OROneRel.IsCyclicallyReducedRelator at *
  rw [FreeGroup.toWord_pow]
  have hc : FreeGroup.IsCyclicallyReduced (List.replicate n (FreeGroup.toWord r)).flatten :=
    h.flatten_replicate n
  rw [hc.isReduced.reduce_eq]
  exact hc

end Work.OROneRel
