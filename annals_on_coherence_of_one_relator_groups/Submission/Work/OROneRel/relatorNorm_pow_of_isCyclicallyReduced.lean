import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# The length of powers of a cyclically reduced relator

If `r` is a cyclically reduced word, then already the concatenation of `n` copies of the reduced
word of `r` is reduced (this is `FreeGroup.IsCyclicallyReduced.flatten_replicate`), so the reduced
word of `r ^ n` is that concatenation and has length `n * relatorNorm r`.
-/

namespace Work.OROneRel

universe u

theorem relatorNorm_pow_of_isCyclicallyReduced {α : Type u} (r : FreeGroup α)
    (h : Work.OROneRel.IsCyclicallyReducedRelator r) (n : ℕ) :
    Work.OROneRel.relatorNorm (r ^ n) = n * Work.OROneRel.relatorNorm r := by
  classical
  have hh : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord r) := by
    simpa only [IsCyclicallyReducedRelator] using h
  have hred : FreeGroup.IsReduced (List.flatten (List.replicate n (FreeGroup.toWord r))) :=
    (hh.flatten_replicate n).1
  have htw : FreeGroup.toWord (r ^ n)
      = List.flatten (List.replicate n (FreeGroup.toWord r)) := by
    rw [FreeGroup.toWord_pow, hred.reduce_eq]
  rw [relatorNorm, FreeGroup.norm, htw]
  simp [List.length_flatten, List.sum_replicate, relatorNorm, FreeGroup.norm]

end Work.OROneRel
