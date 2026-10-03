import Mathlib
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.ntDefs

namespace Work.ORLocInd.CohenLyndon

universe u

/-- Cyclic reduction of a word never increases its length.  This is immediate from
`FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically`, which exhibits the word as
`conjugator L ++ reduceCyclically L ++ invRev (conjugator L)`. -/
theorem length_reduceCyclically_le {α : Type u} [DecidableEq α] (L : List (α × Bool)) :
    (FreeGroup.reduceCyclically L).length ≤ L.length := by
  have h := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L
  have h2 : (FreeGroup.reduceCyclically.conjugator L ++
      FreeGroup.reduceCyclically L ++
      FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L)).length
      = L.length := by rw [h]
  rw [List.length_append, List.length_append, FreeGroup.invRev_length] at h2
  omega

/-- Cyclic reduction does not increase the relator norm: `relatorNorm` is the length of the
reduced word, and `cyclicReduction r` is represented by the no-longer word
`reduceCyclically r.toWord`. -/
theorem relatorNorm_cyclicReduction_le {α : Type u} (r : FreeGroup α) :
    Work.OROneRel.relatorNorm (Work.OROneRel.cyclicReduction r) ≤
      Work.OROneRel.relatorNorm r := by
  classical
  calc Work.OROneRel.relatorNorm (Work.OROneRel.cyclicReduction r)
      = FreeGroup.norm (FreeGroup.mk (FreeGroup.reduceCyclically r.toWord)) := by
        simp only [Work.OROneRel.relatorNorm, Work.OROneRel.cyclicReduction]
    _ ≤ (FreeGroup.reduceCyclically r.toWord).length := FreeGroup.norm_mk_le
    _ ≤ r.toWord.length := length_reduceCyclically_le r.toWord
    _ = Work.OROneRel.relatorNorm r := rfl

end Work.ORLocInd.CohenLyndon
