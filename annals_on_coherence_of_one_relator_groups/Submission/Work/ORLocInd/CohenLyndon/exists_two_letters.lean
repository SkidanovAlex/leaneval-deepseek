import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.exists_two_mem_relatorLetters_ne

/-!
# Two distinct letters in a relator that is not a proper power

If `r : FreeGroup α` is not a proper power and has `relatorNorm r ≥ 2`, then at least two distinct
generators occur in the reduced word of `r`.

Indeed, if only the single letter `x` occurred, the reduced word would be `x ^ (±k)` with `k ≥ 2`,
so `r` would be the proper power `(of x) ^ (±k)`; this is the content of the already-available
lemma `Work.OROneRel.exists_two_mem_relatorLetters_ne`, which we re-use here in the shape required
by the Cohen--Lyndon development (`∃ t x, t ≠ x ∧ ...`).
-/

namespace Work.ORLocInd.CohenLyndon

universe u

/-- A relator which is not a proper power and has norm at least two involves at least two distinct
generators. -/
theorem exists_two_letters {α : Type u} {r : FreeGroup α}
    (hpp : ¬ Work.OROneRel.IsProperPower r) (hr1 : r ≠ 1)
    (hlen : 2 ≤ Work.OROneRel.relatorNorm r) :
    ∃ t x : α, t ≠ x ∧ t ∈ Work.OROneRel.relatorLetters r ∧ x ∈ Work.OROneRel.relatorLetters r := by
  -- `hr1` is in fact redundant here (it follows from `hpp`), but we keep it in the signature.
  have _hne : r ≠ 1 := hr1
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Work.OROneRel.exists_two_mem_relatorLetters_ne r hlen hpp
  exact ⟨x, y, hxy, hx, hy⟩

end Work.ORLocInd.CohenLyndon
