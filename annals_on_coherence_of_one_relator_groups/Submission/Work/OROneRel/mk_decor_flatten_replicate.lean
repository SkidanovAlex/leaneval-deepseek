import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.decor_flatten_replicate_gen

namespace Work.OROneRel

/-- `FreeGroup.mk` of a flattened repetition is a power: this is `mul_mk` iterated. -/
private theorem mk_flatten_replicate_pow {β : Type*} (M : List (β × Bool)) (l : ℕ) :
    FreeGroup.mk (List.flatten (List.replicate l M)) = (FreeGroup.mk M) ^ l := by
  induction l with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero, FreeGroup.one_eq_mk]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

theorem mk_decor_flatten_replicate {α : Type*} (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) (l : ℕ)
    (hL : Work.OROneRel.lsig c L = 0) :
    FreeGroup.mk (Work.OROneRel.decor c i (List.flatten (List.replicate l L))) =
      (FreeGroup.mk (Work.OROneRel.decor c i L)) ^ l := by
  rw [decor_flatten_replicate_gen c L hL i l]
  exact mk_flatten_replicate_pow (Work.OROneRel.decor c i L) l

end Work.OROneRel
