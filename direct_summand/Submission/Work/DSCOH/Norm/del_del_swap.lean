import Mathlib
import Submission.Work.DSCOH.Norm.Defs

namespace Work.DSCOH.Norm

theorem del_del_swap {ι : Type*} {N : ℕ} (z : Fin (N+3) → ι) (b : Fin (N+3)) (c : Fin (N+2)) :
    del (del z (b.succAbove c)) (c.predAbove b) = del (del z b) c := by
  funext a
  -- Both sides are functions `Fin (N+1) → ι`.  Evaluating at `a` and unfolding `del` leaves
  -- the index identity `(b.succAbove c).succAbove ((c.predAbove b).succAbove a) =
  -- b.succAbove (c.succAbove a)`, which Mathlib has.
  simp only [del_apply]
  exact congrArg z (Fin.succAbove_succAbove_succAbove_predAbove b c a)

end Work.DSCOH.Norm
