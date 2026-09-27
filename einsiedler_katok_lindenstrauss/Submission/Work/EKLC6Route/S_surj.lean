import Mathlib
import Submission.Work.EKLC6Route.Defs

namespace Work.EKLC6Route

open Classical
open Work.EKLContract

/-- Unfolding the coding partition `Window.S`: the enumeration is driven by `Encodable.decode₂`
for the instance `Encodable.ofCountable PIdx` that `Window.S` installs locally. -/
private lemma Window.S_unfold {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ}
    (w : Window μ t) (n : ℕ) :
    w.S n = (match @Encodable.decode₂ Window.PIdx (Encodable.ofCountable Window.PIdx) n with
      | some p => w.piece p
      | none => ∅) := rfl

/-- `S` is a surjection onto the pieces: every piece `w.piece p` occurs in the enumeration. -/
theorem S_surj {μ : MeasureTheory.Measure Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (w : Work.EKLC6Route.Window μ t) (p : Work.EKLC6Route.Window.PIdx) :
    ∃ m : ℕ, w.S m = w.piece p := by
  refine ⟨@Encodable.encode Window.PIdx (Encodable.ofCountable Window.PIdx) p, ?_⟩
  rw [Window.S_unfold w, @Encodable.decode₂_encode Window.PIdx (Encodable.ofCountable Window.PIdx) p]

end Work.EKLC6Route
