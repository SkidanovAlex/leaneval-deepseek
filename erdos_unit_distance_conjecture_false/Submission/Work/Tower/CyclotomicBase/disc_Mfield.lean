import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.Mof_disc

namespace Work.Tower.CyclotomicBase

theorem disc_Mfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    |NumberField.discr ↥(Mfield r hr hr3)| =
      (((∏ i, (r i) ^ 2 : ℕ)) : ℤ) ^ (3 ^ (ℓ - 1)) := by
  rw [← Mof_univ r hr hr3]
  have h := (Mof_disc r hr hr3 hrinj Finset.univ).2
  simpa using h

end Work.Tower.CyclotomicBase
