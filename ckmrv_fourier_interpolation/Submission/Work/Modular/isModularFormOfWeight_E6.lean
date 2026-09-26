import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- The (normalized) weight-six Eisenstein series `E₆` is a modular form of weight `6`
in the sense of `IsModularFormOfWeight`: it is quasimodular of depth `0`.  Indeed
`E₆ = ⇑ModularForm.E₆` is the underlying function of Mathlib's modular form `E₆`. -/
theorem isModularFormOfWeight_E6 : IsModularFormOfWeight 6 E6 := by
  unfold IsModularFormOfWeight IsQuasiModularFormDepth
  refine ⟨fun j => Fin.eq_zero j ▸ (ModularForm.E₆ : ModularForm 𝒮ℒ 6), ?_⟩
  rw [Finset.sum_eq_single 0]
  · simp [E6]
  · intro b _ hb
    exact absurd (Fin.eq_zero b) hb
  · intro h
    exact absurd (Finset.mem_univ 0) h

end Work.Modular
