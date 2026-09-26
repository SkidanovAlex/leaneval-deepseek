import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

theorem isModularFormOfWeight_E4 : IsModularFormOfWeight 4 E4 := by
  let m : (j : Fin (0 + 1)) → ModularForm 𝒮ℒ (4 - 2 * (j : ℤ)) :=
    Fin.cases ModularForm.E₄ (fun j => j.elim0)
  refine ⟨m, ?_⟩
  rw [Fin.sum_univ_one]
  simp [m, E4]

end Work.Modular
