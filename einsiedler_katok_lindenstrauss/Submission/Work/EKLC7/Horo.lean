import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLContract.Lemmas.isHoro_Upar
import Submission.Work.EKLContract.Lemmas.isHoro_sup_same_source
import Submission.Work.EKLContract.Lemmas.isHoro_sup_same_target

namespace Work.EKLC7

open Work.EKLContract

/-- The Heisenberg group `Heis3 = U_ij ⊔ U_jk ⊔ U_ik` is the group `Upar` of
`isHoro_Upar` with parameters `(a,b,c) = (i,k,j)`, since this gives the three root groups
`U_ik ⊔ U_ij ⊔ U_jk`. -/
theorem heis3_eq_upar {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Heis3 hij hjk hik = Upar hik hij hjk := by
  rw [Heis3, Upar]
  ac_rfl

theorem Horo : ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
    Work.EKLContract.IsHoro (Work.EKLC7.Heis3 hij hjk hik)
      ∧ Work.EKLContract.IsHoro (Work.EKLC7.VjkIk hjk hik)
      ∧ Work.EKLContract.IsHoro (Work.EKLC7.VijIk hij hik) := by
  intro i j k hij hjk hik
  refine ⟨?_, ?_, ?_⟩
  · rw [heis3_eq_upar hij hjk hik]
    exact Work.EKLContract.Lemmas.isHoro_Upar hik hij hjk
  · exact Work.EKLContract.Lemmas.isHoro_sup_same_target hjk hik
  · exact Work.EKLContract.Lemmas.isHoro_sup_same_source hij hik

end Work.EKLC7
