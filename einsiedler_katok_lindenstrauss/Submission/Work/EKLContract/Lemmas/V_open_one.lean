import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-- `V δ` is the finite intersection of the open entrywise conditions. -/
theorem V_eq_iInter (δ : ℝ) :
    Work.EKLContract.V δ = ⋂ i : Fin 3, ⋂ j : Fin 3,
      {g : SL3 | |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ} := by
  ext g
  simp [Work.EKLContract.V]

theorem V_open_one (δ : ℝ) (hδ : 0 < δ) : IsOpen (Work.EKLContract.V δ) ∧ (1 : Work.EKLContract.SL3) ∈ Work.EKLContract.V δ := by
  constructor
  · rw [V_eq_iInter]
    refine isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j => ?_))
    apply isOpen_lt _ continuous_const
    fun_prop
  · intro i j
    have h1 : (1 : SL3) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := rfl
    rw [h1, sub_self, abs_zero]
    exact hδ

end Work.EKLContract.Lemmas
