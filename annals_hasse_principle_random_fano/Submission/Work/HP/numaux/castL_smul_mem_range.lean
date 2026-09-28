import Mathlib
import Submission.Work.HP.numaux.rk_orthLatDefs

namespace Work.HP.numaux

open Finset

/-- Every rational vector acquires a nonzero integer multiple lying in the range of the
coordinatewise inclusion `ℤ^ι → ℚ^ι`: namely the product of the denominators of its
coordinates. -/
theorem castL_smul_mem_range {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℚ) :
    ∃ M : ℤ, M ≠ 0 ∧ M • y ∈ LinearMap.range (castL (ι := ι)) := by
  refine ⟨∏ i, ((y i).den : ℤ), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact_mod_cast (y i).den_nz
  · rw [LinearMap.mem_range]
    refine ⟨fun i => (y i).num * ∏ j ∈ Finset.univ.erase i, ((y j).den : ℤ), ?_⟩
    ext i
    rw [castL_apply, Pi.smul_apply, zsmul_eq_mul]
    push_cast
    rw [← Finset.prod_erase_mul Finset.univ (fun j => ((y j).den : ℚ)) (Finset.mem_univ i)]
    rw [← Rat.mul_den_eq_num]
    ring

end Work.HP.numaux
