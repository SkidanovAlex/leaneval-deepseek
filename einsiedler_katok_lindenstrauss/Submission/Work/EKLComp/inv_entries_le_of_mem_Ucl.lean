import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLProd.inv_entries_bound

namespace Work.EKLComp

/-- Every entry of `g⁻¹` is bounded by `2 (1+r)²` for `g` in the closed `U`-ball of radius `r`.
Since `g ∈ Ucl U r` implies `|g i j| ≤ 1 + r`, the inverse is (up to sign) the adjugate of `g`,
whose entries are `2 × 2` minors, bounded by `2 (1+r)²`. -/
theorem inv_entries_le_of_mem_Ucl {U : Subgroup Work.EKLContract.SL3} {r : ℝ} (hr : 0 < r)
    {g : Work.EKLContract.SL3} (hg : g ∈ Work.EKLComp.Ucl U r) (i j : Fin 3) :
    |((g⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 * (1 + r) ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  refine Work.EKLProd.abs_adjugate_entry_le (by linarith) (fun p q => ?_) i j
  have hlt : |(g : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| ≤ r :=
    hg.2 p q
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  calc |(g : Matrix (Fin 3) (Fin 3) ℝ) p q|
      = |((g : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := by rw [sub_add_cancel]
    _ ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := abs_add_le _ _
    _ ≤ r + 1 := add_le_add hlt hone
    _ = 1 + r := by ring

end Work.EKLComp
