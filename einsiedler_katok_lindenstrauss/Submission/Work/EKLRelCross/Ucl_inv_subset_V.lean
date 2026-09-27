import Mathlib
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLProd.inv_entries_bound
import Submission.Work.EKLRelCross.exists_Ucl_bound

namespace Work.EKLRelCross

/-- An element of the closed ball `Ucl U a` has its inverse in the *open* displacement
neighbourhood `V (2(1+a)² + 2)`.  This is `Ucl_inv_mem` (`g⁻¹ ∈ Ucl U (2(1+a)²+1)`)
combined with the strict inequality `2(1+a)²+1 < 2(1+a)²+2`. -/
theorem Ucl_inv_subset_V {U : Subgroup Work.EKLContract.SL3} {a : ℝ} (ha : 0 ≤ a)
    {g : Work.EKLContract.SL3} (hg : g ∈ Work.EKLRelCross.Ucl U a) :
    g⁻¹ ∈ Work.EKLContract.V (2 * (1 + a) ^ 2 + 2) := by
  intro i j
  have hle := (Ucl_inv_mem (U := U) ha hg).2 i j
  simp only [LamU] at hle
  linarith

end Work.EKLRelCross
