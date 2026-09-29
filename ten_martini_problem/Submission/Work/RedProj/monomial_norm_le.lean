import Mathlib
import Submission.Work.RedProj.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RedProj

/-- The product of the norms of the coordinate projections appearing in `monomial n m` is at
most `1`. -/
lemma prod_norm_proj_le (n m : ℕ) :
    ∏ i : Fin n, ‖(if (i : ℕ) < m then pi1 else pi2)‖ ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro i _; positivity
  · intro i _
    split
    · exact ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ
    · exact ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ

theorem monomial_norm_le (n m : ℕ) : ‖monomial n m‖ ≤ 1 := by
  rw [monomial]
  calc ‖(ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
          (fun i : Fin n => if (i : ℕ) < m then pi1 else pi2)‖
      ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ‖ *
          ∏ i : Fin n, ‖(if (i : ℕ) < m then pi1 else pi2)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ∏ i : Fin n, ‖(if (i : ℕ) < m then pi1 else pi2)‖ := by
        rw [ContinuousMultilinearMap.norm_mkPiAlgebra, one_mul]
    _ ≤ 1 := prod_norm_proj_le n m

end Work.RedProj
