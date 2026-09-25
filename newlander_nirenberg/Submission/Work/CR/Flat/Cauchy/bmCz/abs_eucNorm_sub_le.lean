import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

namespace Work.CR.Flat.Cauchy.bmCz

/-- `eucNorm` is the norm of `x` viewed as an element of `EuclideanSpace ℂ (Fin n)`. -/
private lemma eucNorm_eq_norm_withLp {n : ℕ} (x : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.eucNorm x = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [Work.CR.Flat.Cauchy.eucNorm]

/-- Reverse triangle inequality for the Euclidean norm. -/
theorem abs_eucNorm_sub_le {n : ℕ} (x y : Fin n → ℂ) :
    |Work.CR.Flat.Cauchy.eucNorm x - Work.CR.Flat.Cauchy.eucNorm y|
      ≤ Work.CR.Flat.Cauchy.eucNorm (x - y) := by
  rw [eucNorm_eq_norm_withLp x, eucNorm_eq_norm_withLp y, eucNorm_eq_norm_withLp (x - y)]
  have hsub : (WithLp.equiv 2 (Fin n → ℂ)).symm (x - y)
      = (WithLp.equiv 2 (Fin n → ℂ)).symm x - (WithLp.equiv 2 (Fin n → ℂ)).symm y := by
    simp [WithLp.equiv_symm_apply]
  rw [hsub]
  exact abs_norm_sub_norm_le _ _

end Work.CR.Flat.Cauchy.bmCz
