import Mathlib
import Submission.Work.KT.hk_idem_C_pre

namespace Work.KT

open scoped Matrix

/-- Composing `combine` with the projection onto the first block (i.e. killing the second
block) equals multiplying by the diagonal matrix which is `1` on the first `r` coordinates
and `0` on the remaining ones, followed by `combine`. -/
theorem combine_conj (n r : ℕ) (hr : r ≤ n) :
    (combine n r hr).toLinearMap ∘ₗ (LinearMap.id.prodMap (0 : (Fin (n - r) → ℂ) →ₗ[ℂ] (Fin (n - r) → ℂ))) =
      (Matrix.toLin' (Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0))) ∘ₗ
        (combine n r hr).toLinearMap := by
  apply LinearMap.ext
  intro fg
  funext i
  change combineFun n r hr (fg.1, 0) i =
    (Matrix.toLin' (Matrix.diagonal fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0))
      (combineFun n r hr fg) i
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  simp only [combineFun_apply]
  split_ifs <;> simp

end Work.KT
