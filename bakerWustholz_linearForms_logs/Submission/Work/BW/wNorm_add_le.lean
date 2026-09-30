import Mathlib
import Submission.Work.BW.basisRed_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem wNorm_add_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (x y : Fin n → ℝ) : Work.BW.wNorm A c (x + y) ≤ Work.BW.wNorm A c x + Work.BW.wNorm A c y := by
  unfold Work.BW.wNorm
  set M : Matrix (Fin n) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
  have hterm : ∀ i, c i * |M.mulVec (x + y) i| ≤ c i * |M.mulVec x i| + c i * |M.mulVec y i| := by
    intro i
    calc c i * |M.mulVec (x + y) i|
        = c i * |M.mulVec x i + M.mulVec y i| := by rw [Matrix.mulVec_add, Pi.add_apply]
      _ ≤ c i * (|M.mulVec x i| + |M.mulVec y i|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (hc i)
      _ = c i * |M.mulVec x i| + c i * |M.mulVec y i| := mul_add _ _ _
  calc ∑ i, c i * |M.mulVec (x + y) i|
      ≤ ∑ i, (c i * |M.mulVec x i| + c i * |M.mulVec y i|) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, c i * |M.mulVec x i|) + (∑ i, c i * |M.mulVec y i|) := Finset.sum_add_distrib

end Work.BW
