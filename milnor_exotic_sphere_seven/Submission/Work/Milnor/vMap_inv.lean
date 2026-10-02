import Mathlib
import Submission.Work.Milnor.VBundleDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Milnor

open Submission.Milnor

/-! ## The twisting of the fibre and its inverse

`vTwist m q y = q ^ m * y * q⁻¹` and `vTwistInv m q y = q ^ (-m) * y * q` are mutually inverse
for every nonzero `q : ℍ` (in particular for the unit direction `unitDir x`). -/

/-- `vTwist m q` and `vTwistInv m q` are mutually inverse on `ℍ`, for `q ≠ 0`. -/
lemma vTwist_vTwistInv (m : ℤ) {q : Quaternion ℝ} (hq : q ≠ 0) (y : Quaternion ℝ) :
    vTwist m q (vTwistInv m q y) = y := by
  have h1 : q ^ m * q ^ (-m) = 1 := by
    rw [← zpow_add₀ hq, add_neg_cancel, zpow_zero]
  simp only [vTwist, vTwistInv]
  rw [mul_assoc (q ^ (-m)) y q, ← mul_assoc (q ^ m) (q ^ (-m)) (y * q), h1, one_mul,
    mul_assoc, mul_inv_cancel₀ hq, mul_one]

/-- `vTwistInv m q` and `vTwist m q` are mutually inverse on `ℍ`, for `q ≠ 0`. -/
lemma vTwistInv_vTwistInv' (m : ℤ) {q : Quaternion ℝ} (hq : q ≠ 0) (y : Quaternion ℝ) :
    vTwistInv m q (vTwist m q y) = y := by
  have h1 : q ^ (-m) * q ^ m = 1 := by
    rw [← zpow_add₀ hq, neg_add_cancel, zpow_zero]
  simp only [vTwist, vTwistInv]
  rw [mul_assoc (q ^ m) y q⁻¹, ← mul_assoc (q ^ (-m)) (q ^ m) (y * q⁻¹), h1, one_mul,
    mul_assoc, inv_mul_cancel₀ hq, mul_one]

/-- `vMapInv k` is a two-sided inverse of `vMap k` on the gluing region `{x ≠ 0} × ℍ`. -/
theorem vMap_inv (k : ℤ) {p : Submission.Milnor.MSpace8} (hp : p.1 ≠ 0) :
    Submission.Milnor.vMapInv k (Submission.Milnor.vMap k p) = p ∧
      Submission.Milnor.vMap k (Submission.Milnor.vMapInv k p) = p := by
  have hq : ((unitDir p.1 : QS3) : Quaternion ℝ) ≠ 0 := Work.Quaternion.coe_ne_zero _
  constructor
  · rw [vMapInv, vMap]
    refine Prod.ext ?_ ?_
    · exact invBase_invBase hp
    · rw [unitDir_invBase p.1 hp]
      exact vTwistInv_vTwistInv' (-k) hq p.2
  · rw [vMap, vMapInv]
    refine Prod.ext ?_ ?_
    · exact invBase_invBase hp
    · rw [unitDir_invBase p.1 hp]
      exact vTwist_vTwistInv (-k) hq p.2

end Work.Milnor
