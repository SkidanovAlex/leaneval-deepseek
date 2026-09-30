import Mathlib
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.basisRed_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

/-- The dilation by `t > 0` of the unit ball `{y | F y ≤ 1}` of a nonnegative, absolutely
homogeneous function `F` is the ball `{x | F x ≤ t}` of radius `t`.  (Stated with
`Work.BW.smulSet` to avoid the `Pointwise` scoped notation.) -/
theorem smulSet_unitBall_eq {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) {t : ℝ}
    (ht : 0 < t) :
    Work.BW.smulSet t {y : Fin n → ℝ | F y ≤ 1} = {x : Fin n → ℝ | F x ≤ t} := by
  ext x
  rw [Work.BW.mem_smulSet]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change F (t • y) ≤ t
    rw [hF.smul, abs_of_pos ht]
    have hy' : F y ≤ 1 := hy
    nlinarith [hy', le_of_lt ht, hF.nonneg y]
  · intro hx
    refine ⟨t⁻¹ • x, ?_, ?_⟩
    · change F (t⁻¹ • x) ≤ 1
      rw [hF.smul, abs_of_pos (inv_pos.mpr ht), inv_mul_le_iff₀ ht]
      simpa using hx
    · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]

end Work.BW.Minkowski2
