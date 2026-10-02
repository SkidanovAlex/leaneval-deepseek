import Mathlib
import Submission.Work.Tubular.OnePointModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Tubular

/-- The Pontryagin–Thom blow-up coefficient `ε * (ε - ‖p‖)⁻¹` at a normal vector of norm at most
`ε/2` lies in the interval `[1,2]`. -/
theorem blowCoeff_bounds {V : Work.ThomBordism.Man8} {N : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V N} {ε : ℝ}
    (hε : 0 < ε) {p : Work.Tubular.NormalTotal E} (h : Work.Tubular.normalNorm E p ≤ ε / 2) :
    1 ≤ Work.Tubular.blowCoeff E ε p ∧ Work.Tubular.blowCoeff E ε p ≤ 2 := by
  have ht : 0 ≤ normalNorm E p := normalNorm_nonneg E p
  have hd : 0 < ε - normalNorm E p := by linarith
  have hlow : ε / 2 ≤ ε - normalNorm E p := by linarith
  have hkey : blowCoeff E ε p = ε / (ε - normalNorm E p) := by
    rw [blowCoeff, div_eq_mul_inv]
  rw [hkey]
  constructor
  · rw [le_div_iff₀ hd]
    linarith
  · rw [div_le_iff₀ hd]
    linarith

end Work.Tubular
