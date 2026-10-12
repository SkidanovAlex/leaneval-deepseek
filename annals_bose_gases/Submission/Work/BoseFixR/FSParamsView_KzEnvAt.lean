import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

theorem FSParamsView_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {E : Work.BoseB7.Q3Env Mode} (h : Work.BoseB7.FSParamsView E) {ρ : ℝ}
    (hρ : 0 < ρ) (hℓ : E.ell ≠ 0) (hclose : |ρ - E.mu| ≤ E.mu / 2) :
    Nonempty (Work.BoseB7.FSParamsView (Work.BoseFixR.KzEnvAt E ρ)) := by
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E h
  have hpos : 0 < ρ * E.ell ^ 3 := mul_pos hρ (pow_pos hell 3)
  refine ⟨{ h with z_ne := ?_, rho_close := ?_ }⟩
  · show Real.sqrt (ρ * E.ell ^ 3) ≠ 0
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  · show |Real.sqrt (ρ * E.ell ^ 3) ^ 2 / E.ell ^ 3 - E.mu| ≤ E.mu / 2
    rw [Real.sq_sqrt hpos.le, mul_div_cancel_right₀ ρ (pow_ne_zero 3 (ne_of_gt hell))]
    exact hclose

end Work.BoseFixR
