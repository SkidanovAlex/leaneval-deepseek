import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24XtruncDefs
import Submission.Work.Asymptotics.KhatE1Core.DSm1RowBound
import Submission.Work.Asymptotics.KhatE1Core.invDeltaSecondOrder

namespace Work.Asymptotics.KhatE1Core.XtruncDev

/-!
# The deviation of the truncated `1/Δ` from `1/Δ`

The truncated atom `invDeltaT z = (q z)⁻¹ + 24 + 324 q z` (with `q = qParamFun`) is the
second-order truncation of `1/Δ(z) = q⁻¹ + 24 + 324 q + O(q²)`.  This file records that the
truncation tail is `O(‖q(z)‖²)` on the funnel strip, in the two-exponent `Bound2` calculus of
`KhatE1Core.DSm1RowBound` (trivial `‖q(τ)‖`- and scale-exponents `0`, `(1+t)`-exponent `0`, and
`‖q(z)‖`-exponent `2`).

The input is the already-proved second-order cusp expansion
`Work.Asymptotics.KhatE1Core.invDeltaSecondOrder`,
`‖1/Δ(z) - ((Ept z)⁻¹² + 24 + 324 q(z))‖ ≤ C ‖Ept z‖⁴`, together with `q(z) = Ept z²`
(so `‖Ept z‖⁴ = ‖q(z)‖²`).
-/

/-- `q(z) = Ept z ^ 2`, so that `(q(z))⁻¹ = (Ept z)⁻¹ ^ 2`. -/
lemma qParamFun_eq_Ept_sq_local (z : UpperHalfPlane) :
    Work.Kernels.qParamFun z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
  congr 1
  ring

theorem dinvDeltaTdev :
    Work.Asymptotics.KhatE1Core.Bound2
      (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
        (Work.Kernels.DeltaFun z)⁻¹ - Work.Asymptotics.KhatE1Core.invDeltaT z) 0 2 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.KhatE1Core.invDeltaSecondOrder
  refine ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  dsimp only
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  have h := hb z hz1'
  have hEinv : (Work.Kernels.qParamFun z)⁻¹ = (Work.Residues.Ept z)⁻¹ ^ 2 := by
    rw [qParamFun_eq_Ept_sq_local z, inv_pow]
  have hEq : Work.Asymptotics.KhatE1Core.invDeltaT z
      = (Work.Residues.Ept z)⁻¹ ^ 2 + 24 + 324 * Work.Kernels.qParamFun z := by
    simp only [Work.Asymptotics.KhatE1Core.invDeltaT, Work.Asymptotics.KhatE1Core.Tq]
    rw [hEinv]
  rw [hEq]
  have h4 : ‖Work.Residues.Ept z‖ ^ 4 = ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [qParamFun_eq_Ept_sq_local z, norm_pow]; ring
  calc ‖(Work.Kernels.DeltaFun z)⁻¹
          - ((Work.Residues.Ept z)⁻¹ ^ 2 + 24 + 324 * Work.Kernels.qParamFun z)‖
      ≤ C * ‖Work.Residues.Ept z‖ ^ 4 := h
    _ = C * ‖Work.Kernels.qParamFun z‖ ^ 2 := by rw [h4]
    _ = C * (‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) * (Work.Kernels.scale τ) ^ (0 : ℝ)
          * (1 + t) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun z‖ ^ (2 : ℤ)) := by
        simp only [zpow_ofNat, Real.rpow_zero, pow_zero, mul_one, one_mul]

end Work.Asymptotics.KhatE1Core.XtruncDev
