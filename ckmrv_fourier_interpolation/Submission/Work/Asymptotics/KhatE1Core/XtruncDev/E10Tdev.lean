import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24XtruncDefs
import Submission.Work.Asymptotics.KhatE1Core.DSm1RowBound
import Submission.Work.Asymptotics.KhatE1Core.StripAtoms
import Submission.Work.Asymptotics.KhatE1.ZAtomsSecondOrder

namespace Work.Asymptotics.KhatE1Core.XtruncDev

open UpperHalfPlane

noncomputable section

/-- `E₁₀(z) - E10T z = O(‖q(z)‖³)` on `{1 ≤ Im z}`: `E10T` is the `q²`-truncation of the
weight-ten Eisenstein series `E₁₀ = E₄E₆`. -/
theorem E10Fun_sub_E10T_bigO :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.E10Fun z - E10T z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, hf⟩ := Work.Asymptotics.KhatE1.E4E6ThirdOrder
  refine ⟨C, hC, fun z hz => ?_⟩
  have h : ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1
        + 264 * Work.Kernels.qParamFun z + 135432 * Work.Kernels.qParamFun z ^ 2‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := hf z hz
  have hconv : Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1
        + 264 * Work.Kernels.qParamFun z + 135432 * Work.Kernels.qParamFun z ^ 2
      = Work.Kernels.E10Fun z - E10T z := by
    rw [show Work.Kernels.E10Fun z = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z from rfl,
        show E10T z = 1 - 264 * Work.Kernels.qParamFun z
          - 135432 * (Work.Kernels.qParamFun z) ^ 2 from rfl]
    ring
  rw [hconv] at h
  exact h

theorem E10Tdev :
    Work.Asymptotics.KhatE1Core.Bound2
      (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
        Work.Kernels.E10Fun z - Work.Asymptotics.KhatE1Core.E10T z) 0 3 := by
  obtain ⟨C, hC, hf⟩ := E10Fun_sub_E10T_bigO
  refine ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hzi : (1 : ℝ) ≤ z.im := by
    have h1 : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hF
    rw [hzim]; linarith
  have h := hf z hzi
  simpa [zpow_zero, Real.rpow_zero] using h

end

end Work.Asymptotics.KhatE1Core.XtruncDev
