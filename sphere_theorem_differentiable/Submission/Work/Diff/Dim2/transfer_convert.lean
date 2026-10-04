import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.Azim
import Submission.Work.Diff.Dim2.azimuth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

theorem transfer_convert
    {s : ℝ} {ρ : ℝ → ℝ} {κ : ℝ → EuclideanSpace ℝ (Fin 2)}
    {ux vx : EuclideanSpace ℝ (Fin 2)}
    (hcos : Real.cos (ρ (Work.Diff.Dim2.argE ux)) = (κ (Work.Diff.Dim2.argE ux)) 0)
    (hsin : Real.sin (ρ (Work.Diff.Dim2.argE ux)) = s * (κ (Work.Diff.Dim2.argE ux)) 1)
    (hκ : κ (Work.Diff.Dim2.argE ux) = vx)
    (hux : ‖ux‖ = 1) :
    Work.Diff.Dim2.reflE s vx
      = Work.Diff.Dim2.rotE (ρ (Work.Diff.Dim2.argE ux) - Work.Diff.Dim2.argE ux) ux := by
  -- Both sides, pushed through the identification `toC : ℝ² ≃ ℂ`, equal
  -- `⟨cos (ρ (argE ux)), sin (ρ (argE ux))⟩`.
  have huxc : toC ux = Complex.exp ((argE ux : ℂ) * Complex.I) := by
    calc toC ux = toC (circPt (argE ux)) := by rw [circPt_argE hux]
      _ = Complex.exp ((argE ux : ℂ) * Complex.I) := toC_circPt_exp _
  have hL : toC (reflE s vx)
      = (⟨Real.cos (ρ (argE ux)), Real.sin (ρ (argE ux))⟩ : ℂ) := by
    simp only [reflE, toC_ofC]
    apply Complex.ext
    · show (toC vx).re = Real.cos (ρ (argE ux))
      rw [show (toC vx).re = vx 0 from rfl, ← hκ]
      exact hcos.symm
    · show s * (toC vx).im = Real.sin (ρ (argE ux))
      rw [show (toC vx).im = vx 1 from rfl, ← hκ]
      exact hsin.symm
  have hR : toC (rotE (ρ (argE ux) - argE ux) ux)
      = (⟨Real.cos (ρ (argE ux)), Real.sin (ρ (argE ux))⟩ : ℂ) := by
    simp only [rotE, toC_ofC]
    rw [huxc, ← Complex.exp_add]
    have harg : ((ρ (argE ux) - argE ux : ℝ) : ℂ) * Complex.I + (argE ux : ℂ) * Complex.I
        = ((ρ (argE ux) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_mul_I]
    apply Complex.ext <;>
      simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  exact toC_injective (hL.trans hR.symm)

end Work.Diff.Dim2
