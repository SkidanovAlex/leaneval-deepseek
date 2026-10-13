/-
# `exists_cptQ_approx` — the convergence of the error, unconditionally

This module instantiates the conditional estimate `EstTendsto.tendsto_HkSq_err` with

* `Est.lintegral_momentFactor_le` (finiteness/smallness of the moment factor),
* `EstAlt.hkMem_err` (`ℋᵏ`-membership of the error),
* `Est.rhoProf_ae_le` (finiteness of the angular profile `rhoProf`).
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstTendsto
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstHkMem
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.rhoProf_ae_le
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.lintegral_momentFactor_le
import Submission.Work.FTS.PhiStar.ThetaTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `ℋᵏ`-norm of the error of the approximation tends to `0`.** -/
theorem tendsto_HkSq_err_final (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (htr : Work.FTS.PhiStar.ThetaTraces α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α k (err n F)) Filter.atTop (nhds 0) := by
  obtain ⟨Cm, hCm, hmom⟩ :=
    Work.FTS.PhiStar.Honesty.CptApp.Est.lintegral_momentFactor_le (k := k) hsm hF hFs
  obtain ⟨RPb, hRPb, hRPbd⟩ := Work.FTS.PhiStar.Honesty.CptApp.Est.rhoProf_ae_le k α
  have hvolI : (volume : Measure ℝ) Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    norm_num
  have hRP : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))
      ≤ ENNReal.ofReal (RPb * (Real.pi / 2)) := by
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal RPb :=
          lintegral_mono_ae (hRPbd.mono fun θ h => ENNReal.ofReal_le_ofReal h)
      _ = ENNReal.ofReal RPb * volume Work.Spaces.Iθ := by
          rw [lintegral_const]
          congr 1
          exact Measure.restrict_apply_univ Work.Spaces.Iθ
      _ = ENNReal.ofReal RPb * ENNReal.ofReal (Real.pi / 2) := by rw [hvolI]
      _ = ENNReal.ofReal (RPb * (Real.pi / 2)) := (ENNReal.ofReal_mul hRPb).symm
  refine tendsto_HkSq_err k α hα hα1 hsm hF htr hFs hCm
    (mul_nonneg hRPb (by positivity)) hmom ?_ hRP
  intro n hn
  exact Work.FTS.PhiStar.Honesty.CptApp.EstAlt.hkMem_err k α hα hα1 F n hn hsm hF hFs htr

end Work.FTS.PhiStar.Honesty.CptApp
