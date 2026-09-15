import Submission.FUP.BoundSmooth

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The Kohn--Morrey estimate in `L²(μ_φ)` form, without compact support of the data

`BoundSmooth.norm_inner_liftForm_sq_le` proves the `L²(μ_φ)`-form of the Kohn--Morrey/Cauchy--Schwarz
estimate for a *compactly supported* form `η`.  `HormanderStatementPointwise` only provides a
finiteness hypothesis `∫⁻ ofReal (|η|²e^{-φ}/κ) < ⊤`, so we record here the version of the estimate
with that weaker hypothesis, obtained from the already general `HormanderBound.norm_formPair_sq_le`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- **The Kohn--Morrey + Cauchy--Schwarz estimate for smooth compactly supported forms**, in the
`L²(μ_φ)` language, with the finiteness hypothesis on the data `η` instead of compact support. -/
theorem norm_inner_liftForm_sq_le' {φ : FormDu d → ℝ} {κ : FormDu d → ℝ}
    {η x : FormDu d → (Fin d → ℂ)}
    (hφ : ContDiff ℝ 2 φ) (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z)
    (hηc : ∀ j, Continuous (fun z => η z j))
    (hηint : ∫⁻ z, ENNReal.ofReal (formNormSq η z * Real.exp (-(φ z)) / κ z) < ⊤)
    (hx : ∀ j, ContDiff ℝ 2 (fComp x j))
    (hsx : ∀ j, HasCompactSupport (fComp x j))
    (hhess : HessBound φ κ)
    (hxm : MemLp (liftForm x) 2 (wtMeasure φ))
    (hηm : MemLp (liftForm η) 2 (wtMeasure φ))
    (hsm : MemLp (liftForm2 (dbarFormFun2 x)) 2 (wtMeasure φ))
    (hθm : MemLp (dbarAdjoint φ x) 2 (wtMeasure φ)) :
    ‖inner ℂ (hxm.toLp (liftForm x)) (hηm.toLp (liftForm η))‖ ^ 2
      ≤ etaKapNorm η φ κ * (‖hsm.toLp (liftForm2 (dbarFormFun2 x))‖ ^ 2
          + ‖hθm.toLp (dbarAdjoint φ x)‖ ^ 2) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have h := norm_formPair_sq_le (η := η) (u := x) hφ hκc hκpos hηc hηint hx hsx hhess
  rw [formPair_eq_inner (φ := φ) hφ1 hxm hηm,
      dbarNormSq_eq (φ := φ) hφ1 hsm, adjNormSq_eq (φ := φ) hφ1 hθm] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have h1 : (0:ℝ) ≤ ‖hsm.toLp (liftForm2 (dbarFormFun2 x))‖ ^ 2 := by positivity
    linarith
  · rw [etaKapNorm]
    refine integral_nonneg fun z => div_nonneg (mul_nonneg ?_ (Real.exp_nonneg _)) (hκpos z).le
    rw [formNormSq]
    exact Finset.sum_nonneg fun j _ => by positivity

end Submission.FUP
