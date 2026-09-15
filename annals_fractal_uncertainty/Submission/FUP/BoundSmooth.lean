import Submission.FUP.LpNorms

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The Kohn--Morrey/Cauchy--Schwarz estimate in `L²(μ_φ)` form

`norm_formPair_sq_le` (`Submission.FUP.HormanderBound`) is the abstract estimate
`‖formPair η u φ‖² ≤ etaKapNorm η φ κ · (dbarNormSq u φ + adjNormSq u φ)` for smooth compactly
supported forms.  This module rewrites it in the `L²(μ_φ)` language of
`Submission.FUP.LpNorms`, i.e. as

`‖⟪u, η⟫‖² ≤ etaKapNorm η φ κ · (‖∂̄₂ u‖² + ‖ϑ_φ u‖²)`,

which is the `hbound` input of the abstract existence theorem
`Commons.Analysis.InnerProductSpace.LinearPMap.exists_solution_of_bound`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The pointwise Hermitian-Hessian positivity condition. -/
def HessBound (φ : FormDu d → ℝ) (κ : FormDu d → ℝ) : Prop :=
  ∀ z (w : Fin d → ℂ), 4 * (κ z * ∑ j, ‖w j‖ ^ 2)
    ≤ (iteratedFDeriv ℝ 2 φ z) ![w, w]
      + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w]

/-- **The Kohn--Morrey + Cauchy--Schwarz estimate for smooth compactly supported forms**, in the
`L²(μ_φ)` language. -/
theorem norm_inner_liftForm_sq_le {φ : FormDu d → ℝ} {κ : FormDu d → ℝ}
    {η x : FormDu d → (Fin d → ℂ)}
    (hφ : ContDiff ℝ 2 φ) (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z)
    (hηc : ∀ j, Continuous (fun z => η z j))
    (hηs : ∀ j, HasCompactSupport (fun z => η z j))
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
  have hFNScontB : Continuous (formNormSq η) :=
    continuous_finsetSum (Finset.univ : Finset (Fin d)) (fun j _ => (hηc j).norm.pow 2)
  have hFNSnnB : ∀ z, 0 ≤ formNormSq η z := fun z => by
    rw [formNormSq]; exact Finset.sum_nonneg fun j _ => by positivity
  have hFNScs : HasCompactSupport (formNormSq η) := by
    have h1 : ∀ j, HasCompactSupport (fun z => ‖η z j‖ ^ 2) := fun j =>
      (hηs j).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
    have h := HasCompactSupport.finset_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun j z => ‖η z j‖ ^ 2) (fun j _ => h1 j)
    have heq : (∑ j : Fin d, fun z => ‖η z j‖ ^ 2) = formNormSq η := by
      funext z
      exact Finset.sum_apply z Finset.univ _
    rwa [heq] at h
  have hηint : ∫⁻ z, ENNReal.ofReal (formNormSq η z * Real.exp (-(φ z)) / κ z) < ⊤ := by
    have hcont : Continuous (fun z => formNormSq η z * Real.exp (-(φ z)) / κ z) :=
      (hFNScontB.mul (Real.continuous_exp.comp hφ.continuous.neg)).div hκc
        fun z => (hκpos z).ne'
    have hcs : HasCompactSupport (fun z => formNormSq η z * Real.exp (-(φ z)) / κ z) := by
      refine hFNScs.mono' fun z hz => ?_
      have hne : formNormSq η z ≠ 0 := fun h0 => hz (by simp [h0])
      exact subset_tsupport _ hne
    have hint : Integrable (fun z => formNormSq η z * Real.exp (-(φ z)) / κ z)
        (volume : Measure (Fin d → ℂ)) :=
      hcont.integrable_of_hasCompactSupport (μ := volume) hcs
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z =>
      div_nonneg (mul_nonneg (hFNSnnB z) (Real.exp_nonneg _)) (hκpos z).le)]
    exact ENNReal.ofReal_lt_top
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
