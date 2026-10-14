import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_vBound
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Defs
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_kDerivCLM_sub_le_of_two_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

open Work.StabilityFar.Decay (kDerivCLM)

/-- **Pointwise Lipschitz estimate for the Biot–Savart derivative kernel away from two points.**
If `0 < δ`, `‖x - y‖ ≤ δ` and `2δ ≤ ‖a - y‖`, then both `x - a` and `y - a` have norm at least
`‖a - y‖ / 2`, so `norm_kDerivCLM_sub_le` at `m = ‖a - y‖ / 2` gives the degree-`-4` bound
`‖kDerivCLM (x-a) - kDerivCLM (y-a)‖ ≤ 64/(‖a-y‖/2)^4 · ‖x-y‖ ≤ 1024 δ / ‖a-y‖^4`. -/
theorem norm_kDerivCLM_sub_le_of_two_mul_le {δ : ℝ} (hδ : 0 < δ) {x y a : Work.LWP.R3}
    (hxy : ‖x - y‖ ≤ δ) (ha : 2 * δ ≤ ‖a - y‖) :
    ‖Work.StabilityFar.Decay.kDerivCLM (x - a) - Work.StabilityFar.Decay.kDerivCLM (y - a)‖
      ≤ 1024 * δ / ‖a - y‖ ^ 4 := by
  have hr : 0 < ‖a - y‖ := by linarith
  have hm : 0 < ‖a - y‖ / 2 := by linarith
  have hle : ‖x - y‖ ≤ ‖a - y‖ / 2 := by linarith
  -- `x - a` is far from the origin: `‖a - y‖ ≤ ‖x - a‖ + ‖x - y‖`.
  have hxb : ‖a - y‖ / 2 ≤ ‖x - a‖ := by
    have h : ‖a - y‖ ≤ ‖x - a‖ + ‖x - y‖ := by
      have h1 : a - y = (a - x) + (x - y) := by abel
      rw [h1]
      calc ‖(a - x) + (x - y)‖ ≤ ‖a - x‖ + ‖x - y‖ := norm_add_le _ _
        _ = ‖x - a‖ + ‖x - y‖ := by rw [norm_sub_rev a x]
    linarith
  -- `y - a` itself has norm at least `‖a - y‖ / 2`.
  have hyb : ‖a - y‖ / 2 ≤ ‖y - a‖ := by
    rw [norm_sub_rev y a]
    linarith
  have h := Work.StabilityFar.Decay.norm_kDerivCLM_sub_le (x - a) (y - a) (‖a - y‖ / 2) hm hxb hyb
  have hsub : (x - a) - (y - a) = x - y := by abel
  rw [hsub] at h
  have hconst : 64 / (‖a - y‖ / 2) ^ 4 = 1024 / ‖a - y‖ ^ 4 := by
    rw [div_pow]
    field_simp
    ring
  rw [hconst] at h
  calc ‖kDerivCLM (x - a) - kDerivCLM (y - a)‖
      ≤ 1024 / ‖a - y‖ ^ 4 * ‖x - y‖ := h
    _ ≤ 1024 / ‖a - y‖ ^ 4 * δ := by gcongr
    _ = 1024 * δ / ‖a - y‖ ^ 4 := by ring

end Work.CoreResiduals.BiotSavart.Bundle
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.TaylorDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-- The second-order Taylor residual of the Newtonian kernel:
`resid h y = kf (y + h) - kf y - kDerivCLM y h`. -/
noncomputable def resid (h y : Work.LWP.R3) : Work.LWP.R3 :=
  kf (y + h) - kf y - kDerivCLM y h

/-- The Biot–Savart Taylor residual seen at the shifted argument: `kf (x+h-a) - kf (x-a)
- kDerivCLM (x-a) h = resid h (x - a)`. -/
theorem resid_shift (x h a : Work.LWP.R3) :
    kf (x + h - a) - kf (x - a) - kDerivCLM (x - a) h = resid h (x - a) := by
  rw [resid, show x + h - a = (x - a) + h by abel]

/-- `(aⁿ)⁻¹ = a^{-n}` for `a ≥ 0`. -/
lemma inv_natPow_eq_rpow_neg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (a ^ n)⁻¹ = a ^ (-(n:ℝ)) := by
  rw [← Real.rpow_natCast a n]
  exact (Real.rpow_neg ha n).symm

/-- The norm of the Newtonian kernel: `‖kf b‖ = ‖b‖⁻²`. -/
theorem norm_kf_eq (b : Work.LWP.R3) : ‖kf b‖ = ‖b‖ ^ (-2 : ℝ) := by
  rw [Work.StabilityFar.Decay.kf, norm_smul, Real.norm_of_nonneg (by positivity)]
  rcases eq_or_lt_of_le (norm_nonneg b) with h | h
  · rw [← h]; simp
  · have h2 : ((‖b‖ ^ (3:ℕ))⁻¹) * ‖b‖ = (‖b‖ ^ (2:ℕ))⁻¹ := by
      rw [show ‖b‖ ^ (3:ℕ) = ‖b‖ ^ (2:ℕ) * ‖b‖ by ring, mul_inv]
      field_simp
    rw [h2, Real.rpow_neg (norm_nonneg b) 2]
    congr 1
    exact (Real.rpow_natCast ‖b‖ 2).symm

/-- `kDerivCLM` vanishes at the origin. -/
theorem kDerivCLM_zero : kDerivCLM (0 : Work.LWP.R3) = 0 := by
  ext v
  simp [Work.StabilityFar.Decay.kDerivCLM]

/-- **Crude pointwise bound for the Taylor residual**: from the triangle inequality and the
operator-norm bound `‖kDerivCLM y‖ ≤ 4/‖y‖³`.  (For `y = 0` both sides are `‖h‖⁻²`.) -/
theorem norm_resid_le_crude (h y : Work.LWP.R3) :
    ‖resid h y‖ ≤
      ‖y + h‖ ^ (-2 : ℝ) + ‖y‖ ^ (-2 : ℝ) + 4 * ‖y‖ ^ (-3 : ℝ) * ‖h‖ := by
  have h1 := norm_kf_eq (y + h)
  have h2 := norm_kf_eq y
  have h4 : ‖kDerivCLM y h‖ ≤ 4 * ‖y‖ ^ (-3 : ℝ) * ‖h‖ := by
    rcases eq_or_lt_of_le (norm_nonneg y) with hh | hh
    · have hy0 : y = 0 := by rw [← norm_eq_zero]; exact hh.symm
      rw [hy0, kDerivCLM_zero, zero_apply, norm_zero]
      simp
    · have hb := Work.StabilityFar.Decay.norm_kDerivCLM_le y ‖y‖ hh le_rfl
      have h5 : (4:ℝ)/‖y‖^3 = 4 * ‖y‖^(-3:ℝ) := by
        rw [div_eq_mul_inv, inv_natPow_eq_rpow_neg ‖y‖ (norm_nonneg y) 3]
        congr 1
      calc ‖kDerivCLM y h‖ ≤ ‖kDerivCLM y‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (4 / ‖y‖ ^ 3) * ‖h‖ := by gcongr
        _ = 4 * ‖y‖ ^ (-3:ℝ) * ‖h‖ := by rw [h5]
  have hb := norm_sub_le (kf (y + h)) (kf y)
  have hc := norm_sub_le (kf (y + h) - kf y) (kDerivCLM y h)
  rw [resid]
  linarith [h1, h2, h4, hb, hc]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.BSSwirl.integrable_inv_cube_smulRight =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

open MeasureTheory
open scoped Topology ENNReal

namespace Work.FTS.BSSwirl

/-- **Pointwise domination of the `potDeriv` kernel.**  The tensor `(‖x-y‖³)⁻¹ • innerSL(y-x) ⊗ ω y`
is bounded in norm by the (integrable) weight `M ‖x-y‖⁻²`, but only on the support ball `B(0,R)`;
off the support the vorticity vanishes and so does the integrand.  The algebraic content is
`(a³)⁻¹ · a = (a²)⁻¹`, valid for every real `a` including `a = 0` (both sides are `0` there). -/
theorem norm_inv_cube_smulRight_le {ω : R3 → R3} {M R : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) (x : R3) :
    ∀ y, ‖((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • (innerSL ℝ (y - x)).smulRight (ω y)‖
      ≤ (Metric.closedBall (0:R3) R).indicator (fun y => M * ((‖x - y‖ ^ (2:ℕ))⁻¹)) y := by
  have haux : ∀ a : ℝ, (a^3)⁻¹ * (a * M) = M * ((a^2)⁻¹) := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · field_simp
  intro y
  by_cases hw : ω y = 0
  · have h0 : (innerSL ℝ (y - x)).smulRight (ω y) = 0 := by rw [hw]; simp
    rw [h0, smul_zero, norm_zero]
    by_cases hy : y ∈ Metric.closedBall (0:R3) R
    · rw [Set.indicator_of_mem hy]
      exact mul_nonneg hM (inv_nonneg.mpr (by positivity))
    · rw [Set.indicator_of_notMem hy]
  · have hy : y ∈ Metric.closedBall (0:R3) R := hsupp y hw
    rw [Set.indicator_of_mem hy]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    calc (‖x - y‖ ^ (3:ℕ))⁻¹ * (‖y - x‖ * ‖ω y‖)
        ≤ (‖x - y‖ ^ (3:ℕ))⁻¹ * (‖y - x‖ * M) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hbdd y) (norm_nonneg _)
      _ = M * ((‖x - y‖ ^ (2:ℕ))⁻¹) := by
          rw [norm_sub_rev y x]
          exact haux ‖x - y‖

theorem integrable_inv_cube_smulRight {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} {M R : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (x : Work.FTS.BSSwirl.R3) :
    MeasureTheory.Integrable
      (fun y : Work.FTS.BSSwirl.R3 =>
        ((‖x - y‖ ^ (3 : ℕ))⁻¹ : ℝ) • (innerSL ℝ (y - x)).smulRight (ω y))
      MeasureTheory.volume := by
  refine Integrable.mono' (Work.StabilityFar.Decay.integrable_indicator_inv_sq (R := R) x hM) ?_ ?_
  · first
    | exact ((((continuous_const.sub continuous_id).norm.pow 3).measurable.inv).aestronglyMeasurable).smul
            (Continuous.comp_aestronglyMeasurable₂ (ContinuousLinearMap.smulRightL ℝ Work.FTS.BSSwirl.R3 Work.FTS.BSSwirl.R3).continuous₂
              (((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable) hmeas)
    | measurability
  · filter_upwards with y
    exact norm_inv_cube_smulRight_le hM hbdd hsupp x y

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Fstar_eq_integral_FstarInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.FstarSmooth

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false




end Work.FTS.EllipticEst.Cert.FstarSmooth
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarSmoothOfSol =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false

/-! ## Two independent pieces of the route

`FstarSmoothOfSol` is assembled from three ingredients, of which the first two are proved
here (they are independent of each other) and the third is the parametric-integral lemma
`Work.FTS.EllipticEst.contDiffOn_infty_integral_Itheta_Ioi_neg_one` of `Fstar_contDiffOn.lean`:

* `FstarInt_smoothNbhdOfSol`: the smooth integrand `FstarInt α Ψ` is `SmoothNbhd` whenever
  `Ψ` is — it is a sum/product of `∂_z^2Ψ`, `∂_zΨ`, `∂_θ^2Ψ`, `∂_θΨ`, `Ψ`, polynomials in `z`
  and functions of `θ` alone;
* `Fstar_eq_integral_FstarIntOfSol`: on the open quadrant `F = bslOp α Ψ`, so multiplying by
  the angular weight turns the integrand into `FstarInt α Ψ`
  (`Cert.FstarSmooth.bslOp_mul_sinCos2_eq`); at the two endpoints `θ = 0, π/2` the weight
  `sinθcos²θ` vanishes, so the two integrands agree on *all* of `Iθ` and the `θ`-integrals
  agree on the nose (no `a.e.` discussion needed). -/




end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.SlicePsiNear =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.Honest

set_option autoImplicit false


set_option autoImplicit false

local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

private lemma pi_div_four_pos : (0 : ℝ) < Real.pi / 4 := by positivity

private lemma sig_pos_of_mem_Ioo_pi4 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) : 0 < σ θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact Real.rpow_pos_of_pos hsin _

private lemma sig_nonneg_of_mem_Icc_pi4 {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 4)) : 0 ≤ σ θ :=
  Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

private lemma integrableOn_sig_pi4 : IntegrableOn σ (Set.Ioo 0 (Real.pi / 4)) := by
  refine (Work.FTS.EllipticEst.TanTheta.integrableOn_sin_two_rpow_neg (η := Work.Spaces.eta)
    Work.Spaces.eta_lt_one).mono_set ?_
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩

/-- **The interpolation bound for the first derivative.** -/
private lemma deriv_sq_le_of_mem (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {A θ : ℝ} (hA0 : 0 < A) (hAle : A ≤ Real.pi / 4) (hθ : θ ∈ Set.Ioo 0 A)
    (hX' : IntegrableOn (fun z => (deriv (deriv u) z) ^ 2 * σ z) (Set.Ioo 0 A)) :
    (deriv u θ) ^ 2 ≤ 2 * (deriv u A) ^ 2
      + 2 * ((2 * A) ^ (Work.Spaces.eta) * A)
        * (∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z) := by
  have hθle : θ ≤ A := le_of_lt hθ.2
  have hAle2 : A < Real.pi / 2 := by linarith [hAle, Real.pi_pos]
  have huIoc : Set.uIcc θ A ⊆ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.uIcc_of_le hθle]
    intro x hx
    exact ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hAle2⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hderiv : ∀ x ∈ Set.uIcc θ A, DifferentiableAt ℝ (deriv u) x := by
    intro x hx
    exact (hd1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds (huIoc hx))
  have hint : IntervalIntegrable (deriv (deriv u)) volume θ A := by
    have hcont : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
      hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)
    exact (hcont.mono huIoc).intervalIntegrable
  have hFTC : (∫ x in θ..A, deriv (deriv u) x) = deriv u A - deriv u θ :=
    intervalIntegral.integral_deriv_eq_sub hderiv hint
  have hZint : IntegrableOn (fun z => (deriv (deriv u) z) ^ 2 * σ z) (Set.Ioc θ A) :=
    (hX'.mono_set (fun z hz => ⟨lt_trans hθ.1 hz.1, hz.2⟩)).congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Ioc (a := θ) (b := A)).symm
  have hcontSin : ContinuousOn (fun z : ℝ => (Real.sin (2 * z)) ^ (Work.Spaces.eta))
      (Set.Icc θ A) := by
    refine ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const ?_
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hθ.1 hz.1
    have h2z0 : (0 : ℝ) < 2 * z := by linarith
    have h2zp : 2 * z < Real.pi := by linarith [hz.2, hAle2, Real.pi_pos]
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2z0 h2zp))
  have hWint : IntegrableOn (fun z => (Real.sin (2 * z)) ^ (Work.Spaces.eta)) (Set.Ioc θ A) :=
    (hcontSin.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hcontV : ContinuousOn (deriv (deriv u)) (Set.Icc θ A) := by
    have h := (hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono huIoc
    rwa [Set.uIcc_of_le hθle] at h
  have hCint : IntegrableOn (fun z => |deriv (deriv u) z|) (Set.Ioc θ A) :=
    (hcontV.abs.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hpt : ∀ z ∈ Set.Ioc θ A,
      |(|deriv (deriv u) z|)| ≤ Real.sqrt ((deriv (deriv u) z) ^ 2 * σ z)
        * Real.sqrt ((Real.sin (2 * z)) ^ (Work.Spaces.eta)) := by
    intro z hz
    have hs : 0 < Real.sin (2 * z) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hz.1, hθ.1]) (by linarith [hz.2, hAle2])
    have hsq : Real.sqrt ((deriv (deriv u) z) ^ 2 * σ z)
        = |deriv (deriv u) z| * Real.sqrt (σ z) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    have hσnn : 0 ≤ σ z := le_of_lt (Real.rpow_pos_of_pos hs _)
    have hone : Real.sqrt (σ z) * Real.sqrt ((Real.sin (2 * z)) ^ (Work.Spaces.eta)) = 1 := by
      rw [← Real.sqrt_mul (x := σ z) hσnn]
      have h1 : σ z * (Real.sin (2 * z)) ^ (Work.Spaces.eta) = 1 := by
        change (Real.sin (2 * z)) ^ (-(Work.Spaces.eta)) * (Real.sin (2 * z)) ^ (Work.Spaces.eta)
          = 1
        rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
      rw [h1, Real.sqrt_one]
    rw [abs_abs, hsq, mul_assoc, hone, mul_one]
  have hcs := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt hZint hWint hCint
    (fun z hz => mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem_Icc_pi4
      ⟨le_of_lt (lt_trans hθ.1 hz.1), le_trans hz.2 hAle⟩))
    (fun z hz => Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hz.1, hθ.1])
      (by linarith [hz.2, hAle2, Real.pi_pos])) _)
    hpt
  have hIabs : (∫ z in Set.Ioc θ A, |deriv (deriv u) z|) ≤
      Real.sqrt (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
        * Real.sqrt (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta)) := by
    rw [abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc (fun z _ => abs_nonneg _))] at hcs
    exact hcs
  have hZb : (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
      ≤ ∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z := by
    refine MeasureTheory.setIntegral_mono_set hX' ?_ ?_
    · show ∀ᵐ z ∂(volume.restrict (Set.Ioo 0 A)), 0 ≤ (deriv (deriv u) z) ^ 2 * σ z
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall (fun z hz => mul_nonneg (sq_nonneg _)
        (sig_nonneg_of_mem_Icc_pi4 ⟨by linarith [hz.1], by linarith [hz.2, Real.pi_pos]⟩))
    · rw [MeasureTheory.ae_le_set]
      refine measure_mono_null ?_ (measure_singleton A)
      intro z hz
      rw [Set.mem_singleton_iff]
      rcases lt_or_eq_of_le hz.1.2 with h | h
      · exact absurd ⟨lt_trans hθ.1 hz.1.1, h⟩ hz.2
      · exact h
  have hWb : (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta))
      ≤ (2 * A) ^ (Work.Spaces.eta) * A := by
    rw [← intervalIntegral.integral_of_le hθle]
    have hle : ∀ z ∈ Set.Icc θ A,
        (Real.sin (2 * z)) ^ (Work.Spaces.eta) ≤ (2 * A) ^ (Work.Spaces.eta) := by
      intro z hz
      have h1 : Real.sin (2 * z) ≤ 2 * z := Real.sin_le (by linarith [hz.1, hθ.1])
      have h2 : (0 : ℝ) ≤ Real.sin (2 * z) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hz.1, hθ.1])
          (by linarith [hz.2, hAle2, Real.pi_pos])
      have h3 : (Real.sin (2 * z)) ^ (Work.Spaces.eta) ≤ (2 * z) ^ (Work.Spaces.eta) :=
        Real.rpow_le_rpow h2 h1 Work.Spaces.eta_nonneg
      have h4 : (2 * z) ^ (Work.Spaces.eta) ≤ (2 * A) ^ (Work.Spaces.eta) :=
        Real.rpow_le_rpow (by linarith [hz.1, hθ.1]) (by linarith [hz.2]) Work.Spaces.eta_nonneg
      linarith
    have hkey : (∫ x in θ..A, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
        ≤ ∫ x in θ..A, (2 * A) ^ (Work.Spaces.eta) :=
      intervalIntegral.integral_mono_on hθle (hcontSin.intervalIntegrable_of_Icc hθle)
        intervalIntegrable_const hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at hkey
    have h1 : (A - θ) * (2 * A) ^ (Work.Spaces.eta)
        ≤ A * (2 * A) ^ (Work.Spaces.eta) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.1]) (Real.rpow_nonneg (by linarith [hA0]) _)
    have h2 : A * (2 * A) ^ (Work.Spaces.eta) = (2 * A) ^ (Work.Spaces.eta) * A := by ring
    linarith [hkey, h1, h2]
  have hZ0 : 0 ≤ ∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z :=
    setIntegral_nonneg measurableSet_Ioc (fun z hz => mul_nonneg (sq_nonneg _)
      (sig_nonneg_of_mem_Icc_pi4 ⟨le_of_lt (lt_trans hθ.1 hz.1), le_trans hz.2 hAle⟩))
  have hW0 : 0 ≤ ∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta) :=
    setIntegral_nonneg measurableSet_Ioc (fun z hz => Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hz.1, hθ.1])
        (by linarith [hz.2, hAle2, Real.pi_pos])) _)
  have hI2 : (∫ z in Set.Ioc θ A, |deriv (deriv u) z|) ^ 2
      ≤ (∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
        * ((2 * A) ^ (Work.Spaces.eta) * A) := by
    have h1 : (Real.sqrt (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
        * Real.sqrt (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta))) ^ 2
        = (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
          * (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta)) := by
      rw [mul_pow, Real.sq_sqrt hZ0, Real.sq_sqrt hW0]
    have h2 : (∫ z in Set.Ioc θ A, |deriv (deriv u) z|) ^ 2
        ≤ (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
          * (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta)) := by
      have h3 := pow_le_pow_left₀ (setIntegral_nonneg measurableSet_Ioc (fun z _ => abs_nonneg _))
        hIabs 2
      rwa [h1] at h3
    have h4 : (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
        * (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta))
        ≤ (∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
          * ((2 * A) ^ (Work.Spaces.eta) * A) :=
      mul_le_mul hZb hWb hW0 (le_trans hZ0 hZb)
    linarith
  have hintI : (∫ x in θ..A, |deriv (deriv u) x|) = ∫ z in Set.Ioc θ A, |deriv (deriv u) z| :=
    intervalIntegral.integral_of_le hθle
  have habs : |deriv u θ| ≤ |deriv u A| + ∫ x in θ..A, |deriv (deriv u) x| := by
    have h1 : deriv u θ = deriv u A - ∫ x in θ..A, deriv (deriv u) x := by linarith [hFTC]
    have h2 : |∫ x in θ..A, deriv (deriv u) x| ≤ ∫ x in θ..A, |deriv (deriv u) x| :=
      intervalIntegral.abs_integral_le_integral_abs hθle
    calc |deriv u θ| = |deriv u A - ∫ x in θ..A, deriv (deriv u) x| := by rw [h1]
      _ ≤ |deriv u A| + |∫ x in θ..A, deriv (deriv u) x| := by
          refine (abs_sub_le_iff (b := ∫ x in θ..A, deriv (deriv u) x)
            (c := |deriv u A| + |∫ x in θ..A, deriv (deriv u) x|)).mpr ⟨?_, ?_⟩
          · linarith [le_abs_self (deriv u A), neg_le_abs (∫ x in θ..A, deriv (deriv u) x)]
          · linarith [neg_le_abs (deriv u A), le_abs_self (∫ x in θ..A, deriv (deriv u) x)]
      _ ≤ |deriv u A| + ∫ x in θ..A, |deriv (deriv u) x| := by linarith
  have hYnn : 0 ≤ ∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z :=
    setIntegral_nonneg measurableSet_Ioo (fun z hz => mul_nonneg (sq_nonneg _)
      (sig_nonneg_of_mem_Icc_pi4 ⟨by linarith [hz.1], by linarith [hz.2, Real.pi_pos]⟩))
  have hWnn : 0 ≤ (2 * A) ^ (Work.Spaces.eta) * A :=
    mul_nonneg (Real.rpow_nonneg (by linarith [hA0]) _) (le_of_lt hA0)
  have hIle : (∫ x in θ..A, |deriv (deriv u) x|)
      ≤ Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
        * ((2 * A) ^ (Work.Spaces.eta) * A)) := by
    rw [hintI]
    have h0 : 0 ≤ ∫ z in Set.Ioc θ A, |deriv (deriv u) z| :=
      setIntegral_nonneg measurableSet_Ioc (fun z _ => abs_nonneg _)
    have h3 : Real.sqrt ((∫ z in Set.Ioc θ A, |deriv (deriv u) z|) ^ 2)
        ≤ Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
          * ((2 * A) ^ (Work.Spaces.eta) * A)) := Real.sqrt_le_sqrt hI2
    rwa [Real.sqrt_sq h0] at h3
  have hp : |deriv u θ| ≤ |deriv u A|
      + Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
          * ((2 * A) ^ (Work.Spaces.eta) * A)) := by
    linarith
  have h1 : (deriv u θ) ^ 2 ≤ (|deriv u A|
      + Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
        * ((2 * A) ^ (Work.Spaces.eta) * A))) ^ 2 := by
    have h' : |deriv u θ| ^ 2 ≤ (|deriv u A|
        + Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
          * ((2 * A) ^ (Work.Spaces.eta) * A))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hp 2
    rwa [sq_abs] at h'
  have hs2 : (Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
      * ((2 * A) ^ (Work.Spaces.eta) * A))) ^ 2
      = (∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
        * ((2 * A) ^ (Work.Spaces.eta) * A) := Real.sq_sqrt (mul_nonneg hYnn hWnn)
  nlinarith [h1, hs2, sq_nonneg (|deriv u A| - Real.sqrt ((∫ z in Set.Ioo 0 A,
      (deriv (deriv u) z) ^ 2 * σ z) * ((2 * A) ^ (Work.Spaces.eta) * A))),
    sq_abs (deriv u A)]

/-! ## Conjunct 1 -/

private lemma integrableOn_div_cos_sq (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 4)) := by
  have hsub : Set.Ioo 0 (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx; exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hF : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 4)) :=
    hB.mono_set hsub
  have hcont : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2) (Set.Ioo 0 (Real.pi / 4)) :=
    continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2) (fun θ hθ => by
      have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
      positivity)
  have hbdd : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 4))),
      ‖1 / Real.cos θ ^ 2‖ ≤ 2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun θ hθ => by
      have hcos : Real.sqrt 2 / 2 ≤ Real.cos θ := by
        have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 4) hθ.1.le
          (by linarith [Real.pi_pos]) hθ.2.le
        rwa [Real.cos_pi_div_four] at h
      have hcospos : 0 < Real.cos θ := lt_of_lt_of_le (by positivity) hcos
      have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
        have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        rw [← h2]
        exact pow_le_pow_left₀ (by positivity) hcos 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.cos θ ^ 2)]
      linarith)
  have hI := hF.mul_bdd (hcont.aestronglyMeasurable measurableSet_Ioo) hbdd
  refine hI.congr ?_
  show ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 4))),
    u θ ^ 2 * σ θ * (1 / Real.cos θ ^ 2) = (u θ / Real.cos θ) ^ 2 * σ θ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall (fun θ hθ => by
    have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
    rw [div_pow]
    ring)

/-! ## Conjunct 2 -/

/-- The derivative of `θ ↦ u θ / cos θ`, in the single-fraction form. -/
private lemma deriv_div_cos_formula (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2 := by
  have hmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hd : HasDerivAt u (deriv u θ) θ :=
    ((hu.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hmem)).hasDerivAt
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hmem.2⟩)
  have hdiv : HasDerivAt (fun t => u t / Real.cos t)
      ((deriv u θ * Real.cos θ - u θ * (-Real.sin θ)) / Real.cos θ ^ 2) θ :=
    hd.div (Real.hasDerivAt_cos θ) hcos
  rw [hdiv.deriv]
  rw [show deriv u θ * Real.cos θ - u θ * (-Real.sin θ)
      = deriv u θ * Real.cos θ + u θ * Real.sin θ by ring]

private lemma psi'_sq_le (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (deriv (fun t => u t / Real.cos t) θ) ^ 2 * σ θ
      ≤ 4 * ((deriv u θ) ^ 2 * σ θ) + 8 * ((u θ) ^ 2 * σ θ) := by
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 4) hθ.1.le
      (by linarith [Real.pi_pos]) hθ.2.le
    rwa [Real.cos_pi_div_four] at h
  have hcospos : 0 < Real.cos θ := lt_of_lt_of_le (by positivity) hcos
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
    have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← h2]
    exact pow_le_pow_left₀ (by positivity) hcos 2
  have hsin2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hσ : 0 ≤ σ θ := le_of_lt (sig_pos_of_mem_Ioo_pi4 hθ)
  rw [deriv_div_cos_formula u hu hθ]
  have hkey : ((deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2) ^ 2
      ≤ 4 * (deriv u θ) ^ 2 + 8 * (u θ) ^ 2 := by
    have hden : 0 < (Real.cos θ ^ 2) ^ 2 := by positivity
    rw [div_pow, div_le_iff₀ hden]
    have hA : (1 : ℝ) ≤ 4 * (Real.cos θ ^ 2) ^ 2 := by nlinarith [hcos2]
    have hB : (1 : ℝ) ≤ 2 * Real.cos θ ^ 2 := by linarith
    have h1 : (deriv u θ * Real.cos θ + u θ * Real.sin θ) ^ 2
        ≤ 2 * (deriv u θ * Real.cos θ) ^ 2 + 2 * (u θ * Real.sin θ) ^ 2 := by
      nlinarith [sq_nonneg (deriv u θ * Real.cos θ - u θ * Real.sin θ)]
    have h2 : 2 * (u θ * Real.sin θ) ^ 2 ≤ 8 * (u θ) ^ 2 * (Real.cos θ ^ 2) ^ 2 := by
      have hs4 : Real.sin θ ^ 2 ≤ 4 * (Real.cos θ ^ 2) ^ 2 := le_trans hsin2 hA
      calc 2 * (u θ * Real.sin θ) ^ 2 = 2 * (u θ) ^ 2 * Real.sin θ ^ 2 := by ring
        _ ≤ 2 * (u θ) ^ 2 * (4 * (Real.cos θ ^ 2) ^ 2) :=
              mul_le_mul_of_nonneg_left hs4 (by positivity)
        _ = 8 * (u θ) ^ 2 * (Real.cos θ ^ 2) ^ 2 := by ring
    have h3 : 2 * (deriv u θ * Real.cos θ) ^ 2
        ≤ 4 * (deriv u θ) ^ 2 * (Real.cos θ ^ 2) ^ 2 := by
      have hc2nn : 0 ≤ 2 * (deriv u θ) ^ 2 * Real.cos θ ^ 2 := by positivity
      calc 2 * (deriv u θ * Real.cos θ) ^ 2
          = 2 * (deriv u θ) ^ 2 * Real.cos θ ^ 2 := by ring
        _ = 2 * (deriv u θ) ^ 2 * Real.cos θ ^ 2 * 1 := by ring
        _ ≤ 2 * (deriv u θ) ^ 2 * Real.cos θ ^ 2 * (2 * Real.cos θ ^ 2) :=
              mul_le_mul_of_nonneg_left hB hc2nn
        _ = 4 * (deriv u θ) ^ 2 * (Real.cos θ ^ 2) ^ 2 := by ring
    linarith [h1, h2, h3]
  calc ((deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2) ^ 2 * σ θ
      ≤ (4 * (deriv u θ) ^ 2 + 8 * (u θ) ^ 2) * σ θ := mul_le_mul_of_nonneg_right hkey hσ
    _ = 4 * ((deriv u θ) ^ 2 * σ θ) + 8 * ((u θ) ^ 2 * σ θ) := by ring

private lemma integrableOn_deriv_div_cos_sq (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 * σ θ)
      (Set.Ioo 0 (Real.pi / 4)) := by
  have hsub : Set.Ioo 0 (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx; exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hX' : IntegrableOn (fun z => (deriv (deriv u) z) ^ 2 * σ z) (Set.Ioo 0 (Real.pi / 4)) :=
    hX.mono_set hsub
  have hB' : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 4)) :=
    hB.mono_set hsub
  set M : ℝ := 2 * (deriv u (Real.pi / 4)) ^ 2
    + 2 * ((2 * (Real.pi / 4)) ^ (Work.Spaces.eta) * (Real.pi / 4))
      * (∫ z in Set.Ioo 0 (Real.pi / 4), (deriv (deriv u) z) ^ 2 * σ z) with hMdef
  have hdom : IntegrableOn (fun θ => 4 * (M * σ θ) + 8 * ((u θ) ^ 2 * σ θ))
      (Set.Ioo 0 (Real.pi / 4)) :=
    ((integrableOn_sig_pi4.const_mul M).const_mul 4).add (hB'.const_mul 8)
  refine Integrable.mono_nonneg hdom ?_ ?_ ?_
  · apply Measurable.aestronglyMeasurable
    change Measurable (fun θ : ℝ => deriv (fun t => u t / Real.cos t) θ ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact mul_nonneg (sq_nonneg _) (le_of_lt (sig_pos_of_mem_Ioo_pi4 hθ))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hpt := psi'_sq_le u hu hθ
    have hb : (deriv u θ) ^ 2 ≤ M := by
      rw [hMdef]
      exact deriv_sq_le_of_mem u hu pi_div_four_pos (le_refl _) hθ hX'
    have h1 : (deriv u θ) ^ 2 * σ θ ≤ M * σ θ :=
      mul_le_mul_of_nonneg_right hb (le_of_lt (sig_pos_of_mem_Ioo_pi4 hθ))
    linarith [hpt, h1]


/-! ## The requested lemma -/

theorem slice_psi_near_zero (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hB : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 4)) ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 4)) :=
  ⟨integrableOn_div_cos_sq u hu hB, integrableOn_deriv_div_cos_sq u hu hB hX⟩



open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## Tools

Two auxiliary results, proved in sibling modules, are used below:

* `Work.FTS.EllipticEst.Honest.integrableOn_of_sin_sq_mul` — removal of the `sin²` factor on
  the right half (there `sin² θ ≥ 1/2`);
* `Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv` — boundedness of a differentiable
  function whose derivative is integrable.
-/

/-! ## Elementary facts about the angular weight -/

/-- `sig θ = sin(2θ)^{-η}` is measurable. -/
private lemma sig_meas : Measurable Work.FTS.EllipticEst.AngSecond.sig := by
  unfold Work.FTS.EllipticEst.AngSecond.sig
  fun_prop

/-- `sig` is integrable on `(π/4, π/2)` (the only singularity is at `π/2`, of order
`η = 99/100 < 1`). -/
private lemma sig_integrableOn :
    MeasureTheory.IntegrableOn Work.FTS.EllipticEst.AngSecond.sig
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have h := Work.FTS.EllipticEst.TanTheta.integrableOn_sin_two_rpow_neg
    (η := Work.Spaces.eta) (by norm_num [Work.Spaces.eta])
  exact h.mono_set (fun x hx => ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩)

/-- `sig` is continuous on `(π/4, π/2)`. -/
private lemma sig_continuousOn :
    ContinuousOn Work.FTS.EllipticEst.AngSecond.sig
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  change ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (Real.pi / 4) (Real.pi / 2))
  refine ContinuousOn.rpow_const ?_ (fun θ hθ => Or.inl ?_)
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos]))

/-- Membership in the closed angular interval from membership in the open right half. -/
private lemma mem_Iθ_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    θ ∈ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact ⟨by linarith [Real.pi_pos, hθ.1], le_of_lt hθ.2⟩

/-! ## The slice lemma -/

theorem slice_psi_near_pi2 (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have hlt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun θ hθ => ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  -- ### first conjunct: the `sin²θ` factor can be removed on the right half
  have h1 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine integrableOn_of_sin_sq_mul ?_ ?_ ?_
    · exact ((measurable_deriv _).pow_const 2).mul sig_meas
    · intro θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.AngSecond.sig_nonneg (mem_Iθ_of_mem_Ioo hθ))
    · simpa only [mul_assoc] using hY
  refine ⟨h1, ?_⟩
  -- ### second conjunct: `φ = u/cos θ` is bounded
  have hderiv : ∀ x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      HasDerivAt (fun θ => u θ / Real.cos θ) (deriv (fun θ => u θ / Real.cos θ) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
    have hdu : DifferentiableAt ℝ u x :=
      (hu.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt (by norm_num)
    have hcos : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos],
        by linarith [hx.2, Real.pi_pos]⟩)
    exact (hdu.div Real.differentiableAt_cos hcos).hasDerivAt
  have hsq : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono' h1 ?_ ?_
    · exact ((measurable_deriv _).pow_const 2).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hsig1 : 1 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
        Work.FTS.EllipticEst.AngSecond.one_le_sig ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
      have hsq0 : 0 ≤ (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hsq0]
      nlinarith [hsig1, hsq0]
  have habs : MeasureTheory.IntegrableOn
      (fun θ => |deriv (fun θ => u θ / Real.cos θ) θ|)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (by simp)
    refine MeasureTheory.Integrable.mono' (hsq.add hone) ?_ ?_
    · exact ((measurable_deriv _).abs).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ _
      have hnn : 0 ≤ |deriv (fun θ => u θ / Real.cos θ) θ| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_abs, Pi.add_apply]
      by_cases hcase : |deriv (fun θ => u θ / Real.cos θ) θ| ≤ 1
      · nlinarith [sq_nonneg (deriv (fun θ => u θ / Real.cos θ) θ)]
      · rw [not_le] at hcase
        nlinarith [sq_abs (deriv (fun θ => u θ / Real.cos θ) θ), hcase, hnn]
  have hIntφ' : MeasureTheory.IntegrableOn (deriv (fun θ => u θ / Real.cos θ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono' habs (measurable_deriv _).aestronglyMeasurable ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
  obtain ⟨C, hC0, hC⟩ := bdd_of_integrableOn_deriv hlt hderiv hIntφ'
  have hφcont : ContinuousOn (fun θ => u θ / Real.cos θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    (hu.continuousOn.mono hsub).div Real.continuous_cos.continuousOn
      (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩))
  refine MeasureTheory.Integrable.mono' (sig_integrableOn.const_mul (C ^ 2)) ?_ ?_
  · exact ((hφcont.pow 2).mul sig_continuousOn).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hb := hC θ hθ
    have hs0 : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg (mem_Iθ_of_mem_Ioo hθ)
    have hsqC : (u θ / Real.cos θ) ^ 2 ≤ C ^ 2 := by
      nlinarith [hb, abs_nonneg (u θ / Real.cos θ), sq_abs (u θ / Real.cos θ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hs0)]
    exact mul_le_mul_of_nonneg_right hsqC hs0


end Work.FTS.EllipticEst.H2W.AngBW.S3
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sliceI4Open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

theorem sliceI4Open (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ z, Ψ z 0 = 0) (hpi : ∀ z, Ψ z (Real.pi / 2) = 0) {z : ℝ} (hz : 0 < z)
    (hM1 : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hM2 : Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ))
    (hM3 : Work.FTS.EllipticEst.AngSecond.IPMem Ψ Ψ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (Ψ z θ / Real.cos θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (hBD : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (hB2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (hBD2 : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ) ^ 2
        * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        * Work.Spaces.pthIter 2 Ψ z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ (1 - Work.Spaces.eta) * (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  -- shortcuts
  set u : ℝ → ℝ := fun θ => Ψ z θ with hu
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hIooM : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self
  -- ## smoothness and boundary values of the slice
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := by
    have hp : ContDiffOn ℝ 2 (fun t : ℝ => (z, t)) (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmap : Set.MapsTo (fun t : ℝ => (z, t)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun t ht => ⟨hz, ht⟩
    have h := (hsm 2).comp hp hmap
    simpa [Function.comp_def, Function.uncurry, hu] using h
  have hu0 : u 0 = 0 := by simpa only [hu] using h0 z
  have hu1 : u (Real.pi / 2) = 0 := by simpa only [hu] using hpi z
  -- ## the integrability inputs of the honest slice lemmas
  have hA_u : MeasureTheory.IntegrableOn (fun θ => u θ ^ 2 * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => (u θ ^ 2 * AngSecond.sig θ) * AngSecond.w2 z) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun (hM3.1 z hzI) ?_ measurableSet_Icc
      intro θ _
      simp only [hu]
      ring
    exact (AngSecond.integrableOn_of_mul_w2 hz measurableSet_Icc h1).mono_set hsub
  have hX : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * AngSecond.sig θ) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun hB2 ?_ measurableSet_Icc
      intro θ _
      rfl
    exact h2.mono_set hsub
  have hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hBD2.mono_set hsub) ?_ hIooM
    intro θ _
    simp only [hu]
  have hAd : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hB.mono_set hsub) ?_ hIooM
    intro θ _
    simp only [hu]
  have hAd' : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hBD.mono_set hsub) ?_ hIooM
    intro θ _
    simp only [hu]
  -- ## the endpoint vanishing of the integration-by-parts boundary terms
  obtain ⟨hv1, hv2, hv3, hv4⟩ :=
    Honest.psi_boundary_vanish u hu2 hu0 hu1 hA_u hX hY hAd hAd'
  -- ## the honest slice identity
  have hident := Honest.slice_ident_honest u hu2 hu0 hu1 hA_u hX hY hAd hAd' hv1 hv2 hv3 hv4
  -- ## the pointwise identity `∂_θ(tan θ · u) - u = sin θ · ∂_θ(u / cos θ)`
  have htan : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ
        = Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ := by
    intro θ hθ
    have hdiff : DifferentiableAt ℝ u θ :=
      (hu2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have h := AngSecond.I4_tan_mul_sub_deriv u hθ hdiff
    simp only [Work.Spaces.pth, hu] at h ⊢
    exact h
  -- ## step 1: linearity of the `θ`-integral
  have step1 :
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
          * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
        - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ
            * AngSecond.w2 z * AngSecond.sig θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ := by
    rw [← MeasureTheory.integral_sub (hM1.1 z hzI) (hM2.1 z hzI)]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
      simp only [Pi.sub_apply]; ring
  -- ## step 2: nothing happens on the endpoints
  have step2 :
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ := by
    rw [AngSecond.setIntegral_Ioo_Iθ]
  -- ## step 3: rewrite the integrand as `sin θ ψ' u'' σ` and pull out `w²`
  have step3 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
      = AngSecond.w2 z * (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
            * deriv (fun θ' => u θ' / Real.cos θ') θ * deriv (deriv u) θ
            * AngSecond.sig θ) := by
    rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ
            * deriv (fun θ' => u θ' / Real.cos θ') θ * deriv (deriv u) θ
            * AngSecond.sig θ) * AngSecond.w2 z from
      MeasureTheory.setIntegral_congr_fun hIooM fun θ hθ => by
        have hf : Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv u) θ := rfl
        rw [htan θ hθ, hf]; ring]
    rw [MeasureTheory.integral_mul_const]; ring
  -- ## step 4: the value of the slice integral
  have step5 :
      (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
      = AngSecond.w2 z * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          u θ * u θ * AngSecond.sig θ) := by
    rw [← AngSecond.setIntegral_Ioo_Iθ
      (fun θ => Ψ z θ * Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)]
    rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Ψ z θ * Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (u θ * u θ * AngSecond.sig θ) * AngSecond.w2 z from
      MeasureTheory.setIntegral_congr_fun hIooM fun θ _ => by
        simp only [hu]; ring]
    rw [MeasureTheory.integral_mul_const]; ring
  -- ## the two numerical inputs of the final inequality
  have hCnn : 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), AngSecond.acoef θ
      * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * AngSecond.sig θ := by
    refine MeasureTheory.setIntegral_nonneg hIooM fun θ hθ => ?_
    exact mul_nonneg (mul_nonneg (AngSecond.acoef_nonneg θ) (sq_nonneg _))
      (AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hN : MeasureTheory.IntegrableOn (fun θ => u θ * u θ * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hA_u ?_ hIooM
    intro θ _
    ring
  have hcosle : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * AngSecond.sig θ)
      ≤ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), u θ * u θ * AngSecond.sig θ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hIooM fun θ hθ => ?_
    · have h := AngSecond.integrableOn_continuousOn_mul (g := fun θ => Real.cos (2 * θ)) hAd
        (by fun_prop) hIooM fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ hIooM
      intro θ _
      ring
    · exact hN.const_mul 2
    · have h1 := AngSecond.cos_two_mul_mul_div_cos_sq_le (a := u θ) hθ
      have h2 : 0 ≤ AngSecond.sig θ := AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      have h4 : 2 * u θ ^ 2 * AngSecond.sig θ = 2 * (u θ * u θ * AngSecond.sig θ) := by ring
      linarith [h3, h4]
  -- ## assemble
  rw [step1, step2, step3, hident, step5]
  set B : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2),
      Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * AngSecond.sig θ with hBdef
  set C : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), AngSecond.acoef θ
      * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * AngSecond.sig θ with hCdef
  set N : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), u θ * u θ * AngSecond.sig θ with hNdef
  have hBle : B ≤ 2 * N := by rw [hBdef, hNdef]; exact hcosle
  have hCnn' : 0 ≤ C := by rw [hCdef]; exact hCnn
  have hw2nn : 0 ≤ AngSecond.w2 z := AngSecond.w2_nonneg z
  have heta : 0 < (1 - Work.Spaces.eta) / 2 := by linarith [AngSecond.one_sub_eta_pos]
  have e1 : (1 - Work.Spaces.eta) / 2 * B - C ≤ (1 - Work.Spaces.eta) / 2 * B := by
    linarith [hCnn']
  have e2 : (1 - Work.Spaces.eta) / 2 * B ≤ (1 - Work.Spaces.eta) / 2 * (2 * N) :=
    mul_le_mul_of_nonneg_left hBle (le_of_lt heta)
  have e3 : (1 - Work.Spaces.eta) / 2 * (2 * N) = (1 - Work.Spaces.eta) * N := by ring
  have e4 : AngSecond.w2 z * ((1 - Work.Spaces.eta) / 2 * B - C)
      ≤ AngSecond.w2 z * ((1 - Work.Spaces.eta) * N) :=
    calc AngSecond.w2 z * ((1 - Work.Spaces.eta) / 2 * B - C)
        ≤ AngSecond.w2 z * ((1 - Work.Spaces.eta) / 2 * B) :=
          mul_le_mul_of_nonneg_left e1 hw2nn
      _ ≤ AngSecond.w2 z * ((1 - Work.Spaces.eta) / 2 * (2 * N)) :=
          mul_le_mul_of_nonneg_left e2 hw2nn
      _ = AngSecond.w2 z * ((1 - Work.Spaces.eta) * N) := by rw [e3]
  have e5 : AngSecond.w2 z * ((1 - Work.Spaces.eta) * N)
      = (1 - Work.Spaces.eta) * (AngSecond.w2 z * N) := by ring
  linarith [e4, e5]

end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonDerivBounded =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSliceDerivBdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory




end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.EllFarTop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top-order far-window bound, assembled from the two slot estimates

This module contains the **assembly** of the far-window estimate for the top-order slot
`∂^{k+1}(v)` (`v = u / cos θ`) from

* the `i ≤ k` slot bounds `TopCoreB.xTerm_le` + `TopCoreB.integrableOn_sinWeight_xDivX`
  (proved in `TopCoreB/far_vBound.lean`), and
* the `i = k + 1` slot bound, taken as an explicit hypothesis
  (`htop`, the statement of `Work.FTS.EllipticEst.remov.sinWeight_xDivX_top_le`).

Produced here:

* `farTopXAuxLive_of_top` — the reflected-variable form
  `∫_{(0)..xEnd} (∂^{k+1}(shiftV u))² sin(2x)^{2k-γ} ≤ C·FarR k γ u g` together with its
  integrability.  This is exactly the `hTopXph` gap of `remov/slice_ang_v_far.lean`.
* `slice_ang_v_far_live_of_top` — a *copy* of `Work.FTS.EllipticEst.remov.slice_ang_v_far`
  (whose only missing step is that `hTopXph` gap), with the gap filled by `htop`.

The wiring to the child lemma `sinWeight_xDivX_top_le` is done in `EllFarTopWired.lean`.

The pointwise input is `TopCoreB.shiftV_deriv_sq_le` with the derivative bounds of
`TopCoreB.sinDivDerivBounds (k+1)`: `(∂^{k+1} v)² ≤ A · Σ_{i ≤ k+1} (∂^i (U/x))²`,
`U = shiftU u`, `A = (2^{k+1}K)²(k+2)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.EllipticEst.remov.TopCoreB

/-- `secH` is smooth on `(0, xEnd)`. -/
private theorem contDiffOn_secH_local (n : ℕ) :
    ContDiffOn ℝ n TopCoreB.secH (Set.Ioo 0 TopCoreB.xEnd) := by
  intro x hx
  exact (TopCoreB.contDiffAt_secH (m := n) (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1
    (by linarith [hx.2, TopCoreB.xEnd_lt_pi_half, Real.pi_pos])))).contDiffWithinAt

/-- The reflected `v = u/cos θ` is `C^n` on `(0, xEnd)`. -/
private theorem contDiffOn_shiftV_local {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (n + 1) u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (TopCoreB.shiftV u) (Set.Ioo 0 TopCoreB.xEnd) := by
  intro x hx
  have h1 : ContDiffWithinAt ℝ n (fun y : ℝ => TopCoreB.shiftU u y / y)
      (Set.Ioo 0 TopCoreB.xEnd) x :=
    (TopCoreB.contDiffOn_divX hu).contDiffWithinAt hx
  have h2 : ContDiffWithinAt ℝ n TopCoreB.secH (Set.Ioo 0 TopCoreB.xEnd) x :=
    (contDiffOn_secH_local n).contDiffWithinAt hx
  have h3 : ContDiffWithinAt ℝ n
      (fun y : ℝ => (TopCoreB.shiftU u y / y) * TopCoreB.secH y)
      (Set.Ioo 0 TopCoreB.xEnd) x := h1.mul h2
  have hev : (fun y : ℝ => (TopCoreB.shiftU u y / y) * TopCoreB.secH y)
      =ᶠ[𝓝[Set.Ioo (0:ℝ) TopCoreB.xEnd] x] TopCoreB.shiftV u := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    simp only [TopCoreB.shiftV, TopCoreB.secH]
    field_simp
  exact h3.congr_of_eventuallyEq hev.symm (hev.self_of_nhdsWithin hx).symm

/-- **The top-order far-window bound**, in the reflected variable, from the `i = k+1` slot. -/
theorem farTopXAuxLive_of_top (k : ℕ) (hk : 2 ≤ k)
    (htop : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      TopCoreB.FarHyp k γ u g →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (Set.Ioc 0 TopCoreB.xEnd) ∧
      (∫ x in (0 : ℝ)..TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ C * TopCoreB.FarR k γ u g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      TopCoreB.FarHyp k γ u g →
      (∫ x in (0 : ℝ)..TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ C * TopCoreB.FarR k γ u g ∧
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (Set.Ioc 0 TopCoreB.xEnd) := by
  obtain ⟨Ct, hCtpos, htop'⟩ := htop
  obtain ⟨K, hKpos, hKb⟩ := TopCoreB.sinDivDerivBounds (k + 1)
  set A : ℝ := ((2 : ℝ) ^ (k + 1) * K) ^ 2 * ((k + 2 : ℕ) : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set Cs : ℝ := ((k + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) + Ct) with hCsdef
  have hCspos : 0 < Cs := by
    rw [hCsdef]
    have : (0 : ℝ) < (2 : ℝ) ^ (2 * k + 3) + Ct := by positivity
    positivity
  refine ⟨A * Cs + 1, by positivity, ?_⟩
  intro γ u g h
  have hFnn : 0 ≤ TopCoreB.FarR k γ u g := TopCoreB.FarR_nonneg hk h
  have hK : ∀ i ≤ k + 1, ∀ y ∈ Set.Ioc (0 : ℝ) TopCoreB.xEnd,
      |iteratedDeriv i TopCoreB.secH y| ≤ K := fun i hi y hy => hKb i hi y hy
  have hu1 : ContDiffOn ℝ (k + 1) u (Set.Ioo 0 (Real.pi / 2)) :=
    h.huC.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2))
  -- a.e. only the interior matters
  have haeIoo : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)),
      x ∈ Set.Ioo 0 TopCoreB.xEnd := by
    have h1 : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) TopCoreB.xEnd)),
        x ∈ Set.Ioo 0 TopCoreB.xEnd := ae_restrict_mem measurableSet_Ioo
    rwa [Measure.restrict_congr_set
      (Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := TopCoreB.xEnd))] at h1
  -- the pointwise Leibniz bound
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) TopCoreB.xEnd,
      (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ A * ∑ i ∈ Finset.range (k + 2),
            ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
              * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) := by
    intro x hx
    have hsnn : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _
    have h1 := TopCoreB.shiftV_deriv_sq_le (u := u) (m := k + 1) hK hu1 hx
    rw [show k + 1 + 1 = k + 2 from by omega] at h1
    have h2 : (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ (A * ∑ i ∈ Finset.range (k + 2),
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2)
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
      rw [hAdef]
      exact mul_le_mul_of_nonneg_right h1 hsnn
    refine h2.trans_eq ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the per-slot integrability
  have hslotint : ∀ i ∈ Finset.range (k + 2),
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioc 0 TopCoreB.xEnd) := by
    intro i hi
    have hik : i ≤ k + 1 := by have := Finset.mem_range.mp hi; omega
    rcases eq_or_lt_of_le hik with h1 | h1
    · subst h1
      exact (htop' γ u g h).1
    · exact TopCoreB.integrableOn_sinWeight_xDivX hk h (i := i) (by omega)
  have hGint : MeasureTheory.IntegrableOn (fun x : ℝ => ∑ i ∈ Finset.range (k + 2),
      ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))) (Set.Ioc 0 TopCoreB.xEnd) :=
    integrable_finsetSum _ fun i hi => hslotint i hi
  -- the slot bounds, summed
  have hslotbnd : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        ∑ i ∈ Finset.range (k + 2),
          ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)))
      ≤ Cs * TopCoreB.FarR k γ u g := by
    rw [integral_finsetSum _ fun i hi => hslotint i hi]
    have hterm : ∀ i ∈ Finset.range (k + 2),
        (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
          ≤ ((2 : ℝ) ^ (2 * k + 3) + Ct) * TopCoreB.FarR k γ u g := by
      intro i hi
      have hik : i ≤ k + 1 := by have := Finset.mem_range.mp hi; omega
      have hconv : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
          = ∫ x in (0 : ℝ)..TopCoreB.xEnd,
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
        (intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le).symm
      rw [hconv]
      have hb : (∫ x in (0 : ℝ)..TopCoreB.xEnd,
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
            ≤ (2 : ℝ) ^ (2 * k + 3) * TopCoreB.FarR k γ u g
          ∨ (∫ x in (0 : ℝ)..TopCoreB.xEnd,
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
            ≤ Ct * TopCoreB.FarR k γ u g := by
        rcases eq_or_lt_of_le hik with h1 | h1
        · subst h1
          exact Or.inr (htop' γ u g h).2
        · exact Or.inl (TopCoreB.xTerm_le hk h (i := i) (by omega))
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k + 3) := by positivity
      rcases hb with hb | hb
      · exact hb.trans (by nlinarith [hFnn, hCtpos.le, h2pos])
      · exact hb.trans (by nlinarith [hFnn, hCtpos, h2pos])
    calc (∑ i ∈ Finset.range (k + 2),
            ∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
              (iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ ∑ _i ∈ Finset.range (k + 2),
            ((2 : ℝ) ^ (2 * k + 3) + Ct) * TopCoreB.FarR k γ u g :=
          Finset.sum_le_sum hterm
      _ = Cs * TopCoreB.FarR k γ u g := by
          rw [hCsdef, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- integrability of the left-hand side
  have hLHSint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioc 0 TopCoreB.xEnd) := by
    have hcont : ContinuousOn (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioo 0 TopCoreB.xEnd) := by
      have hcdV : ContDiffOn ℝ (k + 1) (TopCoreB.shiftV u) (Set.Ioo 0 TopCoreB.xEnd) :=
        contDiffOn_shiftV_local (n := k + 1) h.huC
      have hunic : UniqueDiffOn ℝ (Set.Ioo (0:ℝ) TopCoreB.xEnd) := isOpen_Ioo.uniqueDiffOn
      have hcontW : ContinuousOn
          (iteratedDerivWithin (k + 1) (TopCoreB.shiftV u) (Set.Ioo 0 TopCoreB.xEnd))
          (Set.Ioo 0 TopCoreB.xEnd) :=
        hcdV.continuousOn_iteratedDerivWithin le_rfl hunic
      have hcont' : ContinuousOn (iteratedDeriv (k + 1) (TopCoreB.shiftV u))
          (Set.Ioo 0 TopCoreB.xEnd) :=
        hcontW.congr fun x hx =>
          (iteratedDerivWithin_eq_iteratedDeriv hunic
            (hcdV.contDiffAt (isOpen_Ioo.mem_nhds hx)) hx).symm
      exact (hcont'.pow 2).mul (TopCoreB.continuousOn_sin_rpow)
    have hass : AEStronglyMeasurable
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)) :=
      TopCoreB.aestronglyMeasurable_Ioc_of_continuousOn hcont
    refine (hGint.const_mul A).mono' hass ?_
    filter_upwards [haeIoo] with x hx
    have hsnn : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hsnn)]
    exact hpt x hx
  -- the integral bound
  have hLHSle : (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
        (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ A * (Cs * TopCoreB.FarR k γ u g) := by
    have hae : (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)]
        (fun x : ℝ => A * ∑ i ∈ Finset.range (k + 2),
              ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))) := by
      filter_upwards [haeIoo] with x hx
      exact hpt x hx
    have h0 : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) TopCoreB.xEnd)]
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (TopCoreB.sin_two_nonneg_Ioc ⟨hx.1, hx.2⟩) _)
    calc (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ ∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, A * ∑ i ∈ Finset.range (k + 2),
              ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) :=
          integral_mono_of_nonneg h0 (hGint.const_mul A) hae
      _ = A * (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd, ∑ i ∈ Finset.range (k + 2),
              ((iteratedDeriv i (fun y : ℝ => TopCoreB.shiftU u y / y) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))) :=
          integral_const_mul A _
      _ ≤ A * (Cs * TopCoreB.FarR k γ u g) := mul_le_mul_of_nonneg_left hslotbnd hApos.le
  refine ⟨?_, hLHSint⟩
  rw [intervalIntegral.integral_of_le TopCoreB.xEnd_pos.le]
  calc (∫ x in Set.Ioc (0 : ℝ) TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ A * (Cs * TopCoreB.FarR k γ u g) := hLHSle
    _ ≤ (A * Cs + 1) * TopCoreB.FarR k γ u g := by nlinarith [hFnn, hApos, hCspos]


open scoped Real Topology
open MeasureTheory Set Filter

/-- On the angular interval `Iθ` the weight `sin(2θ)` is nonnegative. -/
private lemma sin_two_nonneg_Iθ_local {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `AngRHS` is a sum of integrals of nonnegative functions. -/
private lemma angRHS_nonneg_prv (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : 0 ≤ AngRHS k γ u g := by
  unfold AngRHS
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
  · exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_local hθ) _)
  · exact Finset.sum_nonneg fun j _ =>
      setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_local hθ) _)
  · exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_local hθ) _)
  · exact setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _
  · exact setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _

/-- `TopCoreB.FarR` is `AngRHS`, definitionally. -/
private lemma farR_eq_angRHS (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    TopCoreB.FarR k γ u g = AngRHS k γ u g := by
  simp only [TopCoreB.FarR, AngRHS]

/-- The far window, as an explicit interval. -/
private lemma farSet_eq : TopCoreB.farSet = Set.Icc (3 * Real.pi / 8) (Real.pi / 2) := rfl

/-- The far-window integrand, written in the `TopCoreB` vocabulary. -/
private lemma integrand_eq (k : ℕ) (γ : ℝ) (m : ℕ) (u : ℝ → ℝ) (θ : ℝ) :
    (iteratedDeriv m (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ
      = (iteratedDeriv m (fun t : ℝ => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := by
  have h1 : TopCoreB.vF u = fun t : ℝ => u t / Real.cos t := rfl
  have h2 : TopCoreB.qW k γ θ = Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) := rfl
  rw [h1, h2]

/-- The far-window integral in the target's notation equals the `TopCoreB` one. -/
private lemma farIntegral_eq (k : ℕ) (γ : ℝ) (m : ℕ) (u : ℝ → ℝ) :
    (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
        (iteratedDeriv m (fun t : ℝ => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
      = ∫ θ in TopCoreB.farSet,
          (iteratedDeriv m (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ := by
  rw [farSet_eq]
  exact setIntegral_congr_fun measurableSet_Icc fun θ _ => (integrand_eq k γ m u θ).symm

/-- Integrability on the far window, transferred to the reflected variable. -/
private lemma integrableOn_farSet_iff (F : ℝ → ℝ) :
    MeasureTheory.IntegrableOn F TopCoreB.farSet ↔
      MeasureTheory.IntegrableOn (fun x : ℝ => F (Real.pi / 2 - x))
        (Set.Icc 0 TopCoreB.xEnd) := by
  have h := (MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    TopCoreB.measurePreserving_reflectC TopCoreB.measurableEmbedding_reflectC
    (s := TopCoreB.farSet) (f := F)).symm
  rw [TopCoreB.preimage_reflectC_farSet] at h
  simpa [TopCoreB.reflectC, Function.comp_def] using h

/-- **Weighted `v = u / cos θ` bound on the far window `[3π/8, π/2]`.**

For `k ≥ 2`, `γ ∈ [1,5/4]`, `u ∈ C^{k+2}(0,π/2)` continuous on `[0,π/2]` with `u 0 = u (π/2) = 0`
and `g = Lzero1 u` on the open interval, with the six integrability hypotheses of the target
`slice_ang_gen`, one has for every `m ≤ k+1`

`∫_{[3π/8,π/2]} (∂^m (u/cos))² · sin(2θ)^(2k-γ) ≤ C · AngRHS k γ u g`

(`AngRHS` as in `Submission/Work/FTS/EllipticEst/remov/slice_ang_reduce.lean`), together with the
integrability of the left-hand integrand.

Route (see `Submission/Work/FTS/EllipticEst/remov/NOTES_slice_ang_v_bound.md`): substitute
`x = π/2 - θ ∈ (0,π/8]`, `U x := u (π/2 - x)`, `V x := U x / sin x`.  Then
`v(π/2-x) = V x`, `sin(2θ) = sin(2x)`, `∂_θ^m v(θ) = ± V^{(m)}(x)`, so the far integral becomes
`∫_0^{π/8}(V^{(m)})² sin(2x)^{2k-γ} dx ≤ 2^{2k-γ} ∫_0^{π/8}(V^{(m)})² x^{2k-γ} dx`.  Write
`V = (U h)/x` with `h = x/sin x` smooth on `[0,π/8]` with bounded derivatives (Leibniz):
`V^{(m)} = Σ_{i≤m}C(m,i)h^{(i)}(U/x)^{(m-i)}`.  For each division order `j ≤ k` apply the
Hilbert/Hardy division inequality `∫ x^{2j-γ}((U/x)^{(j)})² ≤ C∫x^{2j-γ}(U^{(j+1)})²` at the needed
finite smoothness — this is the lemma `Work.FTS.EllipticEst.remov.hardyDiv_fin` being produced in
parallel; if `Submission/Work/FTS/EllipticEst/remov/hardyDiv_fin.lean` is not yet on disk, prove
that division inequality locally in your own file (it is the statement of
`Work.FTS.H2.DivQ.hardyA_le_W` with `⊤` weakened to `C^{j+2}`; the `C^∞` case is already proved).
The weight comparison `x^{2k-γ} ≤ x^{2j-γ}` (`j ≤ k`) and
`∫x^{2j-γ}(U^{(j+1)})² ≤ C·H3(j+1)` (`H3(j+1) = ∫(u^{(j+1)})²sin(2θ)^{2(j+1)-4-γ}`) close every
term with `1 ≤ j ≤ k`; `j+1 = 2` is dominated by `H4 = ∫(u'')²sin(2θ)^{-η}`, and `j = 0` by
`H6 = ∫u²`.  For `m = k+1` the term `j = k+1` (from `i = 0`) is handled by the exact Leibniz
relation `x(U/x)^{(k+1)} = U^{(k+1)} - (k+1)(U/x)^{(k)}`, the first piece being exactly the
`H3(k+1)` slot; the second is reduced with the same relation at order `k` (giving `H3(k)`) and the
division inequality at order `k-1`. -/
theorem slice_ang_v_far_live_of_top (k : ℕ) (hk : 2 ≤ k)
    (htop : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      TopCoreB.FarHyp k γ u g →
      (∫ x in (0 : ℝ)..TopCoreB.xEnd,
          (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ C₂ * TopCoreB.FarR k γ u g ∧
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (Set.Ioc 0 TopCoreB.xEnd)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      ∀ m : ℕ, m ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          (Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) ∧
        (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
            (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  -- ### the case `m ≤ k`: the bound is `TopCoreB.far_vBound`
  obtain ⟨C₁, hC₁pos, hLowB⟩ := TopCoreB.far_vBound k hk
  -- ### the integrability for `m ≤ k`
  have hLowInt : ∀ (γ : ℝ) (u g : ℝ → ℝ), TopCoreB.FarHyp k γ u g → ∀ m : ℕ, m ≤ k →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (iteratedDeriv m (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
        TopCoreB.farSet := by
    intro γ u g hF m hm
    exact farVIntLow k hk γ u g hF m hm
  -- ### the case `m = k + 1`: the reflected-window estimate and its integrability
  -- replaced by `obtain ⟨C₂, hC₂pos, hTopX⟩ := farTopXAux k hk` once that module lands
  obtain ⟨C₂, hC₂pos, hTopX⟩ := htop
  have hTopB : ∀ (γ : ℝ) (u g : ℝ → ℝ), TopCoreB.FarHyp k γ u g →
      (∫ θ in TopCoreB.farSet,
          (iteratedDeriv (k + 1) (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
        ≤ C₂ * TopCoreB.FarR k γ u g := by
    intro γ u g hF
    rw [TopCoreB.farSet_LHS_eq k γ (k + 1) u]
    exact (hTopX γ u g hF).1
  have hTopI : ∀ (γ : ℝ) (u g : ℝ → ℝ), TopCoreB.FarHyp k γ u g →
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
          (iteratedDeriv (k + 1) (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
        TopCoreB.farSet := by
    intro γ u g hF
    have hx := (hTopX γ u g hF).2
    have hIcc : MeasureTheory.IntegrableOn
        (fun x : ℝ => (iteratedDeriv (k + 1) (TopCoreB.shiftV u) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Icc 0 TopCoreB.xEnd) :=
      hx.congr_set_ae
        (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := TopCoreB.xEnd)).symm
    refine (integrableOn_farSet_iff (fun θ : ℝ =>
      (iteratedDeriv (k + 1) (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)).2 ?_
    refine hIcc.congr_fun (fun x _ => ?_) measurableSet_Icc
    exact (TopCoreB.farSet_integrand_eq k γ (k + 1) u x).symm
  -- ### assembly
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu hcont hu0 hupi hg hIk2 hIgk hIhigh hI2 hI1 hI0 m hm
  have hF : TopCoreB.FarHyp k γ u g :=
    ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hIk2, hIgk, hIhigh, hI2, hI1, hI0⟩
  have hAng := angRHS_nonneg_prv k γ u g
  by_cases hmk : m ≤ k
  · -- `m ≤ k`
    refine ⟨?_, ?_⟩
    · exact (hLowInt γ u g hF m hmk).congr_fun
        (fun θ _ => (integrand_eq k γ m u θ).symm) measurableSet_Icc
    · rw [farIntegral_eq k γ m u]
      calc (∫ θ in TopCoreB.farSet,
              (iteratedDeriv m (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
          ≤ C₁ * TopCoreB.FarR k γ u g := hLowB γ u g hF m hmk
        _ = C₁ * AngRHS k γ u g := by rw [farR_eq_angRHS]
        _ ≤ (C₁ + C₂) * AngRHS k γ u g :=
            mul_le_mul_of_nonneg_right (by linarith) hAng
  · -- `m = k + 1`
    have hm' : m = k + 1 := by omega
    subst hm'
    refine ⟨?_, ?_⟩
    · exact (hTopI γ u g hF).congr_fun
        (fun θ _ => (integrand_eq k γ (k + 1) u θ).symm) measurableSet_Icc
    · rw [farIntegral_eq k γ (k + 1) u]
      calc (∫ θ in TopCoreB.farSet,
              (iteratedDeriv (k + 1) (TopCoreB.vF u) θ) ^ 2 * TopCoreB.qW k γ θ)
          ≤ C₂ * TopCoreB.FarR k γ u g := hTopB γ u g hF
        _ = C₂ * AngRHS k γ u g := by rw [farR_eq_angRHS]
        _ ≤ (C₁ + C₂) * AngRHS k γ u g :=
            mul_le_mul_of_nonneg_right (by linarith) hAng


end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_step4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Elementary facts about the angular weight `σ = sin(2θ)^{2-γ}` on `Iθ` -/

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Almost every point of `Iθ` lies in the open interval. -/
private lemma ae_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h1 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
      θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun x hx => hx)
  have h2 : (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = (volume : Measure ℝ).restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rwa [h2] at h1

/-- Transferring a pointwise property from `Ioo 0 (π/2)` to `Iθ`. -/
private lemma ae_of_forall_Ioo {P : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), P θ) :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, P θ :=
  ae_Iθ_mem_Ioo.mono fun _ hθ => h _ hθ

private lemma measurable_sig (γ : ℝ) (hγ2 : γ ≤ 3 / 2) :
    Measurable (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
    (fun _ => Or.inr (by linarith))).measurable

/-- The pointwise identity `u''' + g' = sinθ v'' − 4cosθ v' + 5 sinθ v`, `v = u/cos θ`,
used to put the pairing `(tan θ u)''·u'''` into the `v`-form. -/
private lemma T_v_form (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv u)) θ + deriv g θ
        = Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - 4 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          + 5 * Real.sin θ * (u θ / Real.cos θ) := by
  intro θ hθ
  rw [slice_gprime_v_ident u g hu hg θ hθ, (slice_v_identities u hu θ hθ).2.1]
  ring

/-- The elementary arithmetic closing the estimate: from the four coercivity bounds and the
absorbed pairing bound, `∫(u''')²σ` is controlled by `D + B + C₁ + C₀`. -/
private lemma step4_arith {A D B C1 C0 V2 Y2 Y3 G2 Cv Ch Cg Cy : ℝ}
    (hD0 : 0 ≤ D) (hB0 : 0 ≤ B) (hC10 : 0 ≤ C1) (hC00 : 0 ≤ C0)
    (_hCv : 0 < Cv) (hCh : 0 < Ch) (hCg : 0 < Cg) (hCy : 0 < Cy)
    (hV2b : V2 ≤ Cv * (D + B + C1 + C0))
    (hY3b : Y3 ≤ Ch * (C1 + C0))
    (hG2b : G2 ≤ Cg * (D + B + C1 + C0))
    (hY2b : Y2 ≤ Cy * (G2 + B + C1 + C0))
    (hmain : A ≤ (1 / 4) * A + (17 / 8) * D + 72 * C1 + 10 * V2 + 31 * Y2 + 13 * Y3) :
    A ≤ ((4 / 3) * ((17 / 8) + 72 + 10 * Cv + 31 * Cy * (Cg + 1) + 13 * Ch) + 1)
          * (D + B + C1 + C0) := by
  have hRnn : 0 ≤ D + B + C1 + C0 := by linarith
  have hY2R : Y2 ≤ Cy * (Cg + 1) * (D + B + C1 + C0) := by
    nlinarith [hY2b, hG2b, hCy, hCg, hRnn, hD0, hB0, hC10, hC00]
  have hY3R : Y3 ≤ Ch * (D + B + C1 + C0) := by nlinarith [hY3b, hC10, hC00]
  have hstep : A ≤ (1 / 4) * A +
      ((17 / 8) + 72 + 10 * Cv + 31 * Cy * (Cg + 1) + 13 * Ch) * (D + B + C1 + C0) := by
    nlinarith [hmain, hV2b, hY2R, hY3R, hRnn, hD0, hB0, hC10, hC00]
  nlinarith [hstep, hRnn]


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.H2.SupMixedNB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Elementary a.e. facts -/

/-- Almost everywhere on `Iθ = [0,π/2]`, `sin (2σ) > 0`. -/
lemma ae_sin_two_pos :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 < Real.sin (2 * σ) := by
  have h : ∀ᵐ σ ∂(MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))),
      0 < Real.sin (2 * σ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hset : MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0:ℝ)) (b := Real.pi/2))
  rwa [hset] at h

/-- Strong measurability with respect to `volume.restrict Iz` from continuity on the open
half-line `(0,∞)` (which is a.e. equal to `Iz`). -/
lemma aestronglyMeasurable_restrict_Iz {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi (0:ℝ))) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h1 : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hg.aestronglyMeasurable measurableSet_Ioi
  have h2 : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))).symm
  rwa [h2]

/-- `1 ≤ x ^ (-p)` for `0 < x ≤ 1` and `p ≥ 0`. -/
lemma one_le_rpow_neg {x p : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hp : 0 ≤ p) :
    1 ≤ x ^ (-p) := by
  rw [Real.rpow_neg (le_of_lt hx0) p]
  have h1 : x ^ p ≤ 1 := Real.rpow_le_one (le_of_lt hx0) hx1 hp
  have h2 : 0 < x ^ p := Real.rpow_pos_of_pos hx0 p
  exact (one_le_inv₀ h2).mpr h1

/-- `(a / x ^ (c/2)) ^ 2 = a ^ 2 * x ^ (-c)` for `x ≥ 0` and `c ≠ 0`. -/
lemma div_rpow_sq (a x c : ℝ) (hx : 0 ≤ x) (hc : c ≠ 0) :
    (a / x ^ (c / 2)) ^ 2 = a ^ 2 * x ^ (-c) := by
  have h2 : x ^ (-c) = ((x ^ (c/2))⁻¹) ^ 2 := by
    rw [← Real.rpow_neg hx (c / 2)]
    exact (Work.Spaces.bt_rpow_sq c x hx hc).symm
  rw [h2, div_eq_mul_inv, mul_pow]

/-! ## The angular-weight identities -/

/-- `mixed b 1 f z θ = sin(2θ) ∂_θ (D_z^b f)` on the closed quadrant. -/
lemma mixed_one_eq_sin_mul_pth {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (b : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed b 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have hc : Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.DzIter b (Work.Spaces.DthIter 1 f) z θ := by
    have h := Work.Spaces.DthIter_DzIter_comm_eqOn hsm b 1 hy
    simpa [Function.uncurry] using h
  show Work.Spaces.DzIter b (Work.Spaces.DthIter 1 f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
  rw [← hc]
  rfl


/-! ## Continuity and differentiability of the angular slices -/

lemma contDiffOn_slice_DzIter {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (b : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContDiffOn ℝ ⊤ (fun σ : ℝ => Work.Spaces.DzIter b f z σ) (Set.Ioo (-1) (Real.pi/2 + 1)) := by
  have hz1 : (-1:ℝ) < z := by rw [Work.Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter b f) :=
    Work.Spaces.SmoothNbhd.DzIter hsm b
  have hp : ContDiffOn ℝ ⊤ (fun σ : ℝ => (z, σ)) (Set.Ioo (-1) (Real.pi/2 + 1)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := hsm'.comp hp (fun σ hσ => ⟨hz1, hσ⟩)
  simpa [Function.comp_def, Function.uncurry] using h

lemma hasDerivAt_slice_DzIter {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (b : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    HasDerivAt (fun σ => Work.Spaces.DzIter b f z σ)
      (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) θ := by
  have hcd := contDiffOn_slice_DzIter hsm b hz
  have hd : DifferentiableOn ℝ (fun σ => Work.Spaces.DzIter b f z σ)
      (Set.Ioo (-1) (Real.pi/2 + 1)) := hcd.differentiableOn (by simp)
  have hmem : θ ∈ Set.Ioo (-1:ℝ) (Real.pi/2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have := hd.hasDerivAt (isOpen_Ioo.mem_nhds hmem)
  simpa [Work.Spaces.pth] using this

lemma continuousOn_pth_slice {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (b : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) Work.Spaces.Iθ := by
  have hcd := contDiffOn_slice_DzIter hsm b hz
  have hcont := hcd.continuousOn_deriv_of_isOpen isOpen_Ioo le_top
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1:ℝ) (Real.pi/2 + 1) :=
    fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩
  simpa [Work.Spaces.pth] using hcont.mono hsub

/-! ## Pointwise domination of single terms of the `ℋ⁴`-integrand -/

/-- On the open quadrant, `(D_z^j f)² w² ≤ HkIntegrand α 4 f` for `j ≤ 4`. -/
lemma dzIter_sq_w_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ 4) :
    (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    one_le_rpow_neg hsin hs1 Work.Spaces.eta_nonneg
  have hrew : (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta
      (le_of_lt hsin) (ne_of_gt Work.Spaces.eta_pos)]
    ring
  have hzle := Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ j hj
  rw [hrew] at hzle
  calc (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hzle

/-- `(w z)² ≤ (Wt α z θ)²` on the open quadrant. -/
lemma w_sq_le_Wt_sq (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hs := Work.Spaces.bt_sin_nonneg hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    one_le_rpow_neg hsin hs1 (le_of_lt (Work.Spaces.gam_pos hα))
  rw [Work.Spaces.bt_Wt_sq α z θ hα hθ]
  calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)



/-! ## Continuity of the `D_z`-slice of the weighted integrand -/


/-! ## The two `L²` bounds at fixed `z` -/











end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.easySum_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.Transport3Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the weights and the norms -/






/-- The `𝒲^{l,∞}`-norm is nonnegative whenever it is honest. -/
theorem wlInf_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Spaces.WlInfMem α 4 f) :
    0 ≤ Spaces.WlInf α 4 f := by
  rw [Spaces.WlInf]
  exact add_nonneg (Spaces.wlZSum_nonneg α 4 f hmem) (Spaces.wlThSum_nonneg α 4 f hmem)


/-- `n.choose k ≤ 16` for `k ≤ n ≤ 4`. -/
theorem choose_le_sixteen {n k : ℕ} (hn : n ≤ 4) : (n.choose k : ℝ) ≤ 16 := by
  have h1 : ((n.choose k : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_le_two_pow n k
  have h2 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hn
  have h4 : (2 : ℝ) ^ 4 = 16 := by norm_num
  linarith

/-! ## Pointwise bounds for the `f`-factors, in terms of `|f|_{𝒲^{4,∞}}` -/



/-! ## The AM–GM slot bound -/

/-- If `a² ≤ H` and `b² ≤ H` with `a, b ≥ 0` then `a b ≤ H`. -/
theorem mul_self_le_of_sq_le {a b H : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha2 : a ^ 2 ≤ H)
    (hb2 : b ^ 2 ≤ H) : a * b ≤ H := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]


/-! ## The absolute-value forms of the Leibniz summands -/



/-! ## The pointwise bound of the individual summands -/



/-! ## The assembly -/



end Work.FTS.H2.Transport3Aux
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.mx_monomial_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option autoImplicit false



end Work.FTS.H2.Transport3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.DzIter_SR2_le5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false

open Work.FTS.StrongEps.ClassCRHS

/-! ## The level-`5` polynomial data for `SR2`

`DzBoundR2` provides the substitution `x = z/(1+z)` (with `D_z = x(1-x)∂_x`) and the
polynomials `polyR2 i` for `i ≤ 4`, together with their cofactors `AR2 i` satisfying
`polyR2 i x = x²(1-x)·AR2 i x`.  Here we add the missing level: the ordinary derivative
`dpolyR2_5` of `polyR2 4`, the iterate `polyR2_5 x = x(1-x)·(polyR2 4)' x`, and its
cofactor `AR2_5` (of degree `6`, with coefficient `ℓ¹`-norm `318158`). -/

/-- The ordinary derivative of `polyR2 4`
(`(32x² - 746x³ + 4834x⁴ - 13560x⁵ + 18800x⁶ - 12720x⁷ + 3360x⁸)'`). -/
def dpolyR2_5 (x : ℝ) : ℝ :=
  64 * x - 2238 * x ^ 2 + 19336 * x ^ 3 - 67800 * x ^ 4 + 112800 * x ^ 5 - 89040 * x ^ 6
    + 26880 * x ^ 7

/-- The level-`5` iterate `polyR2 5 x = x(1-x)·(polyR2 4)' x` in the variable `x = z/(1+z)`. -/
def polyR2_5 (x : ℝ) : ℝ := x * (1 - x) * dpolyR2_5 x

/-- The cofactor of `polyR2 5`: `polyR2 5 x = x²(1-x)·AR2_5 x`. -/
def AR2_5 (x : ℝ) : ℝ :=
  64 - 2238 * x + 19336 * x ^ 2 - 67800 * x ^ 3 + 112800 * x ^ 4 - 89040 * x ^ 5
    + 26880 * x ^ 6

/-- The polynomial cofactor of `polyR2 5`: `polyR2 5 x = x²(1-x)·AR2_5 x`. -/
lemma factor_polyR2_5 (x : ℝ) : polyR2_5 x = x ^ 2 * (1 - x) * AR2_5 x := by
  simp only [polyR2_5, dpolyR2_5, AR2_5]; ring

/-- The explicit derivative of `polyR2 4`. -/
lemma hasDerivAt_polyR2_four (x : ℝ) :
    HasDerivAt (polyR2 4) (dpolyR2_5 x) x := by
  have h2 : HasDerivAt
      (fun y : ℝ => 32 * y ^ 2 - 746 * y ^ 3 + 4834 * y ^ 4 - 13560 * y ^ 5
        + 18800 * y ^ 6 - 12720 * y ^ 7 + 3360 * y ^ 8)
      (64 * x - 2238 * x ^ 2 + 19336 * x ^ 3 - 67800 * x ^ 4 + 112800 * x ^ 5
        - 89040 * x ^ 6 + 26880 * x ^ 7) x := by
    have hc := (((((((hasDerivAt_pow 2 x).const_mul 32).sub
      ((hasDerivAt_pow 3 x).const_mul 746)).add
      ((hasDerivAt_pow 4 x).const_mul 4834)).sub
      ((hasDerivAt_pow 5 x).const_mul 13560)).add
      ((hasDerivAt_pow 6 x).const_mul 18800)).sub
      ((hasDerivAt_pow 7 x).const_mul 12720)).add
      ((hasDerivAt_pow 8 x).const_mul 3360)
    convert hc using 1
    norm_num
    ring
  simpa only [polyR2, dpolyR2_5] using h2

/-- The cofactor `AR2_5` is bounded by `318158` on `[0,1]` (its coefficient `ℓ¹`-norm is
`64 + 2238 + 19336 + 67800 + 112800 + 89040 + 26880 = 318158`). -/
lemma cof_bound_5 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : |AR2_5 x| ≤ 318158 := by
  have h2 : x ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hx0 hx1
  have h3 : x ^ 3 ≤ 1 := pow_le_one₀ (n := 3) hx0 hx1
  have h4 : x ^ 4 ≤ 1 := pow_le_one₀ (n := 4) hx0 hx1
  have h5 : x ^ 5 ≤ 1 := pow_le_one₀ (n := 5) hx0 hx1
  have h6 : x ^ 6 ≤ 1 := pow_le_one₀ (n := 6) hx0 hx1
  have g2 : 0 ≤ x ^ 2 := pow_nonneg hx0 2
  have g3 : 0 ≤ x ^ 3 := pow_nonneg hx0 3
  have g4 : 0 ≤ x ^ 4 := pow_nonneg hx0 4
  have g5 : 0 ≤ x ^ 5 := pow_nonneg hx0 5
  have g6 : 0 ≤ x ^ 6 := pow_nonneg hx0 6
  simp only [AR2_5]
  rw [abs_le]
  constructor <;> nlinarith

/-- The `5`-th `D_z`-iterate of `SR2`, expressed through the substitution `x = z/(1+z)`. -/
lemma DzdIter_SR2_eq5 (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 5 SR2 z = polyR2_5 (xtR2 z) := by
  have hz' : z ≠ -1 := by intro h; exact hz (by linarith)
  have hev : Work.Elliptic.DzdIter 4 SR2 =ᶠ[nhds z] fun w => polyR2 4 (xtR2 w) := by
    filter_upwards [eventually_ne_nhds hz'] with w hw
    exact DzdIter_SR2_eq 4 (le_refl 4) w (by intro h; exact hw (by linarith))
  have hcomp : deriv (fun w => polyR2 4 (xtR2 w)) z
      = dpolyR2_5 (xtR2 z) * (1 / (1 + z) ^ 2) := by
    have hX := hasDerivAt_xtR2 z hz
    have hp := hasDerivAt_polyR2_four (xtR2 z)
    exact (hp.comp z hX).deriv
  rw [show Work.Elliptic.DzdIter 5 SR2 z
        = z * deriv (Work.Elliptic.DzdIter 4 SR2) z from rfl, hev.deriv_eq, hcomp]
  rw [show z * (dpolyR2_5 (xtR2 z) * (1 / (1 + z) ^ 2))
        = xtR2 z * (1 - xtR2 z) * dpolyR2_5 (xtR2 z) from by
      calc z * (dpolyR2_5 (xtR2 z) * (1 / (1 + z) ^ 2))
            = (z * (1 / (1 + z) ^ 2)) * dpolyR2_5 (xtR2 z) := by ring
        _ = (xtR2 z * (1 - xtR2 z)) * dpolyR2_5 (xtR2 z) := by rw [mul_xtR2 z hz]]
  simp only [polyR2_5]

/-- `|D_z^5 SR2 z| ≤ 318158 z²/(1+z)³` for `z ≥ 0`. -/
lemma DzdIter_SR2_bound5 (z : ℝ) (hz0 : 0 ≤ z) :
    |Work.Elliptic.DzdIter 5 SR2 z| ≤ 318158 * z ^ 2 / (1 + z) ^ 3 := by
  have hz : 1 + z ≠ 0 := by positivity
  rw [DzdIter_SR2_eq5 z hz, factor_polyR2_5 (xtR2 z)]
  have hx0 : 0 ≤ xtR2 z := by simp only [xtR2]; positivity
  have hx1 : xtR2 z ≤ 1 := by
    simp only [xtR2]
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]
    linarith
  have hnn : 0 ≤ (xtR2 z) ^ 2 * (1 - xtR2 z) := by
    nlinarith [sq_nonneg (xtR2 z), hx1]
  have hcof := cof_bound_5 (xtR2 z) hx0 hx1
  calc |(xtR2 z) ^ 2 * (1 - xtR2 z) * AR2_5 (xtR2 z)|
      = (xtR2 z) ^ 2 * (1 - xtR2 z) * |AR2_5 (xtR2 z)| := by
        rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ (xtR2 z) ^ 2 * (1 - xtR2 z) * 318158 := mul_le_mul_of_nonneg_left hcof hnn
    _ = 318158 * z ^ 2 / (1 + z) ^ 3 := by rw [sq_xtR2 z hz]; ring

/-- The level-`4` bound with the larger constant `318158`. -/
lemma bound_of_le4 (i : ℕ) (hi : i ≤ 4) (z : ℝ) (hz0 : 0 ≤ z) :
    |Work.Elliptic.DzdIter i SR2 z| ≤ 318158 * z ^ 2 / (1 + z) ^ 3 := by
  refine le_trans (DzdIter_SR2_bound i hi z hz0) ?_
  have hden : 0 ≤ (1 + z) ^ 3 := by positivity
  have hnum : 30000 * z ^ 2 ≤ 318158 * z ^ 2 := by nlinarith [sq_nonneg z]
  exact div_le_div_of_nonneg_right hnum hden

/-- The level-`5` radial iterates of `SR2 z = 2z²(1-z)/(1+z)⁴` are bounded by `C·z²/(1+z)³`
(the level-`4` version with `C = 30000` is `ClassCRHS.DzBoundR2`; `DzdIter i SR2 = z²P_i(z)/(1+z)^(4+i)`
with `deg P_i ≤ i+1`).  `DzBoundR2`'s file carries the useful substitution `x = z/(1+z)`,
under which `D_z = x(1-x)∂_x`, with the explicit polynomials `polyR2`/`AR2`; for `i = 5` one adds
`polyR2 5 = x(1-x)(polyR2 4)'` and its cofactor `AR2 5`.
The private lemmas of `DzBoundR2` may be copied into the new file (do not edit that file). -/
theorem DzIter_SR2_le5 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR2 z| ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  refine ⟨318158, by norm_num, fun i hi z hz0 => ?_⟩
  by_cases h4 : i ≤ 4
  · exact bound_of_le4 i h4 z hz0
  · have h5 : i = 5 := by omega
    subst h5
    exact DzdIter_SR2_bound5 z hz0

end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.StabilityFar.Decay

theorem timeDeriv_eq_zero_of_notMem_closedBall {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {R t ε : ℝ}
    (hdc : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      HasDerivAt (fun s' => ω y s') (FiniteTimeSingularity.timeDeriv ω y s) s)
    (hsupp : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      ω y s ≠ 0 → y ∈ Metric.closedBall 0 R)
    {s : ℝ} (hs : s ∈ Set.Ioo (t - ε) (t + ε)) {y : Work.StabilityFar.R3}
    (hy : y ∉ Metric.closedBall 0 R) :
    FiniteTimeSingularity.timeDeriv ω y s = 0 := by
  refine Work.StabilityFar.timeDeriv_eq_zero_of_eventuallyEq_zero ?_
  filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs'
  by_contra hne
  exact hy (hsupp s' hs' y hne)

end Work.StabilityFar.Decay
end
