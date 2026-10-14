import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Elliptic.WtoW_g_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary analytic facts -/









/-! ## The coefficients vanish above the diagonal -/



/-! ## The algebraic core of the induction step -/


/-! ## The identity `sin(2θ) D_θ^q(∂_θ g) = Σ_j c_{q,j} D_θ^{j+1} g` -/


/-! ## Pushing `∂_z^m` through the identity -/


/-! ## The final estimate -/


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.endpointParamRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues


end Work.EllipticEst.Core.i0Aux.EndpointValues
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.ibpSurr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## The logarithmic derivative of the weight `thEta`

Throughout we use that `thEta θ = sin(2θ)^{-η}` satisfies `thEta' = -qTh · thEta` on the open
interval `(0, π/2)`, where `qTh θ = 2η cot(2θ)`.  This is the identity which produces the
`qTh`-correction in the integration by parts. -/

/-- `deriv thEta θ = -(qTh θ) * thEta θ` on `(0, π/2)`. -/
private theorem thEta_hasDerivAt {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt Work.FTS.EllipticEst.thEta
      (-(qTh θ) * Work.FTS.EllipticEst.thEta θ) θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hderiv : (2 * Real.cos (2 * θ) * (-(Work.Spaces.eta)))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta) - 1)
      = -(qTh θ) * Work.FTS.EllipticEst.thEta θ := by
    rw [qTh, Real.cot_eq_cos_div_sin, Work.FTS.EllipticEst.thEta]
    rw [show -(Work.Spaces.eta) - 1 = -(Work.Spaces.eta) + (-1 : ℝ) by ring,
      Real.rpow_add hs, Real.rpow_neg_one]
    field_simp
  exact (Work.FTS.H2.hasDerivAt_sin_rpow_neg Work.Spaces.eta θ hθ).congr_deriv hderiv

/-! ## Reducing a set integral over `Iθ` to an interval integral on a subinterval -/

/-- If `h` vanishes to the left of `a` and to the right of `b` (with `0 ≤ a ≤ b ≤ π/2`), then
its integral over `Iθ = [0, π/2]` is the interval integral over `[a, b]`. -/
private theorem setIntegral_Iθ_eq_interval_of_eq_zero_off {h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (h0 : 0 ≤ a) (hpi : b ≤ Real.pi / 2)
    (hlo : ∀ θ, θ < a → h θ = 0) (hhi : ∀ θ, b < θ → h θ = 0) :
    (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in a..b, h θ := by
  have ht : MeasurableSet Work.Spaces.Iθ := by
    show MeasurableSet (Set.Icc 0 (Real.pi / 2))
    exact isClosed_Icc.measurableSet
  have hst : Set.Icc a b ⊆ Work.Spaces.Iθ := by
    show Set.Icc a b ⊆ Set.Icc 0 (Real.pi / 2)
    exact fun x hx => ⟨le_trans h0 hx.1, le_trans hx.2 hpi⟩
  have hv : ∀ x ∈ Work.Spaces.Iθ \ Set.Icc a b, h x = 0 := by
    rintro x ⟨-, hx2⟩
    rw [Set.mem_Icc, not_and_or] at hx2
    rcases hx2 with hh | hh
    · exact hlo x (not_le.mp hh)
    · exact hhi x (not_le.mp hh)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (t := Work.Spaces.Iθ)
    (s := Set.Icc a b) ht hst hv,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-! ## Differentiability of the surrogate and of the primitive of the integration by parts -/

/-- The derivative of the surrogate is differentiable everywhere, with derivative the second
derivative. -/
private theorem surr_deriv_hasDerivAt {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ} (hψ : IsBump ψ C)
    (hL : 0 < L) (θ : ℝ) :
    HasDerivAt (deriv (surrFun ψ F₀ F₁ L)) (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) θ := by
  have hℓ : ContDiff ℝ 2 (surrFun ψ F₀ F₁ L) := surr_smooth hψ (ne_of_gt hL)
  have h1 : ContDiff ℝ 1 (deriv (surrFun ψ F₀ F₁ L)) := hℓ.deriv'
  exact (h1.differentiable (by norm_num) θ).hasDerivAt

/-- The primitive `v θ = (surrFun …)' θ · thEta θ` of the integration by parts: on `(0, π/2)`
its derivative is `(surrFun …)'' θ · thEta θ - (surrFun …)' θ · qTh θ · thEta θ`. -/
private theorem surr_deriv_mul_thEta_hasDerivAt {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ} (hψ : IsBump ψ C)
    (hL : 0 < L) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt
      (fun t : ℝ => deriv (surrFun ψ F₀ F₁ L) t * Work.FTS.EllipticEst.thEta t)
      (deriv (deriv (surrFun ψ F₀ F₁ L)) θ * Work.FTS.EllipticEst.thEta θ
        - deriv (surrFun ψ F₀ F₁ L) θ * qTh θ * Work.FTS.EllipticEst.thEta θ) θ := by
  have h1 : HasDerivAt (deriv (surrFun ψ F₀ F₁ L))
      (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) θ := surr_deriv_hasDerivAt hψ hL θ
  have h2 : HasDerivAt Work.FTS.EllipticEst.thEta
      (-(qTh θ) * Work.FTS.EllipticEst.thEta θ) θ := thEta_hasDerivAt hθ
  exact (h1.mul h2).congr_deriv (by ring)

/-! ## The integration by parts against the surrogate -/

theorem ibpSurr {f : ℝ → ℝ} {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ,
        deriv f θ * deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ *
          Work.FTS.EllipticEst.thEta θ)
      = - (∫ θ in Work.Spaces.Iθ,
            f θ * deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ *
              Work.FTS.EllipticEst.thEta θ)
        + (∫ θ in Work.Spaces.Iθ,
            f θ * deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ *
              Work.EllipticEst.Core.i0Aux.qTh θ * Work.FTS.EllipticEst.thEta θ) := by
  -- ## Geometry of the cut `[L/8, π/2 - L/8]`, which contains the support of `(surrFun …)'`.
  have hL8 : (0 : ℝ) < L / 8 := by linarith
  have hL8lt : L / 8 < L / 4 := by linarith
  have hbgt : Real.pi / 2 - L / 4 < Real.pi / 2 - L / 8 := by linarith
  have hle : L / 8 ≤ Real.pi / 2 - L / 8 := by linarith [hLp, Real.pi_pos]
  have hsub : Set.Icc (L / 8) (Real.pi / 2 - L / 8) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- ## Vanishing of the surrogate derivatives off the cut
  have hzero_left : ∀ θ, θ < L / 8 → deriv (surrFun ψ F₀ F₁ L) θ = 0 := fun θ hθ =>
    deriv_surr_eq_zero_of_lt hψ hL hLp (by linarith)
  have hzero_right : ∀ θ, Real.pi / 2 - L / 8 < θ → deriv (surrFun ψ F₀ F₁ L) θ = 0 :=
    fun θ hθ => deriv_surr_eq_zero_of_gt hψ hL hLp (by linarith)
  have hzero2_left : ∀ θ, θ < L / 8 → deriv (deriv (surrFun ψ F₀ F₁ L)) θ = 0 := fun θ hθ =>
    deriv2_surr_eq_zero_of_lt hψ hL hLp (by linarith)
  have hzero2_right : ∀ θ, Real.pi / 2 - L / 8 < θ →
      deriv (deriv (surrFun ψ F₀ F₁ L)) θ = 0 :=
    fun θ hθ => deriv2_surr_eq_zero_of_gt hψ hL hLp (by linarith)
  -- ## Pass from `Iθ` to the cut, using that all three integrands vanish off the cut.
  have hredA : (∫ θ in Work.Spaces.Iθ,
        deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ * thEta θ)
      = ∫ θ in (L / 8)..(Real.pi / 2 - L / 8),
          deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ * thEta θ :=
    setIntegral_Iθ_eq_interval_of_eq_zero_off hle hL8.le (by linarith)
      (fun θ hθ => by rw [hzero_left θ hθ]; ring)
      (fun θ hθ => by rw [hzero_right θ hθ]; ring)
  have hredB : (∫ θ in Work.Spaces.Iθ,
        f θ * deriv (deriv (surrFun ψ F₀ F₁ L)) θ * thEta θ)
      = ∫ θ in (L / 8)..(Real.pi / 2 - L / 8),
          f θ * deriv (deriv (surrFun ψ F₀ F₁ L)) θ * thEta θ :=
    setIntegral_Iθ_eq_interval_of_eq_zero_off hle hL8.le (by linarith)
      (fun θ hθ => by rw [hzero2_left θ hθ]; ring)
      (fun θ hθ => by rw [hzero2_right θ hθ]; ring)
  have hredD : (∫ θ in Work.Spaces.Iθ,
        f θ * deriv (surrFun ψ F₀ F₁ L) θ * qTh θ * thEta θ)
      = ∫ θ in (L / 8)..(Real.pi / 2 - L / 8),
          f θ * deriv (surrFun ψ F₀ F₁ L) θ * qTh θ * thEta θ :=
    setIntegral_Iθ_eq_interval_of_eq_zero_off hle hL8.le (by linarith)
      (fun θ hθ => by rw [hzero_left θ hθ]; ring)
      (fun θ hθ => by rw [hzero_right θ hθ]; ring)
  -- ## Regularity on the cut
  have hd2cont : Continuous (deriv (deriv (surrFun ψ F₀ F₁ L))) := by
    have h1 : ContDiff ℝ 1 (deriv (surrFun ψ F₀ F₁ L)) :=
      (surr_smooth hψ (ne_of_gt hL)).deriv'
    exact h1.continuous_deriv_one
  have hd1cont : Continuous (deriv (surrFun ψ F₀ F₁ L)) := by
    have h1 : ContDiff ℝ 1 (deriv (surrFun ψ F₀ F₁ L)) :=
      (surr_smooth hψ (ne_of_gt hL)).deriv'
    exact h1.continuous
  have hfcont : ContinuousOn f (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) :=
    hf.continuousOn.mono hsub
  have hdfcont : ContinuousOn (deriv f) (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hwcont : ContinuousOn thEta (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) :=
    (Work.EllipticEst.Core.thEtaFacts.2.2.2).mono hsub
  have hqcont : ContinuousOn qTh (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) := by
    have hcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ))
        (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) :=
      Real.continuous_cos.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) :=
      Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
    have hne : ∀ θ ∈ Set.Icc (L / 8) (Real.pi / 2 - L / 8), Real.sin (2 * θ) ≠ 0 := by
      intro θ hθ
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
    have hdiv := hcos.div hsin hne
    have hmain : ContinuousOn
        (fun θ : ℝ => 2 * Work.Spaces.eta * (Real.cos (2 * θ) / Real.sin (2 * θ)))
        (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) := continuousOn_const.mul hdiv
    refine hmain.congr ?_
    intro θ _
    rw [qTh, Real.cot_eq_cos_div_sin]
  -- ## Interval integrability of the derivative functions
  have huIcc : ∀ {u : ℝ → ℝ}, ContinuousOn u (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) →
      ContinuousOn u (Set.uIcc (L / 8) (Real.pi / 2 - L / 8)) := by
    intro u hu
    rwa [uIcc_of_le hle]
  have hu' : IntervalIntegrable (deriv f) volume (L / 8) (Real.pi / 2 - L / 8) :=
    (huIcc hdfcont).intervalIntegrable
  have hv' : IntervalIntegrable
      (fun x : ℝ => deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x
        - deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x)
      volume (L / 8) (Real.pi / 2 - L / 8) := by
    have hcont : ContinuousOn
        (fun x : ℝ => deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x
          - deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x)
        (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) :=
      (hd2cont.continuousOn.mul hwcont).sub ((hd1cont.continuousOn.mul hqcont).mul hwcont)
    exact (huIcc hcont).intervalIntegrable
  -- ## The pointwise derivative hypotheses on the cut
  have hderf : ∀ x ∈ Set.uIcc (L / 8) (Real.pi / 2 - L / 8), HasDerivAt f (deriv f x) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    exact ((hf.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt
      (by norm_num)).hasDerivAt
  have hderv : ∀ x ∈ Set.uIcc (L / 8) (Real.pi / 2 - L / 8),
      HasDerivAt (fun t : ℝ => deriv (surrFun ψ F₀ F₁ L) t * thEta t)
        (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x
          - deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    exact surr_deriv_mul_thEta_hasDerivAt hψ hL (hsub hx)
  -- ## Integrability of the two summands of the derivative of the primitive
  have hPint : IntervalIntegrable
      (fun x : ℝ => f x * (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x))
      volume (L / 8) (Real.pi / 2 - L / 8) := by
    have hcont : ContinuousOn
        (fun x : ℝ => f x * (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x))
        (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) :=
      hfcont.mul (hd2cont.continuousOn.mul hwcont)
    exact (huIcc hcont).intervalIntegrable
  have hQint : IntervalIntegrable
      (fun x : ℝ => f x * (deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x))
      volume (L / 8) (Real.pi / 2 - L / 8) := by
    have hcont : ContinuousOn
        (fun x : ℝ => f x * (deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x))
        (Set.Icc (L / 8) (Real.pi / 2 - L / 8)) :=
      hfcont.mul ((hd1cont.continuousOn.mul hqcont).mul hwcont)
    exact (huIcc hcont).intervalIntegrable
  -- ## The integration by parts on the cut: the boundary terms vanish
  have hba : deriv (surrFun ψ F₀ F₁ L) (L / 8) * thEta (L / 8) = 0 := by
    rw [deriv_surr_eq_zero_of_lt hψ hL hLp hL8lt]
    ring
  have hbb : deriv (surrFun ψ F₀ F₁ L) (Real.pi / 2 - L / 8) * thEta (Real.pi / 2 - L / 8) = 0 := by
    rw [deriv_surr_eq_zero_of_gt hψ hL hLp hbgt]
    ring
  have hIBP' : (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
        f x * (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x
          - deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x))
      = - ∫ x in (L / 8)..(Real.pi / 2 - L / 8),
          deriv f x * (deriv (surrFun ψ F₀ F₁ L) x * thEta x) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := f) (u' := deriv f)
      (v := fun t : ℝ => deriv (surrFun ψ F₀ F₁ L) t * thEta t)
      (v' := fun t : ℝ => deriv (deriv (surrFun ψ F₀ F₁ L)) t * thEta t
        - deriv (surrFun ψ F₀ F₁ L) t * qTh t * thEta t)
      hderf hderv hu' hv'
    simp only [hba, hbb, mul_zero, zero_sub, neg_zero] at h
    exact h
  -- ## The split of the integral of the primitive's derivative
  have hsplit : (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
        f x * (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x
          - deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x))
      = (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
            f x * (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x))
        - (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
            f x * (deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x)) := by
    have h1 : (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
          f x * (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x
            - deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x))
        = ∫ x in (L / 8)..(Real.pi / 2 - L / 8),
            (f x * (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x)
              - f x * (deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x)) :=
      intervalIntegral.integral_congr (fun x _ => by ring)
    rw [h1, intervalIntegral.integral_sub hPint hQint]
  -- ## Rewriting the four integrals in the associativity of the statement
  have hconvB : (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
        f x * (deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x))
      = ∫ x in (L / 8)..(Real.pi / 2 - L / 8),
          f x * deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  have hconvD : (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
        f x * (deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x))
      = ∫ x in (L / 8)..(Real.pi / 2 - L / 8),
          f x * deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  have hconvA : (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
        deriv f x * (deriv (surrFun ψ F₀ F₁ L) x * thEta x))
      = ∫ x in (L / 8)..(Real.pi / 2 - L / 8),
          deriv f x * deriv (surrFun ψ F₀ F₁ L) x * thEta x :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  -- ## Assembly
  have hkey : (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
        deriv f x * deriv (surrFun ψ F₀ F₁ L) x * thEta x)
      = - (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
            f x * deriv (deriv (surrFun ψ F₀ F₁ L)) x * thEta x)
        + (∫ x in (L / 8)..(Real.pi / 2 - L / 8),
            f x * deriv (surrFun ψ F₀ F₁ L) x * qTh x * thEta x) := by
    linarith [hsplit, hIBP', hconvA, hconvB, hconvD]
  rw [hredA, hredB, hredD]
  exact hkey

end

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

variable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}

/-! ## 0. Elementary `rpow` bookkeeping -/

/-- `L^{-k} L^{-η} L = L^{-(k + η - 1)}` for `L > 0`. -/
lemma rpow_mul_L {L : ℝ} (hL : 0 < L) (k : ℝ) :
    L ^ (-k) * L ^ (-(Work.Spaces.eta)) * L = L ^ (-(k + Work.Spaces.eta - 1)) := by
  have h : L ^ (-(k + Work.Spaces.eta - 1))
      = L ^ (-k) * L ^ (-(Work.Spaces.eta)) * L := by
    rw [show -(k + Work.Spaces.eta - 1) = -k + (-(Work.Spaces.eta) + 1) by ring,
      Real.rpow_add hL, Real.rpow_add hL, Real.rpow_one]
    ring
  exact h.symm


/-- `(x/L)² = x² L^{-2}` for `L > 0`. -/
lemma sq_div_eq {L x : ℝ} (hL : 0 < L) : (x / L) ^ 2 = x ^ 2 * L ^ (-2 : ℝ) := by
  have h : L ^ (-2 : ℝ) = ((L : ℝ) ^ 2)⁻¹ := by
    have he : (-2 : ℝ) = -((2 : ℕ) : ℝ) := by norm_num
    rw [he, Real.rpow_neg hL.le ((2 : ℕ) : ℝ), Real.rpow_natCast]
  rw [div_pow, div_eq_mul_inv, ← h]

/-- `(x/L²)² = x² L^{-4}` for `L > 0`. -/
lemma sq_div_sq_eq {L x : ℝ} (hL : 0 < L) : (x / L ^ 2) ^ 2 = x ^ 2 * L ^ (-4 : ℝ) := by
  have h : L ^ (-4 : ℝ) = ((L : ℝ) ^ 4)⁻¹ := by
    have he : (-4 : ℝ) = -((4 : ℕ) : ℝ) := by norm_num
    rw [he, Real.rpow_neg hL.le ((4 : ℕ) : ℝ), Real.rpow_natCast]
  rw [div_pow, ← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, div_eq_mul_inv, ← h]

/-- `(a/L)² (b/L)² = a² b² L^{-4}` for `L > 0`. -/
lemma sq_mul_sq_div {L a b : ℝ} (hL : 0 < L) :
    (a / L) ^ 2 * (b / L) ^ 2 = a ^ 2 * b ^ 2 * L ^ (-4 : ℝ) := by
  have h : L ^ (-4 : ℝ) = L ^ (-2 : ℝ) * L ^ (-2 : ℝ) := by
    rw [show (-4 : ℝ) = -2 + -2 by norm_num, Real.rpow_add hL]
  rw [sq_div_eq hL, sq_div_eq hL,
    show a ^ 2 * L ^ (-2 : ℝ) * (b ^ 2 * L ^ (-2 : ℝ))
      = a ^ 2 * b ^ 2 * (L ^ (-2 : ℝ) * L ^ (-2 : ℝ)) by ring, ← h]

/-! ## 1. The angular tails of `thEta` -/

/-- `thEta` is invariant under `θ ↦ π/2 - θ`. -/
lemma thEta_reflect (x : ℝ) :
    Work.FTS.EllipticEst.thEta (Real.pi / 2 - x) = Work.FTS.EllipticEst.thEta x := by
  simp only [Work.FTS.EllipticEst.thEta]
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

/-- Set integrals over `Icc a b` are interval integrals. -/
private lemma setIntegral_Icc_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]

/-- Jordan's inequality for the weight: on `[0, π/4]`,
`sin(2x)^{-η} ≤ (π/4)^η x^{-η}`. -/
lemma sin_two_rpow_eta_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
      ≤ (Real.pi / 4) ^ Work.Spaces.eta * x ^ (-(Work.Spaces.eta)) := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h
    rw [mul_zero, Real.sin_zero,
      Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : (-(Work.Spaces.eta)) ≠ 0), mul_zero]
  · have h2x0 : 0 ≤ 2 * x := by linarith
    have h2x1 : 2 * x ≤ Real.pi / 2 := by linarith [hx1, Real.pi_pos]
    have hj := Real.mul_le_sin h2x0 h2x1
    have hjeq : 2 / Real.pi * (2 * x) = (4 / Real.pi) * x := by ring
    rw [hjeq] at hj
    have hpos : 0 < (4 / Real.pi) * x := by positivity
    have key := Real.rpow_le_rpow_of_nonpos hpos hj
      (show -(Work.Spaces.eta) ≤ 0 by linarith [Work.Spaces.eta_pos])
    have hcoef : (4 / Real.pi : ℝ) ^ (-(Work.Spaces.eta)) = (Real.pi / 4) ^ Work.Spaces.eta := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
        ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) Work.Spaces.eta, inv_div]
    have hmr : ((4 / Real.pi) * x) ^ (-(Work.Spaces.eta))
        = (Real.pi / 4) ^ Work.Spaces.eta * x ^ (-(Work.Spaces.eta)) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) (le_of_lt h), hcoef]
    rw [hmr] at key
    exact key

/-- The left tail: `∫_0^{L/2} sin(2θ)^{-η} dθ ≤ 200 L^{1-η}`. -/
lemma thEta_tail_left {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta) := by
  have hhalf : (0 : ℝ) ≤ L / 2 := by linarith
  have hMint : IntegrableOn
      (fun θ : ℝ => (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (L / 2)) := by
    have h1 : IntegrableOn (fun θ : ℝ => θ ^ (-(Work.Spaces.eta))) (Set.Ioo (0 : ℝ) (L / 2)) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hhalf).mp
        (intervalIntegral.intervalIntegrable_rpow' (r := -(Work.Spaces.eta)) (a := 0) (b := L / 2)
          (by linarith [Work.Spaces.eta_lt_one]))
    exact h1.const_mul _
  have hcomp : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (L / 2),
          (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)) := by
    refine integral_mono_of_nonneg ?_ hMint ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, hLp, Real.pi_pos])) _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact sin_two_rpow_eta_le ⟨le_of_lt hθ.1, by linarith [hθ.2, hLp]⟩
  have hMval : (∫ θ in Set.Ioo (0 : ℝ) (L / 2),
        (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)))
      = (Real.pi / 4) ^ Work.Spaces.eta
          * ((L / 2) ^ (1 - Work.Spaces.eta) / (1 - Work.Spaces.eta)) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hhalf]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_rpow (Or.inl (by linarith [Work.Spaces.eta_lt_one]))]
    rw [show (-(Work.Spaces.eta) + 1 : ℝ) = 1 - Work.Spaces.eta by ring]
    rw [Real.zero_rpow (by linarith [Work.Spaces.eta_lt_one] : (1 : ℝ) - Work.Spaces.eta ≠ 0)]
    ring
  have hIcc : (∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  -- arithmetic
  have ha1 : (Real.pi / 4) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (by positivity) (by linarith [Real.pi_lt_four]) (le_of_lt Work.Spaces.eta_pos)
  have hbc : (L / 2) ^ (1 - Work.Spaces.eta) ≤ L ^ (1 - Work.Spaces.eta) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith [Work.Spaces.eta_lt_one])
  have hk0 : (0 : ℝ) < 1 - Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hc0 : (0 : ℝ) ≤ L ^ (1 - Work.Spaces.eta) := Real.rpow_nonneg hL.le _
  have hb0 : (0 : ℝ) ≤ (L / 2) ^ (1 - Work.Spaces.eta) := Real.rpow_nonneg (by linarith) _
  rw [hIcc]
  refine hcomp.trans ?_
  rw [hMval]
  suffices hkey : (Real.pi / 4) ^ Work.Spaces.eta
        * ((L / 2) ^ (1 - Work.Spaces.eta) / (1 - Work.Spaces.eta)) * (1 - Work.Spaces.eta)
      ≤ (200 * L ^ (1 - Work.Spaces.eta)) * (1 - Work.Spaces.eta) by
    exact le_of_mul_le_mul_right hkey hk0
  have hLHS : (Real.pi / 4) ^ Work.Spaces.eta
        * ((L / 2) ^ (1 - Work.Spaces.eta) / (1 - Work.Spaces.eta)) * (1 - Work.Spaces.eta)
      = (Real.pi / 4) ^ Work.Spaces.eta * (L / 2) ^ (1 - Work.Spaces.eta) := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hk0)]
  have hRHS : (200 * L ^ (1 - Work.Spaces.eta)) * (1 - Work.Spaces.eta)
      = 2 * L ^ (1 - Work.Spaces.eta) := by
    rw [show (1 : ℝ) - Work.Spaces.eta = 1 / 100 by rw [Work.Spaces.eta]; norm_num]
    ring
  rw [hLHS, hRHS]
  calc (Real.pi / 4) ^ Work.Spaces.eta * (L / 2) ^ (1 - Work.Spaces.eta)
      ≤ 1 * L ^ (1 - Work.Spaces.eta) := mul_le_mul ha1 hbc hb0 (by norm_num)
    _ = L ^ (1 - Work.Spaces.eta) := one_mul _
    _ ≤ 2 * L ^ (1 - Work.Spaces.eta) := by nlinarith [hc0]

/-- The right tail: `∫_{π/2-L/2}^{π/2} sin(2θ)^{-η} dθ ≤ 200 L^{1-η}`. -/
lemma thEta_tail_right {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta) := by
  have hb : Real.pi / 2 - L / 2 ≤ Real.pi / 2 := by linarith [hLp, Real.pi_pos]
  have heq : (∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2),
        Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ := by
    rw [setIntegral_Icc_eq_intervalIntegral hb, setIntegral_Icc_eq_intervalIntegral (by linarith)]
    have h1 : (∫ θ in (Real.pi / 2 - L / 2)..(Real.pi / 2), Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in (Real.pi / 2 - L / 2)..(Real.pi / 2),
            Work.FTS.EllipticEst.thEta (Real.pi / 2 - θ) := by
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      exact (thEta_reflect θ).symm
    rw [h1, intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => Work.FTS.EllipticEst.thEta x) (Real.pi / 2),
      show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring,
      show Real.pi / 2 - (Real.pi / 2 - L / 2) = L / 2 by ring]
  rw [heq]
  exact thEta_tail_left hL hLp

/-! ## 2. The two shells -/

/-- The union of the two shells carrying the derivatives of the surrogate:
`[L/4, L/2] ∪ [π/2 - L/2, π/2 - L/4]`. -/
def shells (L : ℝ) : Set ℝ :=
  Set.Icc (L / 4) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2 - L / 4)

lemma shells_measurable (L : ℝ) : MeasurableSet (shells L) := by
  rw [shells]
  measurability

lemma shells_subset {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    shells L ⊆ Set.Icc (L / 4) (Real.pi / 2 - L / 4) := by
  intro x hx
  rw [shells] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, by linarith [h2, hLp, Real.pi_pos]⟩
  · exact ⟨by linarith [h1, hLp, Real.pi_pos], h2⟩

lemma shells_subset_Iθ {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    shells L ⊆ Work.Spaces.Iθ := by
  intro x hx
  have h := shells_subset hL hLp hx
  rw [Work.Spaces.Iθ]
  exact ⟨by linarith [h.1, hL], by linarith [h.2, Real.pi_pos]⟩

/-- On the shells the weight `sin(2θ)` is bounded below by `L/π`. -/
lemma sin_shell_le {L θ : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) (hθ : θ ∈ shells L) :
    L / Real.pi ≤ Real.sin (2 * θ) := by
  rw [shells] at hθ
  have hcoef : (0 : ℝ) < 2 / Real.pi := by positivity
  rcases hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h2θ0 : 0 ≤ 2 * θ := by linarith [h1, hL]
    have h2θ1 : 2 * θ ≤ Real.pi / 2 := by linarith [h2, hLp, Real.pi_pos]
    have hj := Real.mul_le_sin h2θ0 h2θ1
    calc L / Real.pi = 2 / Real.pi * (L / 2) := by ring
      _ ≤ 2 / Real.pi * (2 * θ) := mul_le_mul_of_nonneg_left (by linarith [h1]) hcoef.le
      _ ≤ Real.sin (2 * θ) := hj
  · have hy0 : 0 ≤ Real.pi - 2 * θ := by linarith [h2, Real.pi_pos]
    have hy1 : Real.pi - 2 * θ ≤ Real.pi / 2 := by linarith [h1]
    have hj := Real.mul_le_sin hy0 hy1
    have hsin : Real.sin (2 * θ) = Real.sin (Real.pi - 2 * θ) :=
      (Real.sin_pi_sub (2 * θ)).symm
    rw [hsin]
    calc L / Real.pi = 2 / Real.pi * (L / 2) := by ring
      _ ≤ 2 / Real.pi * (Real.pi - 2 * θ) :=
          mul_le_mul_of_nonneg_left (by linarith [h1, h2]) hcoef.le
      _ ≤ Real.sin (Real.pi - 2 * θ) := hj

/-- On the shells the weight is bounded by `π^η L^{-η}`. -/
lemma shell_thEta_le {L θ : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) (hθ : θ ∈ shells L) :
    Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)) := by
  have hsin := sin_shell_le hL hLp hθ
  have hkey := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < L / Real.pi) hsin
    (show -(Work.Spaces.eta) ≤ 0 by linarith [Work.Spaces.eta_pos])
  have hcoef : (L / Real.pi) ^ (-(Work.Spaces.eta))
      = Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ L / Real.pi),
      Real.div_rpow hL.le (le_of_lt Real.pi_pos), div_eq_mul_inv, mul_inv, inv_inv,
      ← Real.rpow_neg hL.le]
    ring
  rw [hcoef] at hkey
  exact hkey

/-- On the shells the logarithmic derivative factor is bounded by `2πη/L`. -/
lemma shell_qTh_le {L θ : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) (hθ : θ ∈ shells L) :
    (qTh θ) ^ 2 ≤ (2 * Real.pi * Work.Spaces.eta / L) ^ 2 := by
  have hsin := sin_shell_le hL hLp hθ
  have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le (by positivity) hsin
  have hcos : |Real.cos (2 * θ)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hcot : |Real.cot (2 * θ)| ≤ Real.pi / L := by
    rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinpos]
    have h1 : |Real.cos (2 * θ)| / Real.sin (2 * θ) ≤ 1 / Real.sin (2 * θ) := by
      have h : (0 : ℝ) ≤ 1 / Real.sin (2 * θ) - |Real.cos (2 * θ)| / Real.sin (2 * θ) := by
        rw [← sub_div]
        exact div_nonneg (by linarith) hsinpos.le
      linarith
    have h2 : 1 / Real.sin (2 * θ) ≤ Real.pi / L := by
      rw [div_le_iff₀ hsinpos, div_mul_eq_mul_div, le_div_iff₀ hL]
      have h3 := (div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi)).mp hsin
      linarith [h3]
    linarith
  have hsq : (Real.cot (2 * θ)) ^ 2 ≤ (Real.pi / L) ^ 2 := by
    have hpiL : (0 : ℝ) < Real.pi / L := by positivity
    calc (Real.cot (2 * θ)) ^ 2 = |Real.cot (2 * θ)| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.pi / L) ^ 2 := by
          rw [← sq_abs (Real.pi / L), abs_of_pos hpiL]
          exact pow_le_pow_left₀ (abs_nonneg _) hcot 2
  calc (qTh θ) ^ 2 = (2 * Work.Spaces.eta) ^ 2 * (Real.cot (2 * θ)) ^ 2 := by
        rw [qTh]; ring
    _ ≤ (2 * Work.Spaces.eta) ^ 2 * (Real.pi / L) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (2 * Real.pi * Work.Spaces.eta / L) ^ 2 := by ring

/-! ## 3. The support of the surrogate and of its derivatives -/

lemma surr_eq_zero_of_mid (hψ : IsBump ψ C) (hL : 0 < L) {θ : ℝ}
    (h1 : L / 2 ≤ θ) (h2 : θ ≤ Real.pi / 2 - L / 2) :
    surrFun ψ F₀ F₁ L θ = 0 := by
  have h1' : ψ (θ / L) = 0 := hψ.eq_zero _ (by rw [le_div_iff₀ hL]; linarith)
  have h2' : ψ ((Real.pi / 2 - θ) / L) = 0 := hψ.eq_zero _ (by rw [le_div_iff₀ hL]; linarith)
  rw [surrFun, h1', h2']
  ring

/-- The surrogate vanishes in the middle of the interval. -/
lemma surr_eq_zero_of_mem_Iθ_of_notMem (hψ : IsBump ψ C) (hL : 0 < L) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)) :
    surrFun ψ F₀ F₁ L θ = 0 := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  simp only [Set.mem_union, Set.mem_Icc, not_or, not_and_or, not_le] at h
  obtain ⟨hA, hB⟩ := h
  have h1 : L / 2 < θ := by
    rcases hA with h' | h'
    · linarith [hθ.1, h']
    · exact h'
  have h2 : θ < Real.pi / 2 - L / 2 := by
    rcases hB with h' | h'
    · exact h'
    · linarith [hθ.2, h']
  exact surr_eq_zero_of_mid hψ hL h1.le h2.le

/-- The first derivative of the surrogate vanishes off the two shells. -/
lemma deriv_surr_eq_zero_of_notMem (hψ : IsBump ψ C) (hL : 0 < L) {θ : ℝ}
    (h : θ ∉ shells L) : deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  simp only [shells, Set.mem_union, Set.mem_Icc, not_or, not_and_or, not_le] at h
  obtain ⟨hA, hB⟩ := h
  have h1 : deriv ψ (θ / L) = 0 := by
    rcases hA with h1 | h1
    · exact hψ.deriv_eq_zero_left _ (by rw [div_lt_iff₀ hL]; linarith)
    · exact hψ.deriv_eq_zero_right _ (by rw [lt_div_iff₀ hL]; linarith)
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    rcases hB with h2 | h2
    · exact hψ.deriv_eq_zero_right _ (by rw [lt_div_iff₀ hL]; linarith)
    · exact hψ.deriv_eq_zero_left _ (by rw [div_lt_iff₀ hL]; linarith)
  rw [h1, h2]
  ring

/-- The second derivative of the surrogate vanishes off the two shells. -/
lemma deriv2_surr_eq_zero_of_notMem (hψ : IsBump ψ C) (hL : 0 < L) {θ : ℝ}
    (h : θ ∉ shells L) : deriv (deriv (surrFun ψ F₀ F₁ L)) θ = 0 := by
  rw [deriv2_surr_eq hψ (ne_of_gt hL) θ]
  simp only [shells, Set.mem_union, Set.mem_Icc, not_or, not_and_or, not_le] at h
  obtain ⟨hA, hB⟩ := h
  have h1 : deriv (deriv ψ) (θ / L) = 0 := by
    rcases hA with h1 | h1
    · exact hψ.deriv2_eq_zero_left _ (by rw [div_lt_iff₀ hL]; linarith)
    · exact hψ.deriv2_eq_zero_right _ (by rw [lt_div_iff₀ hL]; linarith)
  have h2 : deriv (deriv ψ) ((Real.pi / 2 - θ) / L) = 0 := by
    rcases hB with h2 | h2
    · exact hψ.deriv2_eq_zero_right _ (by rw [lt_div_iff₀ hL]; linarith)
    · exact hψ.deriv2_eq_zero_left _ (by rw [div_lt_iff₀ hL]; linarith)
  rw [h1, h2]
  ring

/-! ## 4. The general shell integral estimate -/

/-- If `g ≥ 0` vanishes off the shells and is bounded by `M` there, then
`∫ g thEta ≤ M (π^η L^{-η}) (L/2)`: the weight is bounded by `π^η L^{-η}` on the shells,
which have total length `L/2`. -/
lemma shell_integral_le {g : ℝ → ℝ} {M : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hM : 0 ≤ M) (hg0 : ∀ θ, 0 ≤ g θ)
    (hbound : ∀ θ ∈ shells L, g θ ≤ M)
    (hzero : ∀ θ, θ ∉ shells L → g θ = 0)
    (hshell : ∀ θ ∈ shells L, Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) :
    (∫ θ in Work.Spaces.Iθ, g θ * Work.FTS.EllipticEst.thEta θ)
      ≤ M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) * (L / 2) := by
  have hsubS : shells L ⊆ Work.Spaces.Iθ := shells_subset_Iθ hL hLp
  have hT0 : (0 : ℝ) ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt Real.pi_pos) _) (Real.rpow_nonneg hL.le _)
  have hth0 : ∀ θ ∈ shells L, 0 ≤ Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have hmem := shells_subset_Iθ hL hLp hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hmem
    rw [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hmem.1])
      (by linarith [hmem.2, Real.pi_pos])) _
  have hpoint : ∀ θ, g θ * Work.FTS.EllipticEst.thEta θ
      ≤ (shells L).indicator
          (fun _ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) θ := by
    intro θ
    by_cases hθ : θ ∈ shells L
    · rw [Set.indicator_of_mem hθ]
      calc g θ * Work.FTS.EllipticEst.thEta θ
          ≤ M * Work.FTS.EllipticEst.thEta θ :=
            mul_le_mul_of_nonneg_right (hbound θ hθ) (hth0 θ hθ)
        _ ≤ M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_left (hshell θ hθ) hM
    · rw [Set.indicator_of_notMem hθ, hzero θ hθ]
      simp
  have hdisj : Disjoint (Set.Icc (L / 4) (L / 2))
      (Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2 - L / 4)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1, hLp, Real.pi_pos]
  have hvol : volume (shells L) = ENNReal.ofReal (L / 2) := by
    rw [shells, measure_union hdisj (by measurability), Real.volume_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  have hval : (∫ θ in Work.Spaces.Iθ, (shells L).indicator
        (fun _ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) θ)
      = (M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) * (L / 2) := by
    rw [setIntegral_indicator (shells_measurable L), Set.inter_eq_right.mpr hsubS]
    rw [setIntegral_const, Measure.real_def, hvol, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul]
    ring
  have hint : Integrable ((shells L).indicator
      (fun _ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))))
      (volume.restrict (Work.Spaces.Iθ)) := by
    have : IntegrableOn (fun _ : ℝ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))))
        (Work.Spaces.Iθ) :=
      integrableOn_const (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
    exact this.indicator (shells_measurable L)
  have hnn : 0 ≤ᵐ[volume.restrict (Work.Spaces.Iθ)]
      (fun θ => g θ * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    refine mul_nonneg (hg0 θ) ?_
    rw [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  calc (∫ θ in Work.Spaces.Iθ, g θ * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (shells L).indicator
          (fun _ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) θ :=
        integral_mono_of_nonneg hnn hint (Eventually.of_forall hpoint)
    _ = (M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) * (L / 2) := hval

/-! ## 5. The arithmetic of the constants -/

lemma arith_two {C F₀ F₁ : ℝ} (hC : 0 < C) :
    C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
  have hF : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    have h1 : (|F₀| + |F₁|) ^ 2 = F₀ ^ 2 + F₁ ^ 2 + 2 * (|F₀| * |F₁|) := by
      rw [add_sq, sq_abs, sq_abs]
      ring
    have h2 : 2 * (|F₀| * |F₁|) ≤ F₀ ^ 2 + F₁ ^ 2 := by
      nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
    linarith
  have hpi : Real.pi ^ Work.Spaces.eta ≤ 4 := by
    have h1 : Real.pi ^ Work.Spaces.eta ≤ Real.pi ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
        (le_of_lt Work.Spaces.eta_lt_one)
    rw [Real.rpow_one] at h1
    linarith [Real.pi_lt_four]
  have hCsq : C ^ 2 ≤ (C + 1) ^ 2 := by nlinarith [hC]
  have hpF : (0 : ℝ) ≤ F₀ ^ 2 + F₁ ^ 2 := by positivity
  have h1 : C ^ 2 * (|F₀| + |F₁|) ^ 2 ≤ C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) :=
    mul_le_mul_of_nonneg_left hF (sq_nonneg C)
  have h2 : C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta
      ≤ C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) * 4 :=
    mul_le_mul h1 hpi (Real.rpow_nonneg (le_of_lt Real.pi_pos) _) (by positivity)
  have h3 : C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2
      ≤ 4 * C ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    have h4 : C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2
        ≤ C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) * 4 / 2 := by linarith
    have h5 : C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) * 4 / 2 = 4 * C ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
      ring
    linarith [h4, h5.le, h5.ge]
  have h6 : 4 * C ^ 2 * (F₀ ^ 2 + F₁ ^ 2) ≤ 4 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    nlinarith [hCsq, hpF]
  have h7 : 4 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    nlinarith [hpF, sq_nonneg (C + 1)]
  linarith [h3, h6, h7]

lemma arith_four {C F₀ F₁ : ℝ} (hC : 0 < C) :
    4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
        * Real.pi ^ Work.Spaces.eta / 2
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
  have hF : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    have h1 : (|F₀| + |F₁|) ^ 2 = F₀ ^ 2 + F₁ ^ 2 + 2 * (|F₀| * |F₁|) := by
      rw [add_sq, sq_abs, sq_abs]
      ring
    have h2 : 2 * (|F₀| * |F₁|) ≤ F₀ ^ 2 + F₁ ^ 2 := by
      nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
    linarith
  have heta1 : Work.Spaces.eta ^ 2 ≤ 1 := by
    have h := Work.Spaces.eta_lt_one
    have h0 := Work.Spaces.eta_pos
    nlinarith
  have hpi3 : Real.pi ^ 2 * Real.pi ^ Work.Spaces.eta ≤ 64 := by
    have h1 : Real.pi ^ Work.Spaces.eta ≤ Real.pi ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
        (le_of_lt Work.Spaces.eta_lt_one)
    rw [Real.rpow_one] at h1
    have h2 : Real.pi ^ 2 * Real.pi ≤ 64 := by
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    nlinarith [h1, h2, Real.rpow_nonneg (le_of_lt Real.pi_pos) (Work.Spaces.eta)]
  have hCsq : C ^ 2 ≤ (C + 1) ^ 2 := by nlinarith [hC]
  have hpF : (0 : ℝ) ≤ F₀ ^ 2 + F₁ ^ 2 := by positivity
  have h0 : (0 : ℝ) ≤ Real.pi ^ Work.Spaces.eta := Real.rpow_nonneg (le_of_lt Real.pi_pos) _
  have h1 : 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
        * Real.pi ^ Work.Spaces.eta / 2
      = 2 * (Real.pi ^ 2 * Real.pi ^ Work.Spaces.eta) * Work.Spaces.eta ^ 2 * C ^ 2
          * (|F₀| + |F₁|) ^ 2 := by ring
  rw [h1]
  have h2 : 2 * (Real.pi ^ 2 * Real.pi ^ Work.Spaces.eta) * Work.Spaces.eta ^ 2 * C ^ 2
      * (|F₀| + |F₁|) ^ 2 ≤ 2 * 64 * 1 * C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) := by
    have h3 : Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
        ≤ 1 * C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) := by
      have ha : Work.Spaces.eta ^ 2 * (|F₀| + |F₁|) ^ 2 ≤ 1 * (2 * (F₀ ^ 2 + F₁ ^ 2)) :=
        mul_le_mul heta1 hF (by positivity) (by norm_num)
      nlinarith [ha, sq_nonneg C]
    have h4 : Real.pi ^ 2 * Real.pi ^ Work.Spaces.eta
        * (Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2)
        ≤ 64 * (1 * C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2))) :=
      mul_le_mul hpi3 h3 (by positivity) (by norm_num)
    nlinarith [h4]
  have h5 : 2 * 64 * 1 * C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    nlinarith [hCsq, hpF]
  linarith [h2, h5]

/-! ## 6. The four estimates -/

private lemma main_first (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hT1 : (∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta))
    (hT2 : (∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta)) :
    (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) := by
  have hsub : Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)
      ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ]
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, by linarith [h2, hLp, Real.pi_pos]⟩
    · exact ⟨by linarith [h1, hLp, Real.pi_pos], h2⟩
  have hpoint : ∀ᵐ θ ∂(volume.restrict (Work.Spaces.Iθ)),
      (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        ≤ (Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)).indicator
            (fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ) θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hθ' : θ ∈ Work.Spaces.Iθ := hθ
    by_cases hmem : θ ∈ Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)
    · rw [Set.indicator_of_mem hmem]
      have hb : |surrFun ψ F₀ F₁ L θ| ≤ |F₀| + |F₁| := surr_bound hψ θ
      have h1 : (surrFun ψ F₀ F₁ L θ) ^ 2 ≤ (|F₀| + |F₁|) ^ 2 := by
        rw [← sq_abs (surrFun ψ F₀ F₁ L θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have h2 : 0 ≤ Work.FTS.EllipticEst.thEta θ := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ'
        rw [Work.FTS.EllipticEst.thEta]
        exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ'.1])
          (by linarith [hθ'.2, Real.pi_pos])) _
      exact mul_le_mul_of_nonneg_right h1 h2
    · rw [Set.indicator_of_notMem hmem]
      have hz : surrFun ψ F₀ F₁ L θ = 0 :=
        surr_eq_zero_of_mem_Iθ_of_notMem hψ hL hθ' hmem
      rw [hz]
      simp
  have hInt1 : IntegrableOn Work.FTS.EllipticEst.thEta (Set.Icc (0 : ℝ) (L / 2)) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.mono_set (by
      intro x hx
      rw [Work.Spaces.Iθ]
      exact ⟨hx.1, by linarith [hx.2, hLp, Real.pi_pos]⟩)
  have hInt2 : IntegrableOn Work.FTS.EllipticEst.thEta
      (Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.mono_set (by
      intro x hx
      rw [Work.Spaces.Iθ]
      exact ⟨by linarith [hx.1, hLp, Real.pi_pos], hx.2⟩)
  have hunionInt : IntegrableOn Work.FTS.EllipticEst.thEta
      (Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.mono_set hsub
  have hdisj : Disjoint (Set.Icc (0 : ℝ) (L / 2))
      (Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1, hLp, Real.pi_pos]
  have hmajInt : Integrable
      ((Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)).indicator
        (fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (volume.restrict (Work.Spaces.Iθ)) := by
    have hf : IntegrableOn (fun θ : ℝ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul _
    exact hf.indicator (by measurability)
  have hval : (∫ θ in Work.Spaces.Iθ,
        (Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)).indicator
          (fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ) θ)
      = (|F₀| + |F₁|) ^ 2 * ((∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
          + ∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2), Work.FTS.EllipticEst.thEta θ) := by
    rw [setIntegral_indicator (by measurability), Set.inter_eq_right.mpr hsub]
    rw [MeasureTheory.integral_const_mul,
      setIntegral_union hdisj (by measurability) hInt1 hInt2]
  have htail : (∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      + (∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 400 * L ^ (1 - Work.Spaces.eta) := by linarith [hT1, hT2]
  have hnn : 0 ≤ᵐ[volume.restrict (Work.Spaces.Iθ)]
      (fun θ => (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hmem : θ ∈ Work.Spaces.Iθ := hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hmem
    refine mul_nonneg (sq_nonneg _) ?_
    rw [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hmem.1])
      (by linarith [hmem.2, Real.pi_pos])) _
  have hmain := integral_mono_of_nonneg hnn hmajInt hpoint
  have hF : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    have h1 : (|F₀| + |F₁|) ^ 2 = F₀ ^ 2 + F₁ ^ 2 + 2 * (|F₀| * |F₁|) := by
      rw [add_sq, sq_abs, sq_abs]
      ring
    have h2 : 2 * (|F₀| * |F₁|) ≤ F₀ ^ 2 + F₁ ^ 2 := by
      nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
    linarith
  have hC1 : (1 : ℝ) ≤ (C + 1) ^ 2 := by nlinarith [hψ.C_pos]
  have hL0 : (0 : ℝ) ≤ L ^ (1 - Work.Spaces.eta) := Real.rpow_nonneg hL.le _
  have habs : (0 : ℝ) ≤ (|F₀| + |F₁|) ^ 2 := by positivity
  calc (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)).indicator
            (fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ) θ := hmain
    _ = (|F₀| + |F₁|) ^ 2
          * ((∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
            + ∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2),
                Work.FTS.EllipticEst.thEta θ) := hval
    _ ≤ (|F₀| + |F₁|) ^ 2 * (400 * L ^ (1 - Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left htail habs
    _ ≤ (2 * (F₀ ^ 2 + F₁ ^ 2)) * (400 * L ^ (1 - Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right hF (by positivity)
    _ = 800 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) := by ring
    _ ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) := by
        refine mul_le_mul_of_nonneg_right ?_ hL0
        nlinarith [hC1, sq_nonneg F₀, sq_nonneg F₁,
          mul_le_mul_of_nonneg_right hC1 (by positivity : (0 : ℝ) ≤ F₀ ^ 2 + F₁ ^ 2)]

private lemma main_second (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hshell : ∀ θ ∈ shells L, Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta)) := by
  have hB : (0 : ℝ) ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 := by positivity
  have hM0 : (0 : ℝ) ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ) :=
    mul_nonneg hB (Real.rpow_nonneg hL.le _)
  have hbound : ∀ θ ∈ shells L,
      (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ) := by
    intro θ hθ
    have hb : |deriv (surrFun ψ F₀ F₁ L) θ| ≤ C * (|F₀| + |F₁|) / L :=
      deriv_surr_bound hψ hL θ
    have h3 : (C * (|F₀| + |F₁|) / L) ^ 2 = C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ) := by
      rw [sq_div_eq hL]
      ring
    calc (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2
        = |deriv (surrFun ψ F₀ F₁ L) θ| ^ 2 := (sq_abs _).symm
      _ ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ) := h3
  have hmain := shell_integral_le (g := fun θ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2)
    (M := C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ)) hL hLp hM0
    (fun θ => sq_nonneg _) hbound
    (fun θ hθ => by rw [deriv_surr_eq_zero_of_notMem hψ hL hθ]; ring) hshell
  refine hmain.trans ?_
  rw [show (C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ))
        * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) * (L / 2)
      = (C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2)
          * (L ^ (-2 : ℝ) * L ^ (-(Work.Spaces.eta)) * L) by ring,
    rpow_mul_L (L := L) hL 2,
    show -(2 + Work.Spaces.eta - 1 : ℝ) = -(1 + Work.Spaces.eta) by ring]
  exact mul_le_mul_of_nonneg_right (arith_two hψ.C_pos)
    (Real.rpow_nonneg hL.le _)

private lemma main_third (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hshell : ∀ θ ∈ shells L, Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta)) := by
  have hB : (0 : ℝ) ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 := by positivity
  have hM0 : (0 : ℝ) ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) :=
    mul_nonneg hB (Real.rpow_nonneg hL.le _)
  have hbound : ∀ θ ∈ shells L,
      (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2 ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := by
    intro θ hθ
    have hb : |deriv (deriv (surrFun ψ F₀ F₁ L)) θ| ≤ C * (|F₀| + |F₁|) / L ^ 2 :=
      deriv2_surr_bound hψ hL θ
    have h3 : (C * (|F₀| + |F₁|) / L ^ 2) ^ 2 = C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := by
      rw [sq_div_sq_eq hL]
      ring
    calc (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        = |deriv (deriv (surrFun ψ F₀ F₁ L)) θ| ^ 2 := (sq_abs _).symm
      _ ≤ (C * (|F₀| + |F₁|) / L ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := h3
  have hmain := shell_integral_le
    (g := fun θ => (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2)
    (M := C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ)) hL hLp hM0
    (fun θ => sq_nonneg _) hbound
    (fun θ hθ => by rw [deriv2_surr_eq_zero_of_notMem hψ hL hθ]; ring) hshell
  refine hmain.trans ?_
  rw [show (C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ))
        * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) * (L / 2)
      = (C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2)
          * (L ^ (-4 : ℝ) * L ^ (-(Work.Spaces.eta)) * L) by ring,
    rpow_mul_L (L := L) hL 4,
    show -(4 + Work.Spaces.eta - 1 : ℝ) = -(3 + Work.Spaces.eta) by ring]
  exact mul_le_mul_of_nonneg_right (arith_two hψ.C_pos)
    (Real.rpow_nonneg hL.le _)

private lemma main_fourth (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hshell : ∀ θ ∈ shells L, Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))
    (hqth : ∀ θ ∈ shells L, (qTh θ) ^ 2 ≤ (2 * Real.pi * Work.Spaces.eta / L) ^ 2) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta)) := by
  have hB : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 := by
    positivity
  have hM0 : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
      * L ^ (-4 : ℝ) := mul_nonneg hB (Real.rpow_nonneg hL.le _)
  have hbound : ∀ θ ∈ shells L,
      (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2
        ≤ 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := by
    intro θ hθ
    have hb : |deriv (surrFun ψ F₀ F₁ L) θ| ≤ C * (|F₀| + |F₁|) / L :=
      deriv_surr_bound hψ hL θ
    have hb2 : (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := by
      calc (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2
          = |deriv (surrFun ψ F₀ F₁ L) θ| ^ 2 := (sq_abs _).symm
        _ ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hq := hqth θ hθ
    have hq0 : (0 : ℝ) ≤ (2 * Real.pi * Work.Spaces.eta / L) ^ 2 := by positivity
    calc (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2
        ≤ (C * (|F₀| + |F₁|) / L) ^ 2 * (2 * Real.pi * Work.Spaces.eta / L) ^ 2 :=
          mul_le_mul hb2 hq (sq_nonneg _) (by positivity)
      _ = 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := by
          rw [sq_mul_sq_div hL]
          ring
  have hmain := shell_integral_le
    (g := fun θ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2)
    (M := 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ))
    hL hLp hM0 (fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hbound
    (fun θ hθ => by rw [deriv_surr_eq_zero_of_notMem hψ hL hθ]; ring) hshell
  refine hmain.trans ?_
  rw [show (4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ))
        * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) * (L / 2)
      = (4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
          * Real.pi ^ Work.Spaces.eta / 2)
          * (L ^ (-4 : ℝ) * L ^ (-(Work.Spaces.eta)) * L) by ring,
    rpow_mul_L (L := L) hL 4,
    show -(4 + Work.Spaces.eta - 1 : ℝ) = -(3 + Work.Spaces.eta) by ring]
  exact mul_le_mul_of_nonneg_right (arith_four hψ.C_pos) (Real.rpow_nonneg hL.le _)

end

theorem surrIntegrals {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) ∧
    (∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta))) ∧
    (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta))) ∧
    (∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 *
          (Work.EllipticEst.Core.i0Aux.qTh θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta))) :=
  ⟨main_first hψ hL hLp (thEta_tail_left hL hLp) (thEta_tail_right hL hLp),
   main_second hψ hL hLp (fun θ hθ => shell_thEta_le hL hLp hθ),
   main_third hψ hL hLp (fun θ hθ => shell_thEta_le hL hLp hθ),
   main_fourth hψ hL hLp (fun θ hθ => shell_thEta_le hL hLp hθ)
     (fun θ hθ => shell_qTh_le hL hLp hθ)⟩

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## 1. `Iθ` and `(0, π/2)` agree almost everywhere -/

/-- `Icc a b` and `Ioo a b` agree almost everywhere. -/
lemma tvh_ae_eq_Icc_Ioo (a b : ℝ) : Set.Icc a b =ᵐ[volume] Set.Ioo a b := by
  have hsub : Set.Icc a b \ Set.Ioo a b ⊆ ({a, b} : Set ℝ) := by
    rintro x ⟨hx, hx'⟩
    rw [Set.mem_Icc] at hx
    rw [Set.mem_Ioo] at hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hxa : x = a
    · exact Or.inl hxa
    · by_cases hxb : x = b
      · exact Or.inr hxb
      · exfalso
        exact hx' ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have h0 : volume (Set.Icc a b \ Set.Ioo a b) = 0 := by
    refine measure_mono_null hsub ?_
    exact (Set.finite_singleton b).insert a |>.measure_zero volume
  have hmem : ∀ᵐ x : ℝ, x ∉ (Set.Icc a b \ Set.Ioo a b) := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬x ∉ (Set.Icc a b \ Set.Ioo a b)} = Set.Icc a b \ Set.Ioo a b := by
      ext x; simp only [Set.mem_ofPred_eq, not_not]
    rw [hset]; exact h0
  filter_upwards [hmem] with x hx
  exact propext ⟨fun h1 => by by_contra h2; exact hx ⟨h1, h2⟩,
    fun h1 => ⟨le_of_lt h1.1, le_of_lt h1.2⟩⟩

/-- The closed angular interval and the open one agree almost everywhere. -/
lemma tvh_ae_eq_Iθ_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
  simpa only [Work.Spaces.Iθ] using tvh_ae_eq_Icc_Ioo 0 (Real.pi / 2)



/-- Two functions agreeing on the open interval agree a.e. on `Iθ`. -/
lemma tvh_ae_eq_of_forall_Ioo {g h : ℝ → ℝ}
    (hgh : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), g θ = h θ) :
    g =ᵐ[volume.restrict Work.Spaces.Iθ] h := by
  have hrestrict : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set tvh_ae_eq_Iθ_Ioo
  rw [hrestrict]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => hgh θ hθ)

/-! ## 2. Almost-everywhere strong measurability on `Iθ` -/

/-- The angular weight `thEta θ = sin(2θ)^{-η}` is a.e. strongly measurable on `Iθ`: it is
continuous on the open interval `(0, π/2)`, and the two endpoints are null. -/
lemma tvh_aesm_thEta :
    AEStronglyMeasurable Work.FTS.EllipticEst.thEta (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo 0 (Real.pi / 2)) := by
    refine (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)).rpow_const ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (x := 2 * θ) (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  have h1 : AEStronglyMeasurable Work.FTS.EllipticEst.thEta
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  rw [show volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ from (Measure.restrict_congr_set tvh_ae_eq_Iθ_Ioo).symm] at h1
  exact h1

/-- A function that is continuous on the open interval `(0, π/2)` is a.e. strongly
measurable on `Iθ`. -/
lemma tvh_aesm_of_continuousOn {u : ℝ → ℝ}
    (h : ContinuousOn u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable u (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    h.aestronglyMeasurable measurableSet_Ioo
  rw [show volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ from (Measure.restrict_congr_set tvh_ae_eq_Iθ_Ioo).symm] at h1
  exact h1

/-- A function of class `C^n` on the open interval is a.e. strongly measurable on `Iθ`
(for `n = 0` this is just continuity there). -/
lemma tvh_aesm_of_contDiffOn {u : ℝ → ℝ} {n : WithTop ℕ∞}
    (h : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) :=
  tvh_aesm_of_continuousOn h.continuousOn

/-! ## 3. Dominated integrability on `Iθ` -/

/-- Domination by an integrable function on `Iθ` yields integrability. -/
lemma tvh_integrableOn_of_abs_le {g F : ℝ → ℝ}
    (hF : IntegrableOn F Work.Spaces.Iθ)
    (hg : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ))
    (h : ∀ θ ∈ Work.Spaces.Iθ, |g θ| ≤ F θ) : IntegrableOn g Work.Spaces.Iθ := by
  refine Integrable.mono' hF hg ?_
  refine (ae_restrict_iff' (measurableSet_Icc : MeasurableSet Work.Spaces.Iθ)).mpr ?_
  exact Eventually.of_forall fun θ hθ => by
    simpa only [Real.norm_eq_abs] using h θ hθ

/-- The angular weight is integrable on `Iθ`. -/
lemma tvh_thEta_integrableOn :
    IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.integrableOn_thEta.1

/-- A constant multiple of the angular weight is integrable on `Iθ`. -/
lemma tvh_integrableOn_const_mul_thEta (c : ℝ) :
    IntegrableOn (fun θ : ℝ => c * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
  tvh_thEta_integrableOn.const_mul c

/-! ## 4. The combination rule for weighted squares -/

/-- If the two weighted squares `u² thEta` and `v² thEta` are integrable on `Iθ`,
and `u`, `v` are a.e. strongly measurable there, then so is `(u - v)² thEta`. -/
lemma tvh_integrableOn_sq_sub {u v : ℝ → ℝ}
    (hu : IntegrableOn (fun θ : ℝ => u θ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hv : IntegrableOn (fun θ : ℝ => v θ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hau : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ))
    (hav : AEStronglyMeasurable v (volume.restrict Work.Spaces.Iθ)) :
    IntegrableOn (fun θ : ℝ => (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
  have hdom : IntegrableOn
      (fun θ : ℝ => 2 * (u θ ^ 2 * Work.FTS.EllipticEst.thEta θ
        + v θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
    (hu.add hv).const_mul 2
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => u θ - v θ)
        (volume.restrict Work.Spaces.Iθ) := hau.sub hav
    exact (h1.pow 2).mul tvh_aesm_thEta
  refine tvh_integrableOn_of_abs_le hdom haesm ?_
  intro θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  have h1 : (u θ - v θ) ^ 2 ≤ 2 * (u θ ^ 2 + v θ ^ 2) := by
    nlinarith [sq_nonneg (u θ + v θ), sq_nonneg (u θ - v θ)]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
  calc (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ (2 * (u θ ^ 2 + v θ ^ 2)) * Work.FTS.EllipticEst.thEta θ :=
        mul_le_mul_of_nonneg_right h1 hσ
    _ = 2 * (u θ ^ 2 * Work.FTS.EllipticEst.thEta θ
          + v θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring

/-! ## 5. Derivative identities for `f - u` on the open interval -/

/-- First derivative of a difference: `deriv (f - u) = deriv f - deriv u` on `(0, π/2)`,
for `f` of class `C²` on that interval and `u` globally `C²`. -/
lemma tvh_deriv_sub {f u : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) (hu : ContDiff ℝ 2 u) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun θ : ℝ => f θ - u θ) θ = deriv f θ - deriv u θ := by
  intro θ hθ
  have hdf : DifferentiableAt ℝ f θ :=
    ((hf.contDiffAt (isOpen_Ioo.mem_nhds hθ))).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ u θ :=
    (hu.contDiffAt.differentiableAt) (by norm_num)
  exact deriv_sub hdf hdu

/-- Second derivative of a difference: `deriv (deriv (f - u)) = deriv (deriv f) -
deriv (deriv u)` on `(0, π/2)`. -/
lemma tvh_deriv2_sub {f u : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) (hu : ContDiff ℝ 2 u) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv (fun θ : ℝ => f θ - u θ)) θ = deriv (deriv f) θ - deriv (deriv u) θ := by
  intro θ hθ
  have hev : (fun y : ℝ => deriv f y - deriv u y)
      =ᶠ[𝓝 θ] deriv (fun θ : ℝ => f θ - u θ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    exact (tvh_deriv_sub hf hu y hy).symm
  rw [← hev.deriv_eq]
  have hdf : DifferentiableAt ℝ (deriv f) θ :=
    (((hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := 1) (by norm_num)).differentiableAt)
      (by norm_num)
  have hdu : DifferentiableAt ℝ (deriv u) θ := by
    have h1 : ContDiff ℝ 1 (deriv u) := by simpa using hu.deriv' (n := 1)
    exact h1.contDiffAt.differentiableAt (by norm_num)
  exact deriv_sub hdf hdu

/-! ## 6. Weighted integrability of the surrogate -/

/-- The surrogate and its first two derivatives satisfy global bounds depending only on
`C, F₀, F₁, L`, so their squares against the angular weight `thEta` are integrable on `Iθ`. -/
lemma tvh_surr_sq_integrable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) :
    IntegrableOn
        (fun θ : ℝ => (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    IntegrableOn
        (fun θ : ℝ => (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    IntegrableOn
        (fun θ : ℝ => (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have hs : ContDiff ℝ 2 (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) :=
    surr_smooth hψ (ne_of_gt hL)
  have hds : ContDiff ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) := by
    simpa using hs.deriv' (n := 1)
  have hdds : ContDiff ℝ 0 (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L))) := by
    simpa using hds.deriv' (n := 0)
  refine ⟨?_, ?_, ?_⟩
  · refine tvh_integrableOn_of_abs_le
      (tvh_integrableOn_const_mul_thEta ((|F₀| + |F₁|) ^ 2)) ?_ ?_
    · exact (hs.continuous.aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      refine mul_le_mul_of_nonneg_right ?_ hσ
      rw [← sq_abs (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (surr_bound hψ θ) 2
  · refine tvh_integrableOn_of_abs_le
      (tvh_integrableOn_const_mul_thEta ((C * (|F₀| + |F₁|) / L) ^ 2)) ?_ ?_
    · exact (hds.continuous.aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      refine mul_le_mul_of_nonneg_right ?_ hσ
      rw [← sq_abs (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (deriv_surr_bound hψ hL θ) 2
  · refine tvh_integrableOn_of_abs_le
      (tvh_integrableOn_const_mul_thEta ((C * (|F₀| + |F₁|) / L ^ 2) ^ 2)) ?_ ?_
    · exact (hdds.continuous.aestronglyMeasurable.pow 2).mul tvh_aesm_thEta
    · intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      refine mul_le_mul_of_nonneg_right ?_ hσ
      rw [← sq_abs (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (deriv2_surr_bound hψ hL θ) 2

end

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.thetaInterpEndpoints =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-- `|a| ≤ √B` follows from `a² ≤ B` and `0 ≤ B`. -/
private lemma tie_abs_le_sqrt {a B : ℝ} (_hB : 0 ≤ B) (h : a ^ 2 ≤ B) : |a| ≤ Real.sqrt B := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- Monotonicity of the set integral in the domain, for a nonnegative integrand on the
open angular interval `(0, π/2)`. -/
private lemma tie_setIntegral_mono {F : ℝ → ℝ}
    (hint : IntegrableOn F (Set.Ioo 0 (Real.pi / 2)))
    (hnn : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ F t)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ t in Set.Ioo 0 θ, F t) ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), F t := by
  refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact hnn t ht
  · filter_upwards with t ht
    exact ⟨ht.1, lt_trans ht.2 hθ.2⟩

/-- If `g` satisfies the endpoint bound `(g θ - c)² ≤ K θ^{1+η} ∫_{(0,θ)} G` coming from
`sliceBoundaryLimit`, with `G ≥ 0` and `K ≥ 0`, then `g` is uniformly bounded on the open
angular interval, with the explicit bound displayed below. -/
private lemma tie_bound_of_limit_bound {g : ℝ → ℝ} {G : ℝ → ℝ} {c K : ℝ} (hK : 0 ≤ K)
    (hint : IntegrableOn G (Set.Ioo 0 (Real.pi / 2)))
    (hnn : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ G t)
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (g θ - c) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) * (∫ t in Set.Ioo 0 θ, G t)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |g θ| ≤ |c| +
      Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 (Real.pi / 2), G t)) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hexp : 0 ≤ 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hEfull : 0 ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), G t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo hnn
  have hconst : 0 ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 (Real.pi / 2), G t) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hpi.le _)) hEfull
  intro θ hθ
  have hrpow : θ ^ (1 + Work.Spaces.eta) ≤ (Real.pi / 2) ^ (1 + Work.Spaces.eta) :=
    Real.rpow_le_rpow hθ.1.le hθ.2.le hexp
  have hmono := tie_setIntegral_mono hint hnn hθ
  have hEθ : 0 ≤ ∫ t in Set.Ioo 0 θ, G t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun t ht => hnn t ⟨ht.1, lt_trans ht.2 hθ.2⟩)
  have hsq : (g θ - c) ^ 2 ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 (Real.pi / 2), G t) := by
    refine le_trans (hb θ hθ) ?_
    calc K * θ ^ (1 + Work.Spaces.eta) * (∫ t in Set.Ioo 0 θ, G t)
        ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * (∫ t in Set.Ioo 0 θ, G t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow hK) hEθ
      _ ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo 0 (Real.pi / 2), G t) :=
          mul_le_mul_of_nonneg_left hmono (mul_nonneg hK (Real.rpow_nonneg hpi.le _))
  calc |g θ| = |(g θ - c) + c| := by ring_nf
    _ ≤ |g θ - c| + |c| := abs_add_le _ _
    _ ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 (Real.pi / 2), G t)) + |c| :=
        add_le_add_left (tie_abs_le_sqrt hconst hsq) |c|
    _ = |c| + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 (Real.pi / 2), G t)) := by ring

/-- **Endpoint limits and uniform bounds for angular slices of class `C²` with finite
weighted energy.**

If `f` is `C²` on `(0, π/2)` and the weighted energies `∫ (f)² sin(2θ)^{-η}`,
`∫ (f')² sin(2θ)^{-η}`, `∫ (f'')² sin(2θ)^{-η}` over the closed angular interval `Iθ` are
finite, then `f` and `f'` have limits at both endpoints `0⁺` and `(π/2)⁻`, and both are
bounded on `(0, π/2)`.

The two endpoint limits (and the explicit decay bounds) come from
`Work.EllipticEst.Core.sliceBoundaryLimit` applied to `f` and to `deriv f`; the uniform
bounds are read off from those decay bounds together with the monotonicity of the energy in
the angular variable. -/
theorem thetaInterpEndpoints : ∀ (f : ℝ → ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    ∃ F₀ F₁ L₀ L₁ M M' : ℝ,
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀) ∧
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) ∧
      Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L₀) ∧
      Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L₁) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M') := by
  intro f hf _h0 h1 h2
  -- the open interval sits inside `Iθ`
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩
  have h1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := h1.mono_set hsub
  have h2' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := h2.mono_set hsub
  -- regularity of `f` and of `deriv f` on the open interval
  have hcf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  have hcd : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  obtain ⟨K, hKpos, hK⟩ := sliceBoundaryLimit
  obtain ⟨⟨F₀, hF₀, hbF₀⟩, ⟨F₁, hF₁, hbF₁⟩⟩ := hK f hcf h1'
  obtain ⟨⟨L₀, hL₀, hbL₀⟩, ⟨L₁, hL₁, hbL₁⟩⟩ := hK (deriv f) hcd h2'
  -- nonnegativity of the two energies, for the monotonicity step
  have hnn1 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := fun t ht =>
    mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨ht.1.le, ht.2.le⟩)
  have hnn2 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ (deriv (deriv f) t) ^ 2 * Work.FTS.EllipticEst.thEta t := fun t ht =>
    mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨ht.1.le, ht.2.le⟩)
  exact ⟨F₀, F₁, L₀, L₁,
    |F₀| + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)),
    |L₀| + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) t) ^ 2 * Work.FTS.EllipticEst.thEta t)),
    hF₀, hF₁, hL₀, hL₁,
    tie_bound_of_limit_bound hKpos.le h1' hnn1 hbF₀,
    tie_bound_of_limit_bound hKpos.le h2' hnn2 hbL₀⟩

end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.FTS.BSSwirl.contDiff_one_newtonPotential =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

/-- **`C¹` of the Newtonian potential.**  Let `ω` be a bounded, a.e. strongly measurable vector
field supported in `closedBall 0 R`, and suppose (this is the content of the Calderón–Zygmund
computation `hasFDerivAt_newtonPotential`) that the Newtonian potential `A ω` is differentiable
everywhere with derivative `potDeriv ω`.  Then `A ω` is `C¹`.

The only point to prove is the **continuity of the derivative**: `potDeriv ω x` is the singular
integral `(4π)⁻¹ ∫ z, (potKer z).smulRight (ω (x+z))`; since `ω` is only bounded and measurable,
the pointwise dominated-convergence theorem cannot be applied directly, and the continuity is
obtained instead from the continuity of translations in `L¹`
(`tendsto_integral_norm_sub_translate`, `continuous_integral_smulRight_shift`), the substitution
`z ↦ z + h` moving the shift from the density onto the integrable cut-off kernel `potKerBall ρ`. -/
theorem contDiff_one_newtonPotential {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hd : ∀ x, HasFDerivAt (Work.FTS.BSSwirl.newtonPotential ω)
      (Work.FTS.BSSwirl.potDeriv ω x) x) :
    ContDiff ℝ 1 (Work.FTS.BSSwirl.newtonPotential ω) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨Work.FTS.BSSwirl.potDeriv ω, ?_, hd⟩
  rw [continuous_iff_continuousAt]
  intro x₀
  set ρ : ℝ := R + ‖x₀‖ + 2 with hρ
  have htrans : Filter.Tendsto
      (fun h : Work.FTS.BSSwirl.R3 =>
        ∫ z, ‖Work.FTS.BSSwirl.potKerBall ρ (z + h) - Work.FTS.BSSwirl.potKerBall ρ z‖)
      (nhds 0) (nhds 0) :=
    Work.FTS.BSSwirl.tendsto_integral_norm_sub_translate (Work.FTS.BSSwirl.potKerBall ρ)
      (Work.FTS.BSSwirl.integrable_potKerBall ρ)
  have hcont : Continuous
      (fun x : Work.FTS.BSSwirl.R3 =>
        ∫ z, (Work.FTS.BSSwirl.potKerBall ρ z).smulRight (ω (x + z))) :=
    Work.FTS.BSSwirl.continuous_integral_smulRight_shift (Work.FTS.BSSwirl.integrable_potKerBall ρ)
      hbdd hmeas htrans
  refine (hcont.continuousAt.const_smul ((4 * Real.pi)⁻¹)).congr ?_
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : ‖x - x₀‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hx
    exact hx
  have hxR : R + ‖x‖ + 1 ≤ ρ := by
    have h1 : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h2 := norm_add_le (x - x₀) x₀
      rw [sub_add_cancel] at h2
      linarith
    rw [hρ]
    linarith
  exact (Work.FTS.BSSwirl.potDeriv_eq_integral_potKerBall hsupp hxR).symm

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeSliceBdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-!
# Slicewise boundedness and `σ`-weighted square-integrability for `AeData`

For data `AeData α u G` (the almost-everywhere class of the level-`0` elliptic estimate, whose
slices are allowed to jump at `θ = 0, π/2`), we prove that every `θ`-slice of `u` is

* bounded on the closed interval `Iθ = [0, π/2]`, and
* square-integrable against the angular weight `σ = sEta = sin(2θ)^{-η}`.

The mathematics is two applications of the fundamental theorem of calculus.  The class `AeData`
requires honesty of the level-`0` `ℋ⁰` integrand of `∂_θθu`, i.e. for every `z > 0`

`∫_{Iθ} (∂_θθu(z,·))² σ < ∞`.

Since `σ ≥ 1` on the open interval, this is *stronger* than the plain `L¹`-integrability of
`∂_θθu`; on the open interval `(0, π/2)` the slice `θ ↦ u(z,θ)` is `C²`, so
`∂_θu(θ) = ∂_θu(π/4) + ∫_{π/4}^{θ}∂_θθu`, and once more for `u` itself: the slice is bounded on
`(0, π/2)`.  At the endpoints the *values* `u z 0 = 0`, `u z (π/2) = 0` are part of `AeData`, so
the bound extends to all of `Iθ`.  The second conjunct then follows from the first because `σ` is
integrable on `Iθ` (`η = 99/100 < 1`).
-/

/-! ## Elementary facts about the angular weight `σ = sEta = sin(2θ)^{-η}` on `Iθ` -/

private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

private theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

private theorem measurable_sEta :
    Measurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) := by
  have h : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  simpa only [Work.FTS.EllipticEst.sEta] using h.pow measurable_const


/-- On `Iθ` the level-`0` `HkIntegrand` is the single weighted square `g² w² σ` (the
mixed-derivative sum of `HkIntegrand` is empty at level `0`). -/
private theorem HkIntegrand_zero_eq_sEta (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-- The `θ`-slices of a function smooth on the open quadrant are smooth on the open interval
`(0, π/2)`. -/
private theorem contDiffOn_slice_of_strip {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
  exact (hsm n).comp (by fun_prop) hmap

/-- `HkMem α 0 (∂_θθu)` gives the slicewise `σ`-weighted integrability of `∂_θθu`: for every
`z > 0` the function `θ ↦ (∂_θθu(z,θ))² σ θ` is integrable on `Iθ` (the square `(w z)²` of the
radial weight is a nonzero constant). -/
private theorem integrableOn_pthIter2_sEta_of_HkMem {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u)) {z : ℝ} (hz : 0 < z) :
    IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have h1 := hm.1 z hzI
  have h2 : IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => HkIntegrand_zero_eq_sEta α (Work.Spaces.pthIter 2 u) z hθ)
      measurableSet_Icc
  have hw' : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
  have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
  refine h3.congr (Eventually.of_forall (fun θ => ?_))
  show ((Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
      = (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  field_simp



end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.slice_self_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Blocks


end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.G1Alt.g1BoundAlt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The statement of the crux `Work.FTS.EllipticEst.H2W.vTwoW4Weak`
(`Submission/Work/FTS/EllipticEst/H2W/vTwoW4Weak.lean`), as a hypothesis so that this
module can be used with whichever proof of it becomes available first
(`H2W.VTwoAlt.vTwoW4WeakAlt` is a sibling proof target). -/
def VTwoW4Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))


set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Elementary arithmetic -/

private lemma sq_four_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b + c + d)]

/-! ## Facts on `Iθ` -/

private lemma sin_two_nonneg_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

private lemma sEta_nonneg_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_Iθ_prv hθ) _

private lemma measurable_sig2 (γ : ℝ) (hγ2 : γ ≤ 3 / 2) :
    Measurable (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
  (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
    (Real.continuous_sin.measurable.comp (continuous_const.mul continuous_id).measurable)

/-- Almost every point of `Iθ` lies in the open interval. -/
private lemma ae_mem_Ioo :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
  rw [(show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl),
    MeasureTheory.Measure.restrict_congr_set h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The weight identity `sin²θ · sin(2θ)^{2-γ} = (sin(2θ)^{4-γ}/cos²θ)/4`. -/
private lemma sin_sq_mul_sig2 (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      = Real.rpow (Real.sin (2 * θ)) (4 - γ) / (4 * Real.cos θ ^ 2) := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).ne'
  have hsplit : Real.rpow (Real.sin (2 * θ)) (4 - γ)
      = Real.rpow (Real.sin (2 * θ)) (2 - γ) * Real.sin (2 * θ) ^ 2 := by
    have h := Real.rpow_add hpos (2 - γ) 2
    rw [show (2 - γ) + 2 = 4 - γ by ring, Real.rpow_two] at h
    exact h
  rw [hsplit, Real.sin_two_mul]
  field_simp
  ring

/-! ## The pointwise identity `g' = -u''' + sinθ·v'' + sinθ·v - 4u'` -/

private lemma gprime_ident_v (u g : ℝ → ℝ)
    (hu3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ = - deriv (deriv (deriv u)) θ
        + Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ
        + Real.sin θ * (u θ / Real.cos θ) - 4 * deriv u θ := by
  intro θ hθ
  have hA := Work.FTS.EllipticEst.remov.slice_gprime_ident u g hu3 hode θ hθ
  have hB := Work.FTS.EllipticEst.remov.slice_v_identities u hu3 θ hθ
  rw [hA, hB.2.2.1, hB.2.2.2]
  ring

/-! ## The theorem -/

theorem g1BoundAlt (hcrux : VTwoW4Statement) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := hcrux
  obtain ⟨Cv, hCvpos, hCv⟩ := Work.FTS.EllipticEst.remov.sliceUdivCosUniform
  refine ⟨4 + Cw + 4 * Cv + 64, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu4 hcont hu0 hupi hode hI4 hI3 hI2 hI1 hI0 hIg2
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hu3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) := hu4.of_le (by norm_num)
  -- abbreviations
  set sg2 : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ) with hsg2
  set w4 : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2 with hw4
  set A3 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ with hA3
  set A2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Work.FTS.EllipticEst.sEta θ with hA2
  set A1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA1
  set A0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hA0
  set B2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ) with hB2
  change (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * sg2 θ)
    ≤ (4 + Cw + 4 * Cv + 64) * (B2 + A3 + A2 + A1 + A0)
  -- nonnegativity of the data
  have hA3nn : 0 ≤ A3 := by
    rw [hA3]
    exact MeasureTheory.setIntegral_nonneg hIθmeas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_prv hθ) _))
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    exact MeasureTheory.setIntegral_nonneg hIθmeas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ_prv hθ))
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]; exact MeasureTheory.setIntegral_nonneg hIθmeas (fun θ _ => sq_nonneg _)
  have hA0nn : 0 ≤ A0 := by
    rw [hA0]; exact MeasureTheory.setIntegral_nonneg hIθmeas (fun θ _ => sq_nonneg _)
  have hB2nn : 0 ≤ B2 := by
    rw [hB2]
    exact MeasureTheory.setIntegral_nonneg hIθmeas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_prv hθ) _))
  -- restatements of the integrability hypotheses, in terms of `sg2`
  have hI3' : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ)
      Work.Spaces.Iθ := hI3
  have hI1' : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ := hI1
  -- the imported slot estimates
  have hVslots := hCv γ u hγ1 hγ2 hu3 hcont hu0 hupi hI1 hI0
  obtain ⟨hVint, hVle⟩ := hVslots
  have hVint' : MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * sg2 θ) Work.Spaces.Iθ := hVint
  have hVle' : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 * sg2 θ)
      ≤ Cv * (A1 + A0) := hVle
  have hWle : (∫ θ in Work.Spaces.Iθ,
      (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * w4 θ) ≤ Cw * (A3 + A2 + A1 + A0) :=
    hCw γ u hγ1 hγ2 hu4 hcont hu0 hupi hI3 hI2 hI1 hI0
  -- the pointwise identity and the pointwise bound
  have hid := gprime_ident_v u g hu3 hode
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv g θ) ^ 2 * sg2 θ ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
        + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
        + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
        + 16 * (deriv u θ) ^ 2) := by
    intro θ hθ
    have h2 : (deriv g θ) ^ 2
        = (- deriv (deriv (deriv u)) θ
            + Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ
            + Real.sin θ * (u θ / Real.cos θ) + (-4 * deriv u θ)) ^ 2 := by
      rw [hid θ hθ]; ring
    have h4 := sq_four_le (- deriv (deriv (deriv u)) θ)
      (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ)
      (Real.sin θ * (u θ / Real.cos θ)) (-4 * deriv u θ)
    have hs : 0 ≤ sg2 θ := by
      rw [hsg2]
      exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
    have hs1 : sg2 θ ≤ 1 := by
      rw [hsg2]
      exact Real.rpow_le_one (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) (Real.sin_le_one _)
        (by linarith)
    have h4' := mul_le_mul_of_nonneg_right h4 hs
    have h64 : (-4 * deriv u θ) ^ 2 * sg2 θ ≤ (-4 * deriv u θ) ^ 2 := by
      have hnn : (0 : ℝ) ≤ (-4 * deriv u θ) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hs1 hnn]
    calc (deriv g θ) ^ 2 * sg2 θ
        = (- deriv (deriv (deriv u)) θ
            + Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ
            + Real.sin θ * (u θ / Real.cos θ) + (-4 * deriv u θ)) ^ 2 * sg2 θ := by rw [h2]
      _ ≤ (4 * ((- deriv (deriv (deriv u)) θ) ^ 2
              + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2
              + (-4 * deriv u θ) ^ 2)) * sg2 θ := h4'
      _ = 4 * ((((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
              + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + (-4 * deriv u θ) ^ 2 * sg2 θ) := by ring
      _ ≤ 4 * ((((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
              + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + (-4 * deriv u θ) ^ 2) := by linarith [h64]
      _ = 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
            + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
            + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
            + 16 * (deriv u θ) ^ 2) := by ring
  -- the weight identity, almost everywhere on `Iθ`
  have hW4ae : (fun θ => (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
        * sg2 θ)
      =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
      (fun θ => ((deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * w4 θ) / 4) := by
    filter_upwards [ae_mem_Ioo] with θ hθ
    rw [hsg2, hw4]
    have h := sin_sq_mul_sig2 γ hθ
    calc (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        = (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * (Real.sin θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by ring
      _ = (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (4 * Real.cos θ ^ 2)) := by rw [h]
      _ = (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2) / 4 := by ring
  -- integrability of the `(sinθ · v)²σ₂` piece
  have hz3Int : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ) Work.Spaces.Iθ := by
    have hmeas : AEStronglyMeasurable
        (fun θ => (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
      refine AEStronglyMeasurable.mul (AEStronglyMeasurable.pow ?_ 2)
        (measurable_sig2 γ hγ2).aestronglyMeasurable
      refine AEStronglyMeasurable.mul Real.continuous_sin.measurable.aestronglyMeasurable ?_
      exact AEStronglyMeasurable.div₀ (hcont.aestronglyMeasurable hIθmeas)
        Real.continuous_cos.measurable.aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' hVint' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with θ hθ
    have hs : 0 ≤ sg2 θ := by
      rw [hsg2]
      exact Real.rpow_nonneg (sin_two_nonneg_Iθ_prv hθ) _
    have hv : 0 ≤ (u θ / Real.cos θ) ^ 2 := sq_nonneg _
    have h1 : 0 ≤ (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ :=
      mul_nonneg (sq_nonneg _) hs
    have h2 : 0 ≤ (u θ / Real.cos θ) ^ 2 * sg2 θ := mul_nonneg hv hs
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    nlinarith [mul_nonneg hv hs, sq_nonneg (Real.sin θ)]
  -- the case split
  by_cases hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * sg2 θ) Work.Spaces.Iθ
  · -- main case
    have hz2Int : MeasureTheory.IntegrableOn
        (fun θ => (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * sg2 θ) Work.Spaces.Iθ := by
      have hmaj : MeasureTheory.IntegrableOn (fun θ => 4 * ((deriv g θ) ^ 2 * sg2 θ
          + (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
          + 16 * (deriv u θ) ^ 2)) Work.Spaces.Iθ :=
        (((hD.add hI3').add hz3Int).add (hI1'.const_mul 16)).const_mul 4
      have hmeas : AEStronglyMeasurable
          (fun θ => (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
            * sg2 θ) ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
        (AEStronglyMeasurable.mul (AEStronglyMeasurable.pow
          (AEStronglyMeasurable.mul Real.continuous_sin.measurable.aestronglyMeasurable
            (measurable_deriv (deriv (fun s => u s / Real.cos s))).aestronglyMeasurable) 2)
          (measurable_sig2 γ hγ2).aestronglyMeasurable)
      refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
      filter_upwards [ae_mem_Ioo] with θ hθ
      have h := hid θ hθ
      have hS : Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ
          = deriv g θ + deriv (deriv (deriv u)) θ
            - Real.sin θ * (u θ / Real.cos θ) + 4 * deriv u θ := by linarith
      have hs : 0 ≤ sg2 θ := by
        rw [hsg2]
        exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
      have hs1 : sg2 θ ≤ 1 := by
        rw [hsg2]
        exact Real.rpow_le_one (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) (Real.sin_le_one _)
          (by linarith)
      have h4 := sq_four_le (deriv g θ) (deriv (deriv (deriv u)) θ)
        (-(Real.sin θ * (u θ / Real.cos θ))) (4 * deriv u θ)
      have h4' := mul_le_mul_of_nonneg_right h4 hs
      have hnn : 0 ≤ (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2
          * sg2 θ := mul_nonneg (sq_nonneg _) hs
      have h16 : (4 * deriv u θ) ^ 2 * sg2 θ ≤ (4 * deriv u θ) ^ 2 := by
        have hnn2 : (0 : ℝ) ≤ (4 * deriv u θ) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hs1 hnn2]
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, hS]
      calc (deriv g θ + deriv (deriv (deriv u)) θ - Real.sin θ * (u θ / Real.cos θ)
            + 4 * deriv u θ) ^ 2 * sg2 θ
          = (deriv g θ + deriv (deriv (deriv u)) θ
              + (-(Real.sin θ * (u θ / Real.cos θ))) + (4 * deriv u θ)) ^ 2 * sg2 θ := by ring
        _ ≤ (4 * ((deriv g θ) ^ 2 + (deriv (deriv (deriv u)) θ) ^ 2
              + (-(Real.sin θ * (u θ / Real.cos θ))) ^ 2 + (4 * deriv u θ) ^ 2)) * sg2 θ := h4'
        _ = 4 * ((((deriv g θ) ^ 2 * sg2 θ + (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ)
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + (4 * deriv u θ) ^ 2 * sg2 θ) := by ring
        _ ≤ 4 * ((((deriv g θ) ^ 2 * sg2 θ + (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ)
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + (4 * deriv u θ) ^ 2) := by linarith [h16]
        _ = 4 * ((deriv g θ) ^ 2 * sg2 θ + (deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
              + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
              + 16 * (deriv u θ) ^ 2) := by ring
    have hmajInt : MeasureTheory.IntegrableOn
        (fun θ => 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ
          + 16 * (deriv u θ) ^ 2)) Work.Spaces.Iθ :=
      (((hI3'.add hz2Int).add hz3Int).add (hI1'.const_mul 16)).const_mul 4
    have hle := MeasureTheory.integral_mono_ae hD hmajInt
      (ae_mem_Ioo.mono (fun θ hθ => hpt θ hθ))
    -- the value of the majorant integral
    have hMajVal : (∫ θ in Work.Spaces.Iθ, 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ + 16 * (deriv u θ) ^ 2))
        = 4 * (A3 + (∫ θ in Work.Spaces.Iθ,
              (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
            + (∫ θ in Work.Spaces.Iθ, (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
            + 16 * A1) := by
      rw [MeasureTheory.integral_const_mul]
      have hpoint : ∀ x : ℝ, (deriv (deriv (deriv u)) x) ^ 2 * sg2 x
            + (Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x) ^ 2 * sg2 x
            + (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x + 16 * (deriv u x) ^ 2
          = ((deriv (deriv (deriv u)) x) ^ 2 * sg2 x
              + (Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x) ^ 2 * sg2 x)
            + (((Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x) + 16 * (deriv u x) ^ 2) :=
        fun x => by ring
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
      have h12 : MeasureTheory.Integrable (fun x : ℝ =>
          (deriv (deriv (deriv u)) x) ^ 2 * sg2 x
            + (Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x) ^ 2 * sg2 x)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hI3'.add hz2Int
      have h34 : MeasureTheory.Integrable (fun x : ℝ =>
          (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x + 16 * (deriv u x) ^ 2)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hz3Int.add (hI1'.const_mul 16)
      rw [MeasureTheory.integral_add h12 h34]
      have h1 : MeasureTheory.Integrable (fun x : ℝ => (deriv (deriv (deriv u)) x) ^ 2 * sg2 x)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hI3'
      have h2 : MeasureTheory.Integrable (fun x : ℝ =>
          (Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x) ^ 2 * sg2 x)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hz2Int
      have h3 : MeasureTheory.Integrable (fun x : ℝ =>
          (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hz3Int
      have h4 : MeasureTheory.Integrable (fun x : ℝ => 16 * (deriv u x) ^ 2)
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hI1'.const_mul 16
      rw [MeasureTheory.integral_add h1 h2]
      have hpoint2 : ∀ x : ℝ, (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x
            + 16 * (deriv u x) ^ 2
          = (Real.sin x * (u x / Real.cos x)) ^ 2 * sg2 x
            + (fun y : ℝ => 16 * (deriv u y) ^ 2) x := fun x => rfl
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint2)]
      rw [MeasureTheory.integral_add h3 h4, MeasureTheory.integral_const_mul, hA3.symm,
        hA1.symm]
      ring
    -- the two slot bounds
    have hz2le : (∫ θ in Work.Spaces.Iθ,
        (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
        ≤ (Cw / 4) * (A3 + A2 + A1 + A0) := by
      have heq : (∫ θ in Work.Spaces.Iθ,
          (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ)
          = (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * w4 θ) / 4 := by
        rw [MeasureTheory.integral_congr_ae hW4ae, MeasureTheory.integral_div]
      rw [heq]
      have h := mul_le_mul_of_nonneg_left hWle (by norm_num : (0 : ℝ) ≤ 1 / 4)
      linarith [h]
    have hz3le : (∫ θ in Work.Spaces.Iθ, (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ)
        ≤ Cv * (A1 + A0) := by
      refine le_trans ?_ hVle'
      refine MeasureTheory.integral_mono_ae hz3Int hVint' ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with θ hθ
      have hs : 0 ≤ sg2 θ := by
        rw [hsg2]
        exact Real.rpow_nonneg (sin_two_nonneg_Iθ_prv hθ) _
      have hv : 0 ≤ (u θ / Real.cos θ) ^ 2 := sq_nonneg _
      have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
      nlinarith [mul_nonneg hv hs, sq_nonneg (Real.sin θ)]
    -- assembly
    have step1 : (∫ θ in Work.Spaces.Iθ, 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * deriv (deriv (fun s => u s / Real.cos s)) θ) ^ 2 * sg2 θ
          + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * sg2 θ + 16 * (deriv u θ) ^ 2))
        ≤ 4 * (A3 + (Cw / 4) * (A3 + A2 + A1 + A0) + Cv * (A1 + A0) + 16 * A1) := by
      rw [hMajVal]
      linarith [hz2le, hz3le]
    have step2 : 4 * (A3 + (Cw / 4) * (A3 + A2 + A1 + A0) + Cv * (A1 + A0) + 16 * A1)
        ≤ (4 + Cw) * (A3 + A2 + A1 + A0) + (4 * Cv + 64) * (A1 + A0) := by
      nlinarith [hA2nn, hA1nn, hA0nn, hCwpos, hCvpos]
    have step3 : (4 + Cw) * (A3 + A2 + A1 + A0) + (4 * Cv + 64) * (A1 + A0)
        ≤ (4 + Cw + 4 * Cv + 64) * (B2 + A3 + A2 + A1 + A0) := by
      have h1 : A3 + A2 + A1 + A0 ≤ B2 + A3 + A2 + A1 + A0 := by linarith [hB2nn]
      have h2 : A1 + A0 ≤ B2 + A3 + A2 + A1 + A0 := by linarith [hB2nn, hA3nn, hA2nn]
      have h3 : 0 ≤ B2 + A3 + A2 + A1 + A0 := by
        linarith [hB2nn, hA3nn, hA2nn, hA1nn, hA0nn]
      have h4 : 0 ≤ A3 + A2 + A1 + A0 := by linarith [hA3nn, hA2nn, hA1nn, hA0nn]
      have h5 : 0 ≤ A1 + A0 := by linarith [hA1nn, hA0nn]
      nlinarith [h1, h2, h3, h4, h5, hCwpos, hCvpos]
    exact le_trans hle (le_trans step1 (le_trans step2 step3))
  · -- junk case
    have hzero : (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * sg2 θ) = 0 :=
      MeasureTheory.integral_undef hD
    have h3 : 0 ≤ B2 + A3 + A2 + A1 + A0 := by
      linarith [hB2nn, hA3nn, hA2nn, hA1nn, hA0nn]
    have hCpos : 0 < 4 + Cw + 4 * Cv + 64 := by linarith [hCwpos, hCvpos]
    rw [hzero]
    nlinarith [h3, hCpos]

end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp `cos²`-weighted Hardy inequality on the open interval

This is the *weak-class* version of `Work.FTS.EllipticEst.Honest.SharpHardyCosWeight` and of
`Work.FTS.EllipticEst.H2W.sharpHardy_slice`: the slice `v` is only required to be `C¹` on the
**open** interval `(0,π/2)` (no closed-interval regularity and no endpoint values — this is what
the almost-everywhere class `H2W.Ae.AeData` supplies), and

```
∫_θ v² cos²(2θ) sin(2θ)^{-2-η}  ≤  (1+η)^{-2} · ∫_θ v'(θ)² sin(2θ)^{-η} ,
```

with **no** correction term: the boundary term of the completion of squares vanishes because of
`SlotA.cross_theta_ibp` (`∫ gDeriv η v = 0` on `(0,π/2)`, the derivative of
`gFn η v θ = v θ² cos(2θ) sin(2θ)^{-1-η}`), which is the `θ`-IBP of the cross term of `I₁`.

## Proof

The pointwise completion of squares (`hardy_pointwise`, a copy of the body of
`H2W.sharpHardy_slice.slice_pointwise`) gives, for `θ ∈ (0,π/2)`,

`(1+η)² v² cos²(2θ) sin(2θ)^{-2-η} ≤ v'² sin(2θ)^{-η} - (1+η)·gDeriv η v θ`.

Integrating over `(0,π/2)` and using `∫ gDeriv η v = 0` (from `cross_theta_ibp`, by linearity of
the integral applied to the three summands of `gDeriv`) gives `(1+η)²∫v²cos²2θ sin^{-2-η} ≤
∫v'²sin^{-η}`, i.e. the claim after dividing by `(1+η)² > 0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)




end Work.FTS.EllipticEst.H2W.SlotA
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology Interval

/-- On `Iθ = [0, π/2]` the distance to the nearer endpoint is dominated by `(π/4)·sin(2θ)`.
Concavity of `sin` on `[0, π/2]` gives `(2/π)·x ≤ sin x` there; applied to `2θ ≤ π/2`
(equivalently to `2(π/2 - θ) ≤ π/2`, using `sin(π - x) = sin x`) this yields `θ ≤ (π/4)sin 2θ`
on the left half of `Iθ` and `π/2 - θ ≤ (π/4)sin 2θ` on the right half. -/
theorem min_le_sin_Iθ {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rcases le_total θ (Real.pi / 4) with hle | hge
  · -- left half: `2θ ≤ π/2`, so `(2/π)·(2θ) ≤ sin(2θ)`
    have hmin : min θ (Real.pi / 2 - θ) = θ := by
      refine min_eq_left ?_
      linarith
    rw [hmin]
    have hsin : (2 / Real.pi) * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith)
    calc θ = (Real.pi / 4) * ((2 / Real.pi) * (2 * θ)) := by
          field_simp
          ring
      _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsin (by positivity)
  · -- right half: `2(π/2 - θ) = π - 2θ ≤ π/2`, so `(2/π)·2(π/2 - θ) ≤ sin(π - 2θ) = sin(2θ)`
    have hmin : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := by
      refine min_eq_right ?_
      linarith
    rw [hmin]
    have hsin : (2 / Real.pi) * (2 * (Real.pi / 2 - θ))
        ≤ Real.sin (2 * (Real.pi / 2 - θ)) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have harg : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rw [harg] at hsin
    calc Real.pi / 2 - θ = (Real.pi / 4) * ((2 / Real.pi) * (2 * (Real.pi / 2 - θ))) := by
          field_simp
          ring
      _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsin (by positivity)

theorem weakSliceDerivBound (u : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (deriv u θ) ^ 2
          ≤ (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          |u θ| ≤ (Real.pi / 4) * Real.sin (2 * θ)
            * Real.sqrt ((∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
              * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) := by
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hB
  -- ## Smoothness of `u''` on the open interval
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hu 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2cont : ContinuousOn (fun θ => deriv (fun t => deriv u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  -- ## Integrability of `|u''|` on `Iθ` (from `hint` and `sEta ≥ 1`)
  have hint_abs : MeasureTheory.IntegrableOn
      (fun s => |deriv (fun t => deriv u t) s|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hd2cont hint
  -- ## Rolle: some interior point has `u' = 0`
  obtain ⟨c, hc, hcz⟩ := exists_deriv_eq_zero (f := u) (a := (0 : ℝ)) (b := Real.pi / 2)
    (by positivity) hcont (h0.trans h1.symm)
  -- ## Fundamental theorem of calculus: `|u' θ| ≤ ∫_{Iθ} |u''|`
  have hftc : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv u θ| ≤ ∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s| :=
    Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv hd1 hc hcz hint_abs
  -- ## Weighted Cauchy–Schwarz: `(∫_{Iθ} |u''|)² ≤ A · B`
  have hcs : (∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s|) ^ 2 ≤ A * B := by
    have h := Work.FTS.EllipticEst.sliceCSWeightedOpen
      (g := fun θ => deriv (fun t => deriv u t) θ) hd2cont hint
    simpa [hA, hB] using h
  -- ## First conjunct
  have hbound1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 ≤ A * B := by
    intro θ hθ
    have h1' := hftc θ hθ
    have h2 : |deriv u θ| ^ 2
        ≤ (∫ s in Work.Spaces.Iθ, |deriv (fun t => deriv u t) s|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1' 2
    rw [sq_abs] at h2
    linarith [h2, hcs]
  -- ## Second conjunct: mean-value bounds in `θ` and `(π/2 - θ)`
  have hsqrtnn : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
  have hbd : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), |deriv u x| ≤ Real.sqrt (A * B) := by
    intro x hx
    calc |deriv u x| = Real.sqrt ((deriv u x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt (hbound1 x hx)
  have hmvt := Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen
    (u := u) (M := Real.sqrt (A * B)) ((hu 2).differentiableOn (by norm_num)) hcont h0 h1 hbd
  refine ⟨fun θ hθ => by simpa [hA, hB] using hbound1 θ hθ, fun θ hθ => ?_⟩
  have hI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hleft := hmvt.1 θ hI
  have hright := hmvt.2 θ hI
  have hcase : |u θ| ≤ min θ (Real.pi / 2 - θ) * Real.sqrt (A * B) := by
    rcases le_total θ (Real.pi / 2 - θ) with hh | hh
    · rw [min_eq_left hh]; exact hleft
    · rw [min_eq_right hh]; exact hright
  have hmin := mul_le_mul_of_nonneg_right
    (min_le_sin_Iθ (le_of_lt hθ.1) (le_of_lt hθ.2)) hsqrtnn
  have hfinal : |u θ| ≤ (Real.pi / 4) * Real.sin (2 * θ) * Real.sqrt (A * B) :=
    le_trans hcase hmin
  simpa [hA, hB] using hfinal

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSliceBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonestBddOfSecondSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set Filter
open scoped Real Topology

/-- `Iθ = [0, π/2]` and the open interval `(0, π/2)` carry the same restricted Lebesgue
measure: they differ by the null set `{0, π/2}`. -/
private lemma restrict_Iθ_eq_Ioo' :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm

/-- **Integrability of a square from an a.e. bound.**  If `u` is a.e. strongly measurable on the
open interval `(0, π/2)` and `|u|` is bounded there by the constant `C`, then `u²` is integrable
on `Iθ = [0, π/2]` (which has finite measure). -/
private lemma integrableOn_sq_of_bdd {u : ℝ → ℝ} {C : ℝ}
    (haesm : AEStronglyMeasurable u (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
    (hbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ C) :
    IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ := by
  rw [MeasureTheory.IntegrableOn, restrict_Iθ_eq_Ioo']
  refine Integrable.of_bound (haesm.pow 2) (C ^ 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : |u θ| ^ 2 ≤ C ^ 2 := by
    have h0 := abs_nonneg (u θ)
    nlinarith [hbdd θ hθ]
  rwa [sq_abs] at h1

/-- `|sin θ · cos²θ| ≤ 1` for every real `θ`. -/
private lemma abs_sinCos2_le_one (θ : ℝ) : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  rw [Work.Elliptic.sinCos2, abs_mul]
  have h1 : |Real.sin θ| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact Real.cos_sq_le_one θ
  calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- **Boundedness and slice integrability from the `σ`-weighted `L²`-bound on `f''`.**

From `ContDiffOn ℝ 2 f (0,π/2)` and `∫_{Iθ} (f'')² σ < ∞` (`σ = sEta = sin(2θ)^{-η}`) we obtain:
`f` and `f'` are bounded on the open interval, `(f')²`, `f²` and `f · sinCos2` are integrable on
`Iθ = [0, π/2]`, and `f''` is integrable on the open interval.

The mechanism is that `σ ≥ 1` on `(0, π/2)` (since `0 < sin 2θ ≤ 1` there), so the hypothesis
forces `f'' ∈ L²(0, π/2) ⊂ L¹(0, π/2)`; the fundamental theorem of calculus from the interior
point `π/4` then bounds `f'` (and, once more, `f`) by `|f'(π/4)| + ∫|f''|` and
`|f(π/4)| + (π/2)·sup|f'|`. -/
theorem HonestBddOfSecondSq {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv f t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ B) ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ)
      (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  -- Boundedness of `f` and `f'` on the open interval, with a common constant.
  obtain ⟨C, hC0, hC⟩ := slice_bdd_of_sq_mul_sEta hf hint
  have hf1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  have hcontf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf1.continuousOn
  have hcontψ : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
      simp only [Work.Elliptic.sinCos2]; fun_prop
    exact h.continuousOn
  -- `(f')² ∈ L¹(Iθ)`
  have h3 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_bdd (measurable_deriv f).aestronglyMeasurable
      (fun θ hθ => (hC θ hθ).2)
  -- `f² ∈ L¹(Iθ)`
  have h4 : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_bdd (hcontf.aestronglyMeasurable measurableSet_Ioo)
      (fun θ hθ => (hC θ hθ).1)
  -- `f'' ∈ L¹((0, π/2))`
  have h5 : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsq := Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta f hint
    have habs := Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq f hsq
    refine MeasureTheory.Integrable.mono' habs
      (measurable_deriv (fun t : ℝ => deriv f t)).aestronglyMeasurable ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
  -- `f · sinCos2 ∈ L¹(Iθ)`
  have h6 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, restrict_Iθ_eq_Ioo']
    refine MeasureTheory.Integrable.of_bound
      ((hcontf.mul hcontψ).aestronglyMeasurable measurableSet_Ioo) (max C 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    calc |f θ| * |Work.Elliptic.sinCos2 θ| ≤ C * 1 :=
          mul_le_mul (hC θ hθ).1 (abs_sinCos2_le_one θ) (abs_nonneg _) hC0
      _ = C := by ring
      _ ≤ max C 0 := le_max_left _ _
  exact ⟨⟨C, hC0, fun θ hθ => (hC θ hθ).2⟩, ⟨C, hC0, fun θ hθ => (hC θ hθ).1⟩, h3, h4, h5, h6⟩

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.sliceBarSq2_boundary_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter

namespace Work.FTS.EllipticEst.Honest

/-- **The `π/2⁻` boundary term of the honest slice estimate vanishes.**

If `u θ / cos θ` has a finite limit `c` as `θ → (π/2)⁻`, then
`ρ(θ)·(u θ / cos θ)² → 0`, where `ρ = sin θ cos θ sin(2θ)^{-η}` vanishes like
`sin(2θ)^{1-η}` with `1 - η = 1/100 > 0`.

The limit `(u θ / cos θ)² → c²` is eventually bounded, so the product with `ρ → 0`
converges to `0` by `tendsto_wrho_mul_sq_zero`. -/
theorem sliceBarSq2_boundary_tendsto (u : ℝ → ℝ)
    (hlim : ∃ c : ℝ, Filter.Tendsto (fun θ => u θ / Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c)) :
    Filter.Tendsto (fun b => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta b
        * (u b / Real.cos b) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨c, hc⟩ := hlim
  -- the ratio `u θ / cos θ` is eventually bounded by `‖c‖ + 1`
  have hbdd : ∀ᶠ b in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      ‖u b / Real.cos b‖ ≤ ‖c‖ + 1 := by
    filter_upwards [hc.norm.eventually
      (eventually_lt_nhds (show ‖c‖ < ‖c‖ + 1 by linarith))] with b hb
    exact le_of_lt hb
  exact Work.FTS.EllipticEst.TanTheta.tendsto_wrho_mul_sq_zero hbdd
    (Work.FTS.EllipticEst.TanTheta.wrho_tendsto_zero_left Work.Spaces.eta
      (by linarith [Work.Spaces.eta_lt_one]))

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.MixedSlotAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-! ## The box, the support predicate, and basic two-variable calculus -/



/-- The half strip `(0,∞) × (0,π/2)` on which `v` is smooth. -/
def MStrip : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_MStrip : IsOpen MStrip := isOpen_Ioi.prod isOpen_Ioo



/-- `f` vanishes off the open box. -/
def Van (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ, z ∉ Set.Ioo (1 / 2 : ℝ) 2 ∨ θ ∉ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8) → f z θ = 0

theorem Van.mul {f g : ℝ → ℝ → ℝ} (hf : Van f) : Van (fun z θ => f z θ * g z θ) :=
  fun z θ h => by show f z θ * g z θ = 0; rw [hf z θ h, zero_mul]


theorem Van.neg {f : ℝ → ℝ → ℝ} (hf : Van f) : Van (fun z θ => -f z θ) :=
  fun z θ h => by show -f z θ = 0; rw [hf z θ h, neg_zero]

theorem Van.sq {f : ℝ → ℝ → ℝ} (hf : Van f) : Van (fun z θ => (f z θ) ^ 2) :=
  fun z θ h => by show (f z θ) ^ 2 = 0; rw [hf z θ h]; ring


/-- `D_z f = z·∂_z f` vanishes off the box as soon as `∂_z f` does. -/
theorem Van.Dz {f : ℝ → ℝ → ℝ} (hf : Van (Work.Spaces.pz f)) : Van (Work.Spaces.Dz f) := by
  intro z θ h
  show z * Work.Spaces.pz f z θ = 0
  rw [hf z θ h, mul_zero]

/-- The curried `z`-partial of a two-variable function is differentiable at a point where the
function is differentiable. -/
theorem differentiableAt_curry_left {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry f) (z, θ)) :
    DifferentiableAt ℝ (fun z' => f z' θ) z := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  have hh := (h.hasFDerivAt.comp_hasDerivAt z hcurve).differentiableAt
  have hmem : (Function.uncurry f ∘ fun t : ℝ => (t, θ)) = fun z' => f z' θ := rfl
  rwa [hmem] at hh

/-- The curried `θ`-partial of a two-variable function is differentiable at a point where the
function is differentiable. -/
theorem differentiableAt_curry_right {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry f) (z, θ)) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  have hh := (h.hasFDerivAt.comp_hasDerivAt θ hcurve).differentiableAt
  have hmem : (Function.uncurry f ∘ fun t : ℝ => (z, t)) = fun θ' => f z θ' := rfl
  rwa [hmem] at hh

/-- Membership tests for the box intervals, in the direction in which they are used. -/
theorem notMem_Ioo_of_le {y a b : ℝ} (h : y ≤ a) : y ∉ Set.Ioo a b :=
  fun hy => absurd hy.1 (not_lt.mpr h)

theorem notMem_Ioo_of_ge {y a b : ℝ} (h : b ≤ y) : y ∉ Set.Ioo a b :=
  fun hy => absurd hy.2 (not_lt.mpr h)

/-- Joint smoothness on an open set implies smoothness at each of its points. -/
theorem contDiffAt_of_contDiffOn {f : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : WithTop ℕ∞} (h : ContDiffOn ℝ n (Function.uncurry f) U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ContDiffAt ℝ n (Function.uncurry f) p :=
  (h.contDiffWithinAt hp).contDiffAt (hU.mem_nhds hp)



/-- If a function differentiable at `x` vanishes on `(-∞,x]`, then its derivative at `x` is `0`. -/
theorem deriv_eq_zero_of_eq_zero_of_forall_le {g : ℝ → ℝ} {x : ℝ}
    (hd : DifferentiableAt ℝ g x) (h0 : ∀ y, y ≤ x → g y = 0) : deriv g x = 0 := by
  have h1 : HasDerivWithinAt g (deriv g x) (Set.Iio x) x := hd.hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt g 0 (Set.Iio x) x :=
    (hasDerivWithinAt_const x (Set.Iio x) 0).congr (fun y hy => h0 y (le_of_lt hy))
      (h0 x le_rfl)
  have e1 := h1.derivWithin (uniqueDiffWithinAt_Iio x)
  have e2 := h2.derivWithin (uniqueDiffWithinAt_Iio x)
  rw [e2] at e1
  exact e1.symm

/-- If a function differentiable at `x` vanishes on `[x,∞)`, then its derivative at `x` is `0`. -/
theorem deriv_eq_zero_of_eq_zero_of_forall_ge {g : ℝ → ℝ} {x : ℝ}
    (hd : DifferentiableAt ℝ g x) (h0 : ∀ y, x ≤ y → g y = 0) : deriv g x = 0 := by
  have h1 : HasDerivWithinAt g (deriv g x) (Set.Ioi x) x := hd.hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt g 0 (Set.Ioi x) x :=
    (hasDerivWithinAt_const x (Set.Ioi x) 0).congr (fun y hy => h0 y (le_of_lt hy))
      (h0 x le_rfl)
  have e1 := h1.derivWithin (uniqueDiffWithinAt_Ioi x)
  have e2 := h2.derivWithin (uniqueDiffWithinAt_Ioi x)
  rw [e2] at e1
  exact e1.symm

/-- `pz` preserves vanishing off the box (for a function smooth on the half strip). -/
theorem Van.pz {f : ℝ → ℝ → ℝ} (hvan : Van f)
    (hc : ContDiffOn ℝ 1 (Function.uncurry f) MStrip) : Van (Work.Spaces.pz f) := by
  intro z θ h
  rw [show Work.Spaces.pz f z θ = deriv (fun z' => f z' θ) z from rfl]
  by_cases hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · rcases lt_or_ge z (1 / 2) with hlt | hge
    · have hev : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [isOpen_Ioo.mem_nhds
          (show z ∈ Set.Ioo (z - 1) (1 / 2) from ⟨by linarith, hlt⟩)] with y hy
        exact hvan y θ (Or.inl (notMem_Ioo_of_le (le_of_lt hy.2)))
      rw [hev.deriv_eq]; simp
    · by_cases hzb : z ∈ Set.Ioo (1 / 2 : ℝ) 2
      · have hθb : θ ∉ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8) := by
          rcases h with h' | h'
          · exact absurd hzb h'
          · exact h'
        have h0 : ∀ z' : ℝ, f z' θ = 0 := fun z' => hvan z' θ (Or.inr hθb)
        rw [show (fun z' : ℝ => f z' θ) = fun _ => 0 from funext h0]
        simp
      · rcases eq_or_lt_of_le hge with heq | hlt2
        · obtain rfl : z = (1 / 2 : ℝ) := heq.symm
          refine deriv_eq_zero_of_eq_zero_of_forall_le ?_ ?_
          · have hmem : ((1 / 2 : ℝ), θ) ∈ MStrip := by
              simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
              exact ⟨by norm_num, hθ⟩
            exact differentiableAt_curry_left
              ((contDiffAt_of_contDiffOn isOpen_MStrip hc hmem).differentiableAt one_ne_zero)
          · intro y hy
            exact hvan y θ (Or.inl (notMem_Ioo_of_le hy))
        · have hz2 : (2 : ℝ) ≤ z := by
            by_contra hc'
            exact hzb ⟨hlt2, not_le.mp hc'⟩
          rcases lt_or_eq_of_le hz2 with hlt' | heq
          · have hev : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun _ => 0) := by
              filter_upwards [isOpen_Ioo.mem_nhds
                (show z ∈ Set.Ioo (2 : ℝ) (z + 1) from ⟨hlt', by linarith⟩)] with y hy
              exact hvan y θ (Or.inl (notMem_Ioo_of_ge (le_of_lt hy.1)))
            rw [hev.deriv_eq]; simp
          · obtain rfl : z = (2 : ℝ) := heq.symm
            refine deriv_eq_zero_of_eq_zero_of_forall_ge ?_ ?_
            · have hmem : ((2 : ℝ), θ) ∈ MStrip := by
                simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
                exact ⟨by norm_num, hθ⟩
              exact differentiableAt_curry_left
                ((contDiffAt_of_contDiffOn isOpen_MStrip hc hmem).differentiableAt one_ne_zero)
            · intro y hy
              exact hvan y θ (Or.inl (notMem_Ioo_of_ge hy))
  · have h0 : ∀ z' : ℝ, f z' θ = 0 := fun z' => by
      by_cases hz' : z' ∈ Set.Ioo (1 / 2 : ℝ) 2
      · exact hvan z' θ (Or.inr (fun hθb =>
          hθ ⟨by linarith [hθb.1, Real.pi_pos], by linarith [hθb.2, Real.pi_pos]⟩))
      · exact hvan z' θ (Or.inl hz')
    rw [show (fun z' : ℝ => f z' θ) = fun _ => 0 from funext h0]
    simp

/-- `pth` preserves vanishing off the box (for a function smooth on the half strip). -/
theorem Van.pth {f : ℝ → ℝ → ℝ} (hvan : Van f)
    (hc : ContDiffOn ℝ 1 (Function.uncurry f) MStrip) : Van (Work.Spaces.pth f) := by
  intro z θ h
  rw [show Work.Spaces.pth f z θ = deriv (fun θ' => f z θ') θ from rfl]
  by_cases hz : z ∈ Set.Ioo (1 / 2 : ℝ) 2
  · have hθb : θ ∉ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8) := by
      rcases h with h' | h'
      · exact absurd hz h'
      · exact h'
    rcases lt_or_ge θ (Real.pi / 8) with hlt | hge
    · have hev : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun _ => 0) := by
        filter_upwards [isOpen_Ioo.mem_nhds
          (show θ ∈ Set.Ioo (θ - 1) (Real.pi / 8) from ⟨by linarith, hlt⟩)] with y hy
        exact hvan z y (Or.inr (notMem_Ioo_of_le (le_of_lt hy.2)))
      rw [hev.deriv_eq]; simp
    · rcases eq_or_lt_of_le hge with heq | hlt2
      · obtain rfl : θ = Real.pi / 8 := heq.symm
        refine deriv_eq_zero_of_eq_zero_of_forall_le ?_ ?_
        · have hmem : (z, Real.pi / 8) ∈ MStrip := by
            simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
            exact ⟨by linarith [hz.1], ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
          exact differentiableAt_curry_right
            ((contDiffAt_of_contDiffOn isOpen_MStrip hc hmem).differentiableAt one_ne_zero)
        · intro y hy
          exact hvan z y (Or.inr (notMem_Ioo_of_le hy))
      · have hge3 : 3 * Real.pi / 8 ≤ θ := by
          by_contra hc'
          exact hθb ⟨hlt2, not_le.mp hc'⟩
        rcases lt_or_eq_of_le hge3 with hlt' | heq2
        · have hev : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun _ => 0) := by
            filter_upwards [isOpen_Ioo.mem_nhds
              (show θ ∈ Set.Ioo (3 * Real.pi / 8) (θ + 1) from ⟨hlt', by linarith⟩)] with y hy
            exact hvan z y (Or.inr (notMem_Ioo_of_ge (le_of_lt hy.1)))
          rw [hev.deriv_eq]; simp
        · obtain rfl : θ = 3 * Real.pi / 8 := heq2.symm
          refine deriv_eq_zero_of_eq_zero_of_forall_ge ?_ ?_
          · have hmem : (z, 3 * Real.pi / 8) ∈ MStrip := by
              simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
              exact ⟨by linarith [hz.1], ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
            exact differentiableAt_curry_right
              ((contDiffAt_of_contDiffOn isOpen_MStrip hc hmem).differentiableAt one_ne_zero)
          · intro y hy
            exact hvan z y (Or.inr (notMem_Ioo_of_ge hy))
  · have h0 : ∀ θ' : ℝ, f z θ' = 0 := fun θ' => by
      by_cases hθ' : θ' ∈ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8)
      · exact hvan z θ' (Or.inl (fun hz' => hz ⟨hz'.1, hz'.2⟩))
      · exact hvan z θ' (Or.inr hθ')
    rw [show (fun θ' : ℝ => f z θ') = fun _ => 0 from funext h0]
    simp

theorem Van.congr {f g : ℝ → ℝ → ℝ} (h : Van f) (hfg : ∀ z θ, f z θ = g z θ) : Van g :=
  fun z θ hh => by rw [← hfg z θ, h z θ hh]

/-! ## The weights, the fluxes and the four integrands -/

/-- The radial weight `w(z)²`. -/
def W2 (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The angular weight `sin(2θ)^q`. -/
def Sq (q : ℝ) (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ q


/-- The coefficient `(z-3)/(1+z)`. -/
def xi (z : ℝ) : ℝ := (z - 3) / (1 + z)

/-- The integrand of the left-hand side of the identity. -/
def FL (q : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Dz (Work.Spaces.pth v) z θ) ^ 2 * W2 z * Sq q θ












/-! ## Smoothness of the curried partials and of the weights -/

theorem pz_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pz G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (1, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  have hh := (h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv
  have hmem : (Function.uncurry G ∘ fun t : ℝ => (t, θ)) = fun z' => G z' θ := rfl
  rw [hmem] at hh
  show deriv (fun z' => G z' θ) z = _
  exact hh

theorem pth_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pth G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (0, 1) := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  have hh := (h.hasFDerivAt.comp_hasDerivAt θ hcurve).deriv
  have hmem : (Function.uncurry G ∘ fun t : ℝ => (z, t)) = fun θ' => G z θ' := rfl
  rw [hmem] at hh
  show deriv (fun θ' => G z θ') θ = _
  exact hh

/-- `∂_z` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pz_succ {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) :=
    fun p hp =>
      pz_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fderiv ℝ (Function.uncurry G)) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => by
    show Function.uncurry (Work.Spaces.pz G) p = fderiv ℝ (Function.uncurry G) p (1, 0)
    exact hchain p hp)

/-- `∂_θ` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pth_succ {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) :=
    fun p hp =>
      pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fderiv ℝ (Function.uncurry G)) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => by
    show Function.uncurry (Work.Spaces.pth G) p = fderiv ℝ (Function.uncurry G) p (0, 1)
    exact hchain p hp)




theorem contDiffOn_uncurry_z_mul {A : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n (Function.uncurry A) U) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => z * A z θ)) U :=
  (contDiffOn_fst.mul hA).congr (fun p _ => rfl)

theorem contDiffOn_uncurry_Dz {f : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (h : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz f)) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz f)) U := by
  unfold Work.Spaces.Dz
  exact contDiffOn_uncurry_z_mul h









/-! ## Vanishing of the elementary factors -/









/-! ## Smoothness and continuity of the pieces -/






/-! ## Reduction of the iterated integrals to the box, and linearity -/

/-- A function vanishing off `(0,π/2)` outside `[a,b]` has the same integral over both. -/
theorem setIntegral_Ioo_eq_intervalIntegral_of_support {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b)
    (hf : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → f θ = 0) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ) = ∫ θ in a..b, f θ := by
  have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ) = ∫ θ in Set.Icc a b, f θ :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
      (fun x hx => by
        have hx' : x ∉ Set.Icc a b := hx.2
        simp only [Set.mem_Icc, not_and_or, not_le] at hx'
        exact hf x hx.1.1 hx.1.2 hx')
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]




end Work.FTS.EllipticEst.Prop
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Cs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Cauchy–Schwarz bound `|∫ f χ f''| ≤ √A √D`
-/

namespace Work.FTS.EllipticEst.Prop.TraceLeftCore

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### The weighted Cauchy–Schwarz bound on the `f f''`-term -/


end

end Work.FTS.EllipticEst.Prop.TraceLeftCore
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two integrations by parts against the cutoff `χ`

`cutoff_ibp` produces the boundary term `F₀ L₀` and `cutoff_ibp_cross` moves the `χ'`-term onto
`χ''`.
-/

namespace Work.FTS.EllipticEst.Prop.TraceLeftCore

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### The first integration by parts -/


/-! ### The second integration by parts (the `χ'`-term) -/


end

end Work.FTS.EllipticEst.Prop.TraceLeftCore
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.slice_mixed_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the angular slice `(D_z^j D_θ^i f)² · sin(2θ)^{-γ}`

The mixed slot of the `H^k`-norm of the paper carries the singular angular weight
`thGam α θ = sin(2θ)^{-γ}`, `γ = gam α = 1 + α/10 ≥ 1`.  The weight alone is *not*
integrable on `Iθ = [0,π/2]` (it is not even bounded), but the extra vanishing of the
mixed derivative at the two angular endpoints saves the day: for `i ≥ 1` the operator
`D_θ = sin(2θ)∂_θ` carries an explicit factor `sin(2θ)`, so

  `|D_z^j D_θ^i f (z,θ)| ≤ C · sin(2θ)`  for all `θ ∈ Iθ`

(`Work.FTS.H2.mixed_sin_bound`).  Consequently the integrand is dominated by
`C² · sin(2θ)^{2-γ}` with `2 - γ > 0`, which is integrable on `Iθ`
(`Work.FTS.EllipticEst.integrableOn_sin_two_rpow`).  Only the almost-everywhere
measurability needs care, since the integrand is not continuous at the endpoints; it is
continuous on the co-null open interval `(0,π/2)` where `sin(2θ) > 0`.
-/

namespace Work.FTS.EllipticEst.RPFresh

open scoped Real Topology
open MeasureTheory Set Filter






end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.PthetaMem_of_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.first_iter_le_u =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- For `0 ≤ s ≤ 1`, `0 < γ` and `γ ≤ 2` one has `s ^ 2 * s ^ (-γ) ≤ 1`: it is the standard
comparison `s ^ (2 - γ) ≤ s ^ 0 = 1` (the case `s = 0` is trivial). -/
private lemma sq_mul_rpow_neg_le_one {s γ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 < γ) (hγ2 : γ ≤ 2) : s ^ 2 * s ^ (-γ) ≤ 1 := by
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow (show (-γ) ≠ 0 by linarith)]
    norm_num
  · rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_two s).symm,
      ← Real.rpow_add h (2 : ℝ) (-γ), show (2 : ℝ) + -γ = 2 - γ by ring]
    calc s ^ (2 - γ) ≤ s ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge h hs1 (by linarith)
      _ = 1 := Real.rpow_zero s


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.sliceBoundsOfTraceFts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

theorem sliceBoundsOfTraceFts {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hπ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) := by
  -- The weight `sin (2θ)^{-η}` is `≥ 1` on the open interval, so the hypothesis is stronger
  -- than the plain square-integrability of `f''`: `f'` (and `f`) are bounded.
  obtain ⟨C, hC0, hC⟩ := Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hf h2
  have hbd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C := fun θ hθ => (hC θ hθ).2
  -- The two endpoint limits turn the Lipschitz bound on `f` into the decay
  -- `|f θ| ≤ C·min θ (π/2 - θ)`.
  obtain ⟨hleft, hright⟩ := Work.FTS.EllipticEst.Honest.HonSliceAbsLe C hC0 f hf h0 hπ hbd
  refine ⟨C, hC0, ?_, hbd⟩
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_Iθ hθI
  -- `min θ (π/2 - θ) ≤ (π/4)·sin (2θ)`, from `sin (2θ) ≥ (4/π)·min θ (π/2 - θ)`.
  have hmin : min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
    have h := Work.FTS.H2.sin_two_ge_min θ hθI
    have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ Real.pi / 4 by positivity)
    have he : (Real.pi / 4) * ((4 / Real.pi) * min θ (Real.pi / 2 - θ))
        = min θ (Real.pi / 2 - θ) := by
      field_simp
    linarith [h', he.symm.le]
  calc |f θ| ≤ min (C * θ) (C * (Real.pi / 2 - θ)) := le_min (hleft θ hθ) (hright θ hθ)
    _ = C * min θ (Real.pi / 2 - θ) :=
        (mul_min_of_nonneg θ (Real.pi / 2 - θ) hC0).symm
    _ ≤ C * ((Real.pi / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hmin hC0
    _ = (C * (Real.pi / 4)) * Real.sin (2 * θ) := by ring
    _ ≤ C * Real.sin (2 * θ) := by
        apply mul_le_mul_of_nonneg_right _ hsin
        nlinarith [hC0, Real.pi_lt_four]

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.slice_ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

set_option autoImplicit false

/-! ## General helpers: the fundamental theorem of calculus on an open interval,
and integration by parts against a weight vanishing at both endpoints. -/

/-- **FTC-2 on an open interval.**  If `G` is differentiable on `(a,b)` with derivative `G'`,
`G'` is integrable there, and `G` has limits `m` at `a⁺` and `l` at `b⁻`, then
`∫_{a}^{b} G' = l - m`. -/
theorem integral_Ioo_eq_sub_of_tendsto {a b m l : ℝ} (hab : a < b) {G G' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt G (G' x) x)
    (hint : IntegrableOn G' (Set.Ioo a b))
    (hbot : Tendsto G (𝓝[>] a) (𝓝 m)) (htop : Tendsto G (𝓝[<] b) (𝓝 l)) :
    ∫ x in Set.Ioo a b, G' x = l - m := by
  have hle : a ≤ b := le_of_lt hab
  have hI : IntervalIntegrable G' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mpr hint
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hI hbot htop
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  exact h

/-- **Integration by parts against a weight vanishing at both endpoints.**  If
`(ρ f²) → 0` at `a⁺` and at `b⁻`, then `∫ ρ f f' = -(1/2) ∫ ρ' f²` on `(a,b)`. -/
theorem integral_Ioo_mul_deriv_eq_neg_half {a b : ℝ} (hab : a < b) {ρ ρ' f f' : ℝ → ℝ}
    (hρ : ∀ x ∈ Set.Ioo a b, HasDerivAt ρ (ρ' x) x)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint1 : IntegrableOn (fun x => ρ' x * f x ^ 2) (Set.Ioo a b))
    (hint2 : IntegrableOn (fun x => ρ x * f x * f' x) (Set.Ioo a b))
    (hbot : Tendsto (fun x => ρ x * f x ^ 2) (𝓝[>] a) (𝓝 0))
    (htop : Tendsto (fun x => ρ x * f x ^ 2) (𝓝[<] b) (𝓝 0)) :
    ∫ x in Set.Ioo a b, ρ x * f x * f' x = -(1 / 2) * ∫ x in Set.Ioo a b, ρ' x * f x ^ 2 := by
  have hderivG : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y => (1 / 2) * (ρ y * f y ^ 2))
        (ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2)) x := by
    intro x hx
    have h := ((hρ x hx).mul ((hf x hx).pow 2)).const_mul (1 / 2)
    have h2 : (2 : ℕ) - 1 = 1 := rfl
    rw [h2, pow_one] at h
    convert h using 1
    simp only [Pi.pow_apply]
    ring
  have hInt : IntegrableOn
      (fun x => ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2)) (Set.Ioo a b) :=
    hint2.add (hint1.const_mul (1 / 2))
  have hlim1 : Tendsto (fun y => (1 / 2) * (ρ y * f y ^ 2)) (𝓝[>] a) (𝓝 0) := by
    simpa using hbot.const_mul (1 / 2 : ℝ)
  have hlim2 : Tendsto (fun y => (1 / 2) * (ρ y * f y ^ 2)) (𝓝[<] b) (𝓝 0) := by
    simpa using htop.const_mul (1 / 2 : ℝ)
  have hFTC := integral_Ioo_eq_sub_of_tendsto hab hderivG hInt hlim1 hlim2
  simp only [sub_zero] at hFTC
  have hsplit : ∫ x in Set.Ioo a b, (ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2))
      = (∫ x in Set.Ioo a b, ρ x * f x * f' x)
        + (1 / 2) * ∫ x in Set.Ioo a b, ρ' x * f x ^ 2 := by
    rw [integral_add hint2 (hint1.const_mul (1 / 2)), integral_const_mul]
  rw [hsplit] at hFTC
  linarith [hFTC]

/-- An integrable function on `(0, π/2)` times a bounded measurable function is integrable. -/
theorem integrableOn_mul_of_bound {f g : ℝ → ℝ} {c : ℝ}
    (hf : IntegrableOn f (Set.Ioo 0 (Real.pi / 2)))
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ c) :
    IntegrableOn (fun θ => f θ * g θ) (Set.Ioo 0 (Real.pi / 2)) :=
  hf.mul_bdd hg (ae_restrict_of_forall_mem measurableSet_Ioo hb)


end Work.FTS.EllipticEst.TanTheta
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.AngIbp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two endpoint limits of the weight -/

/-- `θ ↦ θ ^ (1 - η)` tends to `0` as `θ → 0⁺` (since `1 - η = 1/100 > 0`). -/
theorem tendsto_rpow_one_sub_eta_nhdsGT_zero :
    Tendsto (fun θ : ℝ => θ ^ (1 - Work.Spaces.eta)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : Work.Spaces.eta - 1 < 0 := by
    have := Work.Spaces.eta_lt_one
    linarith
  have h1 := (tendsto_rpow_neg_nhdsGT_zero hp).inv_tendsto_atTop
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : 0 < θ := hθ
  show (θ ^ (Work.Spaces.eta - 1))⁻¹ = θ ^ (1 - Work.Spaces.eta)
  rw [show Work.Spaces.eta - 1 = -(1 - Work.Spaces.eta) by ring, Real.rpow_neg hθ0.le,
    inv_inv]

/-- `σ θ · θ → 0` as `θ → 0⁺`, `σ θ = sin(2θ)^{-η}`. -/
theorem tendsto_thEta_mul_self :
    Tendsto (fun θ : ℝ => thEta θ * θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_rpow_one_sub_eta_nhdsGT_zero
  · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)]
      with θ hθ
    refine mul_nonneg (thEta_nonneg ?_) hθ.1.le
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨hθ.1.le, hθ.2.le⟩
  · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4)]
      with θ hθ
    have hθpos : 0 < θ := hθ.1
    have hsin : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
      have h2θ : (2 : ℝ) * θ ≤ Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
      have h2θ0 : (0 : ℝ) ≤ 2 * θ := by linarith [hθpos]
      have hcoef : (2 / Real.pi) * (2 * θ) = (4 / Real.pi) * θ := by ring
      have := Real.mul_le_sin h2θ0 h2θ
      linarith [hcoef ▸ this]
    have hθle : θ ≤ Real.sin (2 * θ) := by
      have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
      have h2 : θ ≤ (4 / Real.pi) * θ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith [Real.pi_pos])]
        nlinarith
      linarith
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hθpos hθle
    have hb : Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) ≤ θ ^ (-(Work.Spaces.eta)) := by
      rw [Real.rpow_neg hsinpos.le, Real.rpow_neg hθpos.le, ← one_div, ← one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hθpos _)
        (Real.rpow_le_rpow hθpos.le hθle (le_of_lt Work.Spaces.eta_pos))
    calc thEta θ * θ = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * θ := rfl
      _ ≤ θ ^ (-(Work.Spaces.eta)) * θ := mul_le_mul_of_nonneg_right hb hθpos.le
      _ = θ ^ (1 - Work.Spaces.eta) := by
            rw [show (1 : ℝ) - Work.Spaces.eta = 1 + (-(Work.Spaces.eta)) by ring,
              Real.rpow_add hθpos 1 (-(Work.Spaces.eta)), Real.rpow_one]
            ring

/-- `θ ↦ (π/2 - θ) ^ (1 - η)` tends to `0` as `θ → (π/2)⁻`. -/
theorem tendsto_pi_sub_rpow_nhdsLT :
    Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - Work.Spaces.eta))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  refine tendsto_rpow_one_sub_eta_nhdsGT_zero.comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 (Real.pi / 2))
        (𝓝 (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact sub_pos.mpr (Set.mem_Iio.mp hθ)

/-- `σ θ · (π/2 - θ) → 0` as `θ → (π/2)⁻`, `σ θ = sin(2θ)^{-η}`. -/
theorem tendsto_thEta_mul_pi_sub :
    Tendsto (fun θ : ℝ => thEta θ * (Real.pi / 2 - θ)) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_pi_sub_rpow_nhdsLT
  · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2)]
      with θ hθ
    refine mul_nonneg (thEta_nonneg ?_) (by linarith [hθ.2])
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨hθ.1.le, hθ.2.le⟩
  · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2)]
      with θ hθ
    have hθ4 : Real.pi / 4 < θ := hθ.1
    have hθ2 : θ < Real.pi / 2 := hθ.2
    have hpos : 0 < Real.pi / 2 - θ := by linarith
    have hsin : (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
      have h := Real.mul_le_sin (x := 2 * (Real.pi / 2 - θ)) (by linarith)
        (by linarith [Real.pi_pos])
      have hcoef : (2 / Real.pi) * (2 * (Real.pi / 2 - θ)) = (4 / Real.pi) * (Real.pi / 2 - θ) := by
        ring
      have harg : 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) := by ring
      rw [harg, Real.sin_pi_sub]
      linarith [hcoef ▸ h]
    have hle : Real.pi / 2 - θ ≤ Real.sin (2 * θ) := by
      have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
      have h2 : Real.pi / 2 - θ ≤ (4 / Real.pi) * (Real.pi / 2 - θ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith [Real.pi_pos])]
        nlinarith
      linarith
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hpos hle
    have hb : Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        ≤ (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by
      rw [Real.rpow_neg hsinpos.le, Real.rpow_neg hpos.le, ← one_div, ← one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos _)
        (Real.rpow_le_rpow hpos.le hle (le_of_lt Work.Spaces.eta_pos))
    calc thEta θ * (Real.pi / 2 - θ)
        = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Real.pi / 2 - θ) := rfl
      _ ≤ (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) * (Real.pi / 2 - θ) :=
            mul_le_mul_of_nonneg_right hb hpos.le
      _ = (Real.pi / 2 - θ) ^ (1 - Work.Spaces.eta) := by
            rw [show (1 : ℝ) - Work.Spaces.eta = 1 + (-(Work.Spaces.eta)) by ring,
              Real.rpow_add hpos 1 (-(Work.Spaces.eta)), Real.rpow_one]
            ring


/-! ## Elementary rpow algebra at a positive point -/

theorem mul_rpow_neg_one_add {x : ℝ} (hx : 0 < x) (p : ℝ) :
    x * x ^ (-(1 + p)) = x ^ (-p) := by
  rw [show -p = 1 + -(1 + p) by ring, Real.rpow_add hx, Real.rpow_one]

theorem rpow_neg_one {x : ℝ} (hx : 0 < x) : x ^ (-1 : ℝ) = x⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_one]

theorem cot_mul_thEta {θ : ℝ} (hsin : 0 < Real.sin (2 * θ)) :
    Real.cot (2 * θ) * thEta θ = Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  have hkey : Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Real.sin (2 * θ))⁻¹
      = Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
    rw [← rpow_neg_one hsin, ← Real.rpow_add hsin]
    ring_nf
  rw [Real.cot_eq_cos_div_sin, thEta, div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc, hkey]

/-! ## Bounds for a `C²` slice vanishing at the endpoints -/

/-- The three bounds on a `C²` slice vanishing at `0` and `π/2` that the arguments below use:
the minimum bound on the slice itself (`Iθ`), and the bounds on the first and second derivative
on the open interval `(0,π/2)`. -/
theorem slice_bounds {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    ∃ C M₃ : ℝ, 0 ≤ C ∧ 0 ≤ M₃ ∧
      (∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C * min θ (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ C) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (deriv f) θ| ≤ M₃) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hf1 : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) := (hf.mono hsub).of_le (by norm_num)
  obtain ⟨C, hC0, hb1, hb2⟩ := Work.Elliptic.contDiffOn_one_bounds hf1 h0 h1
  have h2 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have h3 : ContinuousOn (deriv (deriv f)) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    h2.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have h3' : ContinuousOn (deriv (deriv f)) (Set.Icc 0 (Real.pi / 2)) := h3.mono hsub
  obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hpi.le⟩⟩
    (f := fun θ => |deriv (deriv f) θ|) h3'.abs
  refine ⟨C, |deriv (deriv f) x₀|, hC0, abs_nonneg _, ?_, ?_, ?_⟩
  · intro θ hθ
    exact hb1 θ hθ
  · intro θ hθ
    rw [← Real.norm_eq_abs]
    exact hb2 θ hθ
  · intro θ hθ
    exact isMaxOn_iff.mp hmax θ (Set.Ioo_subset_Icc_self hθ)

/-! ## Integrability of the three pieces of the `η`-weighted angular IBP -/

theorem integrableOn_ang_pieces {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => f θ * deriv (deriv f) θ * thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
      (fun θ => f θ * deriv f θ * Real.cot (2 * θ) * thEta θ) Work.Spaces.Iθ := by
  obtain ⟨C, M₃, hC0, hM₃0, hfb, hdb, hddb⟩ := slice_bounds hf h0 h1
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_pos.le
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- continuity of the three integrands on the open interval
  have hcont_f : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.continuousOn.mono hsub
  have hcont_f' : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (ContDiffOn.continuousOn_deriv_of_isOpen (n := 2) hf isOpen_Ioo (by norm_num)).mono hsub
  have hderiv_f : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hcont_f'' : ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hderiv_f.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono hsub
  have hsin_c : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hthEta_c : ContinuousOn thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsin_c.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
  -- the three majorant bounds on `(0,π/2)`
  have hbA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖(deriv f θ) ^ 2 * thEta θ‖
        ≤ C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by
    intro θ hθ
    have hs : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant_pi Work.Spaces.eta θ Work.Spaces.eta_pos (hIoo hθ)
    have hd : (deriv f θ) ^ 2 ≤ C ^ 2 := by
      have h := abs_le.mp (hdb θ hθ)
      nlinarith [h.1, h.2]
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (hIoo hθ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hthEta_nn)]
    calc (deriv f θ) ^ 2 * thEta θ ≤ C ^ 2 * thEta θ :=
          mul_le_mul_of_nonneg_right hd hthEta_nn
      _ ≤ C ^ 2 * ((Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left hs (sq_nonneg C)
      _ = C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by ring
  have hbB : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖f θ * deriv (deriv f) θ * thEta θ‖
        ≤ C * M₃ * (Real.pi / 2) * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by
    intro θ hθ
    have hs : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant_pi Work.Spaces.eta θ Work.Spaces.eta_pos (hIoo hθ)
    have hmin_nn : 0 ≤ min θ (Real.pi / 2 - θ) :=
      le_min hθ.1.le (by linarith [hθ.2])
    have hmin_le : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 :=
      le_trans (min_le_left _ _) hθ.2.le
    have hfa : |f θ| ≤ C * (Real.pi / 2) := by
      have := hfb θ (hIoo hθ)
      calc |f θ| ≤ C * min θ (Real.pi / 2 - θ) := this
        _ ≤ C * (Real.pi / 2) := mul_le_mul_of_nonneg_left hmin_le hC0
    have hda : |deriv (deriv f) θ| ≤ M₃ := hddb θ hθ
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (hIoo hθ)
    have hK : 0 ≤ C * M₃ * (Real.pi / 2) * (Real.pi / 4) ^ Work.Spaces.eta :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hM₃0) (by linarith [Real.pi_pos]))
        (Real.rpow_nonneg (by positivity) _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hthEta_nn]
    have h1 : |f θ| * |deriv (deriv f) θ| * thEta θ ≤ (C * (Real.pi / 2)) * M₃ * thEta θ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hfa hda (abs_nonneg _) (mul_nonneg hC0 (by linarith [Real.pi_pos])))
        hthEta_nn
    have h2 : (C * (Real.pi / 2)) * M₃ * thEta θ
        ≤ (C * (Real.pi / 2)) * M₃ * ((Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg hC0 (by linarith [Real.pi_pos])) hM₃0)
    calc |f θ| * |deriv (deriv f) θ| * thEta θ ≤ (C * (Real.pi / 2)) * M₃ * thEta θ := h1
      _ ≤ (C * (Real.pi / 2)) * M₃ * ((Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))) := h2
      _ = C * M₃ * (Real.pi / 2) * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by ring
  have hcot_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.cot (2 * θ)| * thEta θ ≤ Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
    have h1 : Real.cot (2 * θ) * thEta θ = Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) :=
      cot_mul_thEta hsin
    have h2 : |Real.cot (2 * θ)| * thEta θ
        = |Real.cos (2 * θ)| * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
      rw [← abs_of_nonneg (thEta_nonneg (hIoo hθ)), ← abs_mul, h1, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hsin.le _)]
    rw [h2]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hsin.le _) (Real.abs_cos_le_one _)
  have hbC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖f θ * deriv f θ * Real.cot (2 * θ) * thEta θ‖
        ≤ C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
    have hsin_nn : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hθp : 0 < θ := hθ.1
    have hπp : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hs : (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ (1 + Work.Spaces.eta)
            * (θ ^ (-(1 + Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant_pi (1 + Work.Spaces.eta) θ (by linarith) (hIoo hθ)
    have hcot := hcot_le θ hθ
    have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (hIoo hθ)
    have hda : |deriv f θ| ≤ C := hdb θ hθ
    have hmin_nn : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθp.le hπp.le
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (hIoo hθ)
    have hx1 : min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta)) ≤ θ ^ (-(Work.Spaces.eta)) := by
      calc min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta))
          ≤ θ * θ ^ (-(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hθp.le _)
        _ = θ ^ (-(Work.Spaces.eta)) := mul_rpow_neg_one_add hθp Work.Spaces.eta
    have hx2 : min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))
        ≤ (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by
      calc min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))
          ≤ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hπp.le _)
        _ = (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := mul_rpow_neg_one_add hπp Work.Spaces.eta
    have hK : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta) :=
      mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
    have hK2 : 0 ≤ C ^ 2 := sq_nonneg C
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hthEta_nn]
    -- now: `|f θ| * |deriv f θ| * |cot| * thEta θ ≤ ...`
    have step1 : |f θ| * |deriv f θ| * |Real.cot (2 * θ)| * thEta θ
        = |f θ| * |deriv f θ| * (|Real.cot (2 * θ)| * thEta θ) := by ring
    rw [step1]
    have step2 : |f θ| * |deriv f θ| * (|Real.cot (2 * θ)| * thEta θ)
        ≤ (C * min θ (Real.pi / 2 - θ)) * C * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
      refine mul_le_mul (mul_le_mul hfa hda (abs_nonneg _) (mul_nonneg hC0 hmin_nn)) hcot
        (mul_nonneg (abs_nonneg _) hthEta_nn) (mul_nonneg (mul_nonneg hC0 hmin_nn) hC0)
    have step3 : (C * min θ (Real.pi / 2 - θ)) * C * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta))
        ≤ (C * min θ (Real.pi / 2 - θ)) * C * ((Real.pi / 4) ^ (1 + Work.Spaces.eta)
            * (θ ^ (-(1 + Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg hC0 hmin_nn) hC0)
    have step4 : (C * min θ (Real.pi / 2 - θ)) * C * ((Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (θ ^ (-(1 + Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))))
        = C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta))
            + min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))) := by
      ring
    have step5 : C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta))
            + min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))
        ≤ C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
      mul_le_mul_of_nonneg_left (add_le_add hx1 hx2) hK
    calc |f θ| * |deriv f θ| * (|Real.cot (2 * θ)| * thEta θ)
        ≤ (C * min θ (Real.pi / 2 - θ)) * C * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := step2
      _ ≤ (C * min θ (Real.pi / 2 - θ)) * C * ((Real.pi / 4) ^ (1 + Work.Spaces.eta)
            * (θ ^ (-(1 + Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))) := step3
      _ = C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta))
            + min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))) := step4
      _ ≤ C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := step5
  refine ⟨?_, ?_, ?_⟩
  · exact Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1
      (C := C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta)
      (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _))
      (hcont_f'.pow 2 |>.mul hthEta_c) (fun θ hθ => by
        rw [Real.norm_eq_abs]; exact hbA θ hθ)
  · exact Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1
      (C := C * M₃ * (Real.pi / 2) * (Real.pi / 4) ^ Work.Spaces.eta)
      (mul_nonneg (mul_nonneg (mul_nonneg hC0 hM₃0) (by linarith [Real.pi_pos]))
        (Real.rpow_nonneg (by positivity) _))
      ((hcont_f.mul hcont_f'').mul hthEta_c) hbB
  · refine Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1
      (C := C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
      (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)) ?_ hbC
    have hcos_c : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have hcot_c : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      refine ContinuousOn.congr (hcos_c.div hsin_c (fun θ hθ => hsinne θ hθ)) (fun θ hθ => ?_)
      simpa using Real.cot_eq_cos_div_sin (2 * θ)
    exact ((hcont_f.mul hcont_f').mul hcot_c).mul hthEta_c

/-! ## The endpoint limits of the primitive -/

theorem tendsto_primitive_nhdsGT_zero {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1))) (h0 : f 0 = 0)
    (h1 : f (Real.pi / 2) = 0) :
    Tendsto (fun θ => thEta θ * (f θ * deriv f θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, M₃, hC0, hM₃0, hfb, hdb, hddb⟩ := slice_bounds hf h0 h1
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun θ => C ^ 2 * (thEta θ * θ)) ?_ ?_ ?_
  · filter_upwards with θ
    exact norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsGT hpi] with θ hθ
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (Set.Ioo_subset_Icc_self hθ)
    have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (Set.Ioo_subset_Icc_self hθ)
    have hda : |deriv f θ| ≤ C := hdb θ hθ
    have hmin : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
    have hmin_nn : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ.1.le (by linarith [hθ.2])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hthEta_nn, abs_mul]
    have h1 : |f θ| * |deriv f θ| ≤ C * θ * C := by
      refine mul_le_mul (le_trans hfa (mul_le_mul_of_nonneg_left hmin hC0)) hda (abs_nonneg _)
        (mul_nonneg hC0 hθ.1.le)
    calc thEta θ * (|f θ| * |deriv f θ|) ≤ thEta θ * (C * θ * C) :=
          mul_le_mul_of_nonneg_left h1 hthEta_nn
      _ = C ^ 2 * (thEta θ * θ) := by ring
  · simpa using tendsto_thEta_mul_self.const_mul (C ^ 2)

theorem tendsto_primitive_nhdsLT_pi {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1))) (h0 : f 0 = 0)
    (h1 : f (Real.pi / 2) = 0) :
    Tendsto (fun θ => thEta θ * (f θ * deriv f θ)) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  obtain ⟨C, M₃, hC0, hM₃0, hfb, hdb, hddb⟩ := slice_bounds hf h0 h1
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun θ => C ^ 2 * (thEta θ * (Real.pi / 2 - θ))) ?_ ?_ ?_
  · filter_upwards with θ
    exact norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsLT hpi] with θ hθ
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (Set.Ioo_subset_Icc_self hθ)
    have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (Set.Ioo_subset_Icc_self hθ)
    have hda : |deriv f θ| ≤ C := hdb θ hθ
    have hmin : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
    have hmin_nn : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ.1.le (by linarith [hθ.2])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hthEta_nn, abs_mul]
    have h1 : |f θ| * |deriv f θ| ≤ C * (Real.pi / 2 - θ) * C := by
      refine mul_le_mul (le_trans hfa (mul_le_mul_of_nonneg_left hmin hC0)) hda (abs_nonneg _)
        (mul_nonneg hC0 (by linarith [hθ.2]))
    calc thEta θ * (|f θ| * |deriv f θ|) ≤ thEta θ * (C * (Real.pi / 2 - θ) * C) :=
          mul_le_mul_of_nonneg_left h1 hthEta_nn
      _ = C ^ 2 * (thEta θ * (Real.pi / 2 - θ)) := by ring
  · simpa using tendsto_thEta_mul_pi_sub.const_mul (C ^ 2)

/-! ## The angular integration by parts -/

theorem ang_ibp_eta {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * thEta θ)
      = - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * thEta θ)
        + 2 * Work.Spaces.eta
            * (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * Real.cot (2 * θ) * thEta θ) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hA, hB, hC⟩ := integrableOn_ang_pieces hf h0 h1
  -- the derivative of the primitive
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ => thEta θ * (f θ * deriv f θ))
        ((deriv f θ) ^ 2 * thEta θ + (f θ * deriv (deriv f) θ * thEta θ
          - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ))) θ := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
    have hmem : (θ : ℝ) ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hs2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
      have h1' : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1'
    have hsig : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta)))
        (-(2 * Work.Spaces.eta) * (Real.cot (2 * θ) * thEta θ)) θ := by
      have hbase := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ)) (p := -(Work.Spaces.eta))
        (Or.inl hsin.ne')).comp θ hs2
      refine hbase.congr_deriv ?_
      rw [cot_mul_thEta hsin]
      rw [show -(Work.Spaces.eta) - 1 = -(1 + Work.Spaces.eta) by ring]
      ring
    have hdf : HasDerivAt f (deriv f θ) θ :=
      ((hf.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt two_ne_zero).hasDerivAt
    have hdf' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ := by
      have hcd : ContDiffAt ℝ 1 (deriv f) θ :=
        (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).contDiffAt (isOpen_Ioo.mem_nhds hmem)
      exact (hcd.differentiableAt one_ne_zero).hasDerivAt
    have hall := hsig.mul (hdf.mul hdf')
    have hfun : (fun θ : ℝ => thEta θ * (f θ * deriv f θ))
        = (fun θ' : ℝ => Real.sin (2 * θ') ^ (-(Work.Spaces.eta))) * (f * deriv f) := by
      funext θ'
      simp only [thEta, Pi.mul_apply]
    rw [hfun]
    have hval : ((deriv f θ) ^ 2 * thEta θ + (f θ * deriv (deriv f) θ * thEta θ
          - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ)))
        = (-(2 * Work.Spaces.eta) * (Real.cot (2 * θ) * thEta θ) * (f * deriv f) θ
            + Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
              * (deriv f θ * deriv f θ + f θ * deriv (deriv f) θ)) := by
      simp only [Pi.mul_apply, thEta]
      ring
    rw [hval]
    exact hall
  -- interval integrability of the derivative
  have hintA : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * thEta θ) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hA.mono_set Set.Ioc_subset_Icc_self)
  have hintB : IntervalIntegrable (fun θ => f θ * deriv (deriv f) θ * thEta θ) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hB.mono_set Set.Ioc_subset_Icc_self)
  have hintC : IntervalIntegrable
      (fun θ => f θ * deriv f θ * Real.cot (2 * θ) * thEta θ) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hC.mono_set Set.Ioc_subset_Icc_self)
  have hint : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * thEta θ
      + (f θ * deriv (deriv f) θ * thEta θ
        - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ)))
      volume 0 (Real.pi / 2) :=
    hintA.add (hintB.sub (hintC.const_mul _))
  -- the fundamental theorem of calculus
  have hFTC : ∫ θ in (0 : ℝ)..(Real.pi / 2), ((deriv f θ) ^ 2 * thEta θ
      + (f θ * deriv (deriv f) θ * thEta θ
        - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ))) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
      (b := Real.pi / 2) hpi hderiv hint
      (tendsto_primitive_nhdsGT_zero hf h0 h1) (tendsto_primitive_nhdsLT_pi hf h0 h1)
    simpa using h
  -- convert the three set integrals to interval integrals
  have hconv : ∀ g : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  rw [hconv (fun θ => (deriv f θ) ^ 2 * thEta θ),
    hconv (fun θ => f θ * deriv (deriv f) θ * thEta θ),
    hconv (fun θ => f θ * deriv f θ * Real.cot (2 * θ) * thEta θ)]
  -- split the integral
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2), ((deriv f θ) ^ 2 * thEta θ
      + (f θ * deriv (deriv f) θ * thEta θ
        - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ))))
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv f θ) ^ 2 * thEta θ)
        + (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ * deriv (deriv f) θ * thEta θ)
        - 2 * Work.Spaces.eta
            * (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ * deriv f θ * Real.cot (2 * θ) * thEta θ) := by
    rw [intervalIntegral.integral_add hintA (hintB.sub (hintC.const_mul _)),
      intervalIntegral.integral_sub hintB (hintC.const_mul _),
      intervalIntegral.integral_const_mul]
    ring
  linarith [hFTC, hsplit]

end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.K1Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The strip of smoothness of the hypothesis of the open interpolation statement. -/
def OStrip : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem isOpen_OStrip : IsOpen OStrip := isOpen_Ioi.prod isOpen_Ioo

/-! ## Smoothness of the derived functions on the strip -/

theorem contDiffOn_uncurry_pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) OStrip) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) OStrip := by
  have hchain : ∀ p ∈ OStrip,
      Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_OStrip.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) OStrip :=
    h.fderiv_of_isOpen isOpen_OStrip (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) OStrip :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

theorem contDiffOn_uncurry_pth_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) OStrip) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) OStrip := by
  have hchain : ∀ p ∈ OStrip,
      Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_OStrip.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) OStrip :=
    h.fderiv_of_isOpen isOpen_OStrip (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) OStrip :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

theorem contDiffOn_uncurry_Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) OStrip) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) OStrip := by
  have hpz := contDiffOn_uncurry_pz_fin h
  have hfun : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) OStrip :=
    contDiff_fst.contDiffOn.mul hpz
  refine hfun.congr (fun p hp => ?_)
  rfl

/-! ## Clairaut identities -/

theorem pth_Dz_eq {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz G) z θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz G) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz G z θ') θ = z * Work.Spaces.pth (Work.Spaces.pz G) z θ
    rw [deriv_const_mul_field]
    rfl
  rw [h1, ← Work.Spaces.pz_pth_comm h]
  rfl

theorem pth_pth_Dz_eq {G : ℝ → ℝ → ℝ} (hG : ContDiffOn ℝ 3 (Function.uncurry G) OStrip)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ
      = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := by
  have hmem : (z, θ) ∈ OStrip := ⟨hz, hθ⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) :=
    (hG.contDiffAt (isOpen_OStrip.mem_nhds hmem)).of_le (by norm_num)
  have hev : (fun θ' => Work.Spaces.pth (Work.Spaces.Dz G) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.Dz (Work.Spaces.pth G) z θ') := by
    have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ OStrip :=
      (isOpen_OStrip.preimage (continuous_const.prodMk continuous_id)).mem_nhds hmem
    filter_upwards [hnb] with θ' hθ'
    exact pth_Dz_eq ((hG.contDiffAt (isOpen_OStrip.mem_nhds hθ')).of_le (by norm_num))
  have h1 : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ
      = Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth G)) z θ := hev.deriv_eq
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth G)) (z, θ) :=
    (contDiffOn_uncurry_pth_fin (hG.of_le (by norm_num))).contDiffAt
      (isOpen_OStrip.mem_nhds hmem)
  rw [h1, pth_Dz_eq hcd2]

/-! ## Integrability of `w² σ F` for the product measure -/

/-- If `F` is continuous on the open quadrant of `(z,θ)`, is supported in `z ∈ [δ,R]` and is
bounded by `M` on the box, then `(z,θ) ↦ w z ² σ θ F z θ` is integrable for the product of
the restrictions of Lebesgue measure to `Iz` and `Iθ`. -/
theorem integrable_prod_quad_of_bound {δ R M : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ M) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * thEta θ * F z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right M 0
  have hMM' : M ≤ M' := le_max_left M 0
  -- the dominating function `M' · (w² 1_{[δ,R]}) ⊗ (σ 1_{Iθ})`
  have hAvol : MeasureTheory.Integrable
      ((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) MeasureTheory.volume := by
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    show ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Icc δ R)
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
    positivity
  have hBvol : MeasureTheory.Integrable
      (Work.Spaces.Iθ.indicator thEta) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      Work.FTS.EllipticEst.integrableOn_thEta.1
  have hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => M' * (((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) p.1
        * (Work.Spaces.Iθ.indicator thEta) p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ((hAvol.integrableOn).mul_prod (hBvol.integrableOn)).const_mul M'
  -- a.e. strong measurability from continuity on the open quadrant
  have hwcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.pow ?_ 2
    rw [show (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p => (1 + p.1) ^ 2 / p.1 ^ 2 from rfl]
    refine ContinuousOn.div ((continuous_const.add continuous_fst).continuousOn.pow 2)
      (continuous_fst.pow 2).continuousOn ?_
    intro p hp
    have hp0 : 0 < p.1 := hp.1
    positivity
  have hsincont : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hsinnene : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
      Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2]))
  have hσcont : ContinuousOn (fun p : ℝ × ℝ => thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    show ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2) ^ (-(Work.Spaces.eta))) _
    exact hsincont.rpow_const (fun p hp => Or.inl (hsinnene p hp))
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * thEta θ * F z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * thEta p.2 * F p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn
          (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (thEta p.2 * F p.1 p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hwcont.mul (hσcont.mul hFc)
      refine h1.congr (fun p hp => ?_)
      ring
    exact Work.Spaces.aesm_of_continuousOn_Qd
      (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)) hcont
  refine hg.mono' hAE ?_
  -- the pointwise domination, a.e. in the second variable
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ)
      (p := fun p : ℝ × ℝ => p.2 ∈ Work.Spaces.Iθ)
      (measurableSet_Icc.preimage measurable_snd)).mpr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iz) measurableSet_Ici]
      with b hb
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with c hc
    exact hc
  filter_upwards [hmem] with p hp
  have hthEta_nn : 0 ≤ thEta p.2 := thEta_nonneg hp
  have hw_nn : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  have hBnn : 0 ≤ (Work.Spaces.Iθ.indicator thEta) p.2 := by
    by_cases h : p.2 ∈ Work.Spaces.Iθ
    · rw [Set.indicator_of_mem h]; exact hthEta_nn
    · rw [Set.indicator_of_notMem h]
  have hAnn : 0 ≤ ((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) p.1 := by
    by_cases h : p.1 ∈ Set.Icc δ R
    · rw [Set.indicator_of_mem h]; exact hw_nn
    · rw [Set.indicator_of_notMem h]
  have hgnn : 0 ≤ M' * (((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) p.1
      * (Work.Spaces.Iθ.indicator thEta) p.2) := mul_nonneg hM'0 (mul_nonneg hAnn hBnn)
  rw [Real.norm_eq_abs]
  change |(Work.Spaces.w p.1) ^ 2 * thEta p.2 * F p.1 p.2|
      ≤ M' * (((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) p.1
        * (Work.Spaces.Iθ.indicator thEta) p.2)
  by_cases hmem : p.1 ∈ Set.Icc δ R
  · have hFb' : |F p.1 p.2| ≤ M := hFb p.1 hmem p.2 hp
    have h1 : |(Work.Spaces.w p.1) ^ 2 * thEta p.2 * F p.1 p.2|
        = (Work.Spaces.w p.1) ^ 2 * thEta p.2 * |F p.1 p.2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw_nn, abs_of_nonneg hthEta_nn]
    rw [h1, Set.indicator_of_mem hmem, Set.indicator_of_mem hp]
    have h2 : (Work.Spaces.w p.1) ^ 2 * thEta p.2 * |F p.1 p.2|
        ≤ (Work.Spaces.w p.1) ^ 2 * thEta p.2 * M' :=
      mul_le_mul_of_nonneg_left (le_trans hFb' hMM') (mul_nonneg hw_nn hthEta_nn)
    calc (Work.Spaces.w p.1) ^ 2 * thEta p.2 * |F p.1 p.2|
        ≤ (Work.Spaces.w p.1) ^ 2 * thEta p.2 * M' := h2
      _ = M' * ((Work.Spaces.w p.1) ^ 2 * thEta p.2) := by ring
  · have hFz : F p.1 p.2 = 0 := hF0 p.1 hmem p.2
    rw [hFz, mul_zero, abs_zero, Set.indicator_of_notMem hmem]
    simp

/-- A bound for a continuous function on the compact box `[δ,R] × Iθ`. -/
theorem exists_bound_box {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Icc δ R ×ˢ Work.Spaces.Iθ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ M := by
  have hbox : IsCompact (Set.Icc δ R ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc δ R ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)).Nonempty :=
    ⟨(δ, 0), ⟨⟨le_rfl, hδR.le⟩, ⟨le_rfl, by linarith [Real.pi_pos]⟩⟩⟩
  obtain ⟨p₀, -, hmax⟩ := hbox.exists_isMaxOn hne (f := fun p : ℝ × ℝ => |Function.uncurry f p|)
    hf.abs
  refine ⟨|Function.uncurry f p₀|, abs_nonneg _, fun z hz θ hθ => ?_⟩
  exact isMaxOn_iff.mp hmax (z, θ) ⟨hz, hθ⟩

/-- **Fubini for the weighted iterated integrals**: for a function `F` which is continuous on the
open quadrant, vanishes for `z ∉ [δ,R]` and is bounded on the box,
`∫_z w z ² (∫_θ F z θ σ θ) = ∫_θ (∫_z w z ² F z θ) σ θ`, `σ θ = sin(2θ)^{-η}`. -/
theorem fubini_w_thEta {δ R : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∃ Mb : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ))
      = ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * F z θ) * thEta θ := by
  obtain ⟨Mb, hMb⟩ := hFb
  have hInt := integrable_prod_quad_of_bound (δ := δ) (R := R) (M := Mb) hδ
    (F := F) hFc hF0 hMb
  have hswap := MeasureTheory.integral_integral_swap hInt
  have hL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ))
      = ∫ z, (∫ θ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
    rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)
        = ∫ θ in Work.Spaces.Iθ, (F z θ * thEta θ) * (Work.Spaces.w z) ^ 2 from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring,
      MeasureTheory.integral_mul_const]
    ring
  have hR : (∫ θ in Work.Spaces.Iθ,
        (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * F z θ) * thEta θ)
      = ∫ θ, (∫ z, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    change (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * F z θ) * thEta θ
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
    rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)
        = ∫ z in Work.Spaces.Iz, ((Work.Spaces.w z) ^ 2 * F z θ) * thEta θ from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      ring,
      MeasureTheory.integral_mul_const]
  rw [hL, hR, hswap]

/-- Integrability of the outer (`z`-)slice integral. -/
theorem integrable_outer_of_bound {δ R : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∃ Mb : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb) :
    MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  obtain ⟨Mb, hMb⟩ := hFb
  have hInt := integrable_prod_quad_of_bound (δ := δ) (R := R) (M := Mb) hδ
    (F := F) hFc hF0 hMb
  have h1 : MeasureTheory.Integrable
      (fun z => ∫ θ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hInt.integral_prod_left
  refine h1.congr ?_
  filter_upwards with z
  rw [show (fun θ => (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)
      = (fun θ => (F z θ * thEta θ) * (Work.Spaces.w z) ^ 2) from by funext θ; ring,
    MeasureTheory.integral_mul_const]
  ring



/-! ## The derived functions vanish off the support in `z` -/








end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.WeakMoment.Open.D2CsBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.WeakMoment.Open

/-- The weighted Cauchy–Schwarz bound for the second derivative `D2 u = u''` on the angular
slice `Iθ = [0, π/2]`, with the *explicit* constant `π/2`:

  `(∫_{Iθ} |u''|)² ≤ (∫_{Iθ} (u'')² sin(2θ)^{-η}) · (π/2)`.

Mathematics.  The Cauch–Schwarz step is the already-proved `sliceCSWeightedOpen`, which
needs only continuity of `u''` on the *open* interval:

  `(∫_{Iθ} |u''|)² ≤ (∫_{Iθ} (u'')² sin(2θ)^{-η}) · (∫_{Iθ} sin(2θ)^{η})`.

For the last factor, `θ ↦ sin(2θ)^η` is bounded by `1` on `Iθ` (since `0 ≤ sin(2θ) ≤ 1` there
and `η ≥ 0`), while `volume Iθ = π/2`; this is exactly the second component of
`Work.FTS.EllipticEst.integrableOn_sin_two_rpow` at `p = η`.

For the continuity input, `hsm 3` gives `ContDiffOn ℝ 3 u (Ioo 0 (π/2))`, and two applications
of `ContDiffOn.deriv_of_isOpen` (which requires the set to be open and the order to drop by at
most one) exhibit `u''` as `C¹`, hence continuous, on `(0, π/2)` (the endpoints of `Iθ` are a
null set and play no role in the slice integral). -/
theorem D2CsBound {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * (Real.pi / 2) := by
  -- `u''` is continuous on the *open* angular interval, from the hypothesis `hsm`.
  have hD2 : ContinuousOn (Work.FTS.EllipticEst.TT.D2 u)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h3 : ContDiffOn ℝ 3 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hsm 3
    have h2 : ContDiffOn ℝ 2 (fun t => deriv u t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      simpa only using h3.deriv_of_isOpen isOpen_Ioo (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have h1 : ContDiffOn ℝ 1 (fun θ => deriv (fun t => deriv u t) θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      simpa only using h2.deriv_of_isOpen isOpen_Ioo (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact h1.continuousOn
  -- The weighted Cauchy–Schwarz inequality of `sliceCSWeightedOpen`.
  have hcs := Work.FTS.EllipticEst.sliceCSWeightedOpen hD2 h
  -- The remaining factor is at most the length `π/2` of `Iθ`.
  have hle : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) ≤ Real.pi / 2 :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow Work.Spaces.eta_nonneg).2
  -- The weighted energy is nonnegative, so the right factor may be enlarged.
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sEta_nonneg hθ))
  calc (∫ θ in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := hcs
    _ ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left hle hnn

end Work.FTS.EllipticEst.WeakMoment.Open
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.hardyDiv_fin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Topology

/-- **Finite-order Hardy division (Elgindi's Lemma 2 / Hilbert-type inequality at finite
smoothness).**  For `j : ℕ`, `γ > -1`, `x₁ > 0` and `f` of class `C^{j+2}` on `(0,x₁]` with
`f → 0` at `0⁺` and `∫_0^{x₁} x^{2j-γ}(f^{(j+1)})² < ∞`:

`∫_0^{x₁} x^{2j-γ}((f/x)^{(j)})² ≤ C(1+γ)^{-2} ∫_0^{x₁} x^{2j-γ}(f^{(j+1)})²`

and the left-hand integrand is `IntegrableOn (Ioc 0 x₁)`.

The `C^∞`-smoothness ancestor of this statement is `Work.FTS.H2.DivQ.hardyA_le_W`
(`ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)`); here `⊤` is replaced by the finite order `j + 2`,
which is what the proof needs (continuity of `f/x` and its iterated derivatives up to order
`j+1`).  Suggested route: verbatim adaptation of the proof of `hardyA_le_W` (primitive identity
`x^{j+1}(f/x)^{(j)} = ∫_0^x s^j f^{(j+1)}`, pointwise quantitative bound
`x^{2j+1-γ}((f/x)^{(j)})² ≤ (1+γ)^{-1}∫_0^x s^{2j-γ}(f^{(j+1)})²`, sharp integration by parts with
constant `4/(1+γ)²`, and the truncation argument of
`Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc`). -/
theorem hardyDiv_fin (j : ℕ) (γ : ℝ) (hγ : -1 < γ) (x₁ : ℝ) (hx₁ : 0 < x₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
      ContDiffOn ℝ (j + 2) f (Set.Ioc 0 x₁) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2)
        (Set.Ioc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (j : ℝ) - γ)
          * (iteratedDeriv j (fun y : ℝ => f y / y) x) ^ 2) (Set.Ioc 0 x₁)
      ∧ (∫ x in (0 : ℝ)..x₁, x ^ (2 * (j : ℝ) - γ)
            * (iteratedDeriv j (fun y : ℝ => f y / y) x) ^ 2)
          ≤ C / (1 + γ) ^ 2 * (∫ x in (0 : ℝ)..x₁,
              x ^ (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2) := by
  refine ⟨6, by norm_num, ?_⟩
  intro f hf hf0 hB
  -- the hypothesis `ContDiffOn ℝ (j + 2) f` (order `↑j + 2 : WithTop ℕ∞`) in the form
  -- `ContDiffOn ℝ ((j+2 : ℕ) : WithTop ℕ∞) f`
  have hf' : ContDiffOn ℝ (((j + 2 : ℕ)) : WithTop ℕ∞) f (Set.Ioc 0 x₁) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hf
  set v : ℝ → ℝ := fun x => iteratedDeriv j (fun y : ℝ => f y / y) x with hv
  set u : ℝ → ℝ := fun x => x ^ (2 * (j : ℝ) - γ) * v x ^ 2 with hu
  set ua : ℝ → ℝ := fun x => |u x| with hua
  set w : ℝ → ℝ := fun x => x ^ (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2 with hw
  set Btot : ℝ := ∫ x in (0 : ℝ)..x₁, w x with hBtot
  have hgm : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) (fun z : ℝ => f z / z) (Set.Ioo 0 x₁) := by
    have h1 : ContDiffOn ℝ (((j + 2 : ℕ)) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
      hf'.mono Set.Ioo_subset_Ioc_self
    have h2 : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
      h1.of_le (by exact_mod_cast (show j ≤ j + 2 by omega))
    have hid : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) (fun y : ℝ => y) (Set.Ioo 0 x₁) :=
      contDiffOn_id
    have hdiv := h2.div hid
      (fun x hx => by simp only [Set.mem_Ioo] at hx; exact ne_of_gt hx.1)
    have hfun : (f / fun y : ℝ => y) = fun y : ℝ => f y / y := by
      funext y; rw [Pi.div_apply]
    rwa [hfun] at hdiv
  have hvcont : ContinuousOn v (Set.Ioo 0 x₁) := by
    rw [hv]
    exact Work.FTS.EllipticEst.remov.HardyFin.continuousOn_iteratedDeriv_Ioo_fin' hgm le_rfl
  have hucont : ContinuousOn u (Set.Ioo 0 x₁) := by
    rw [hu]
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hvcont.pow 2)
  have huacont : ContinuousOn ua (Set.Ioo 0 x₁) := by
    rw [hua]
    exact hucont.abs
  have htrunc0 :=
    Work.FTS.EllipticEst.remov.HardyFin.hardyA_trunc_bound_fin j γ x₁ hx₁ hγ (j + 2) le_rfl
      f hf' hf0 hB
  have htrunc : ∀ y x : ℝ, 0 < y → y < x → x < x₁ →
      (∫ t in y..x, ua t) ≤ 6 * Btot / (1 + γ) ^ 2 := by
    intro y x hy hyx hxx₁
    have heq : (∫ t in y..x, ua t) = ∫ t in y..x, u t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hyx.le] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
      simp only [hua]
      exact abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (sq_nonneg _))
    rw [heq]
    exact htrunc0 y x hy hyx hxx₁
  obtain ⟨hua_int, hua_bound⟩ :=
    Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc hx₁ (fun t => abs_nonneg (u t)) huacont htrunc
  have hu_int : MeasureTheory.IntegrableOn u (Set.Ioc 0 x₁) := by
    refine hua_int.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    exact abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (sq_nonneg _))
  refine ⟨?_, ?_⟩
  · exact hu_int
  · have heq_final : (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t
      intro ht
      rw [Set.uIoc_of_le hx₁.le] at ht
      simp only [hua]
      exact (abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _))).symm
    calc (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := heq_final
      _ ≤ 6 * Btot / (1 + γ) ^ 2 := hua_bound
      _ = 6 / (1 + γ) ^ 2 * Btot := by ring

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.middleRegionLHS_i =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The middle-region bound, with the data hypothesis at the level actually needed.**

This is `middleRegionLHS` with its hypothesis `∀ m ∈ Finset.Icc 1 4, IntegrableOn (Denγ m)`
*wakened* to `∀ m ∈ Finset.Icc 1 i` (the right-hand side already sums only over `m ≤ i`, and the
proof only ever uses the data at levels `m < i`).  The weakening is what makes the result applicable
to the slices `h_b = fun θ => DzIter b Φ z θ` with `b ≥ 1`, for which `HkMem α 4 (pth Φ)` certifies
the data only when `m + b ≤ 4`, while the assembly needs the bound at level `i ≤ 4 - b`.
The proof body of `middleRegionLHS` carries over verbatim: its only use of the data hypothesis is
inside its `hBm`, at levels `1 ≤ m ≤ i`, and the `m = 0` term uses the unchanged `η`-weighted
hypothesis. -/
theorem middleRegionLHS_i :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨K, hKpos, hKb⟩ := divSinIterMidBound
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := honestPoincarePoint
  refine ⟨100 * K * (C₁ + 1) + 1, by positivity, ?_⟩
  intro α h hα hα1 hsm ht0 ht1 hIntη i hi hIntγ
  let γ : ℝ := Work.Spaces.gam α
  let V : ℝ → ℝ := fun θ => h θ / Real.sin (2 * θ)
  let w : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-γ)
  let wη : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let Un : ℕ → ℝ → ℝ := fun m θ => Work.Elliptic.Dth1Iter m (deriv h) θ
  let Denη : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * wη θ
  let Dens : ℝ := ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi4 : i ≤ 4 := (Finset.mem_Icc.mp hi).2
  have hγdef : γ = Work.Spaces.gam α := rfl
  have hγpos : 0 < γ := by rw [hγdef, Work.Spaces.gam]; linarith
  have hγeta : Work.Spaces.eta ≤ γ := by
    rw [hγdef, Work.Spaces.gam, Work.Spaces.eta]; linarith
  have hγle : γ ≤ 1.1 := by rw [hγdef, Work.Spaces.gam]; linarith
  have h2γle : (2 : ℝ) ^ γ ≤ 4 := by
    have h1 : (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ (2 : ℝ) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
    have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    linarith [h1, h2]
  have h2γ1 : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγpos.le
  have h2γ_nn : (0 : ℝ) ≤ 2 ^ γ := le_trans zero_le_one h2γ1
  have hDenη_nn : 0 ≤ Denη :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))
  have hDens_nn : 0 ≤ Dens :=
    Finset.sum_nonneg (fun m _ =>
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _)))
  show (∫ θ in midA..midB, (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens)
  rw [intervalIntegral.integral_of_le midA_lt_midB.le]
  -- ## integrability on the middle interval
  have hIc : ∀ m ∈ Finset.range i,
      IntegrableOn (fun θ => (Un m θ) ^ 2 * w θ) (Set.Ioc midA midB) := by
    intro m _
    exact (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hIa : IntegrableOn (fun θ => (V θ) ^ 2 * w θ) (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_div_sin_two hsm).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hIb : IntegrableOn (fun θ => ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ)
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_finsetSum (Finset.range i) (fun m _ =>
        ((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
          (continuousOn_rpow_neg_sin_two γ)))).mono_set Set.Ioc_subset_Icc_self
  have hFint : IntegrableOn (fun θ => (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (((continuousOn_Dth1Iter_div hsm i).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ))).mono_set Set.Ioc_subset_Icc_self
  have hΨint : IntegrableOn
      (fun θ => K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ))
      (Set.Ioc midA midB) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_const.mul ((((continuousOn_div_sin_two hsm).pow 2).mul
        (continuousOn_rpow_neg_sin_two γ)).add
        (continuousOn_finsetSum (Finset.range i) (fun m _ =>
          ((continuousOn_Dth1Iter_deriv hsm m).pow 2).mul
            (continuousOn_rpow_neg_sin_two γ)))))).mono_set Set.Ioc_subset_Icc_self
  -- ## the pointwise iterate bound
  have hpt : ∀ θ ∈ Set.Ioc midA midB,
      (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ
        ≤ K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) := by
    intro θ hθ
    have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
    have hw : 0 ≤ w θ :=
      Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ (midSet_subset_Iθ hm)) _
    have h1 := hKb h hsm i hi θ hm
    calc (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ
        ≤ (K * ((V θ) ^ 2 + ∑ m ∈ Finset.range i, (Un m θ) ^ 2)) * w θ :=
          mul_le_mul_of_nonneg_right h1 hw
      _ = K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) := by
          rw [← Finset.sum_mul]; ring
  -- ## evaluation of `∫ Ψ`
  have hΨeq : (∫ θ in Set.Ioc midA midB,
        K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ))
      = K * ((∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
          + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_add hIa hIb, MeasureTheory.integral_finsetSum _ hIc]
  -- ## the `V`-term
  have hBV : (∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ) ≤ 16 * C₁ * Denη := by
    have hptV : ∀ θ ∈ Set.Ioc midA midB, (V θ) ^ 2 * w θ ≤ 16 * C₁ * Denη := by
      intro θ hθ
      have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
      have hhalf := half_le_sin_two_of_mem_mid hm
      have hC := hC₁b h hsm ht0 hIntη θ (midSet_subset_Ioo hm)
      have hw := rpow_neg_sin_two_le_mid hγpos.le hm
      have hV2 : (V θ) ^ 2 ≤ 4 * (h θ) ^ 2 := by
        have hs2 : (1 : ℝ) / 4 ≤ (Real.sin (2 * θ)) ^ 2 := by nlinarith [hhalf]
        rw [show V θ = h θ / Real.sin (2 * θ) from rfl, div_pow,
          div_le_iff₀ (by positivity : (0 : ℝ) < (Real.sin (2 * θ)) ^ 2)]
        nlinarith [hs2, sq_nonneg (h θ)]
      have h2 : (V θ) ^ 2 ≤ 4 * (C₁ * Denη) := by
        have := hV2; nlinarith [hC, hC₁pos.le, hDenη_nn]
      have h4 : (0 : ℝ) ≤ 4 * (C₁ * Denη) := by
        have := hC₁pos.le; nlinarith [hDenη_nn]
      calc (V θ) ^ 2 * w θ ≤ (4 * (C₁ * Denη)) * 2 ^ γ :=
            mul_le_mul h2 hw (Real.rpow_nonneg
              (Work.FTS.H2.sin_two_nonneg_Iθ (midSet_subset_Iθ hm)) _) h4
        _ ≤ (4 * (C₁ * Denη)) * 4 := mul_le_mul_of_nonneg_left h2γle h4
        _ = 16 * C₁ * Denη := by ring
    have hInt2 : IntegrableOn (fun _ : ℝ => 16 * C₁ * Denη) (Set.Ioc midA midB) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have haux := MeasureTheory.setIntegral_mono_on hIa hInt2 measurableSet_Ioc hptV
    rw [MeasureTheory.setIntegral_const, volume_real_Ioc_mid, smul_eq_mul] at haux
    refine haux.trans ?_
    have hnn : (0 : ℝ) ≤ 16 * C₁ * Denη := by have := hC₁pos.le; nlinarith [hDenη_nn]
    nlinarith [Real.pi_le_four, hnn]
  -- ## the `m = 0` term
  have hB0 : (∫ θ in Set.Ioc midA midB, (Un 0 θ) ^ 2 * w θ) ≤ 2 ^ γ * Denη := by
    have hpt0 : ∀ θ ∈ Set.Ioc midA midB,
        (Un 0 θ) ^ 2 * w θ ≤ 2 ^ γ * ((deriv h θ) ^ 2 * wη θ) := by
      intro θ hθ
      have hm : θ ∈ midSet := ⟨le_of_lt hθ.1, hθ.2⟩
      have hle := rpow_neg_sin_two_le_mid_eta hγeta hm
      calc (Un 0 θ) ^ 2 * w θ = (deriv h θ) ^ 2 * w θ := rfl
        _ ≤ (deriv h θ) ^ 2 * (2 ^ γ * wη θ) :=
            mul_le_mul_of_nonneg_left hle (sq_nonneg _)
        _ = 2 ^ γ * ((deriv h θ) ^ 2 * wη θ) := by ring
    have hInt3 : IntegrableOn (fun θ => 2 ^ γ * ((deriv h θ) ^ 2 * wη θ))
        (Set.Ioc midA midB) :=
      (ContinuousOn.integrableOn_compact isCompact_Icc
        (continuousOn_const.mul (((continuousOn_deriv_slice hsm).pow 2).mul
          (continuousOn_rpow_neg_sin_two (Work.Spaces.eta))))).mono_set Set.Ioc_subset_Icc_self
    have h0mem : (0 : ℕ) ∈ Finset.range i := Finset.mem_range.mpr hi1
    have haux := MeasureTheory.setIntegral_mono_on (hIc 0 h0mem) hInt3 measurableSet_Ioc hpt0
    refine haux.trans ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ h2γ_nn
    have hmono : (∫ θ in Set.Ioc midA midB, (deriv h θ) ^ 2 * wη θ)
        ≤ (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * wη θ) :=
      MeasureTheory.setIntegral_mono_set hIntη
        ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))))
        (Filter.Eventually.of_forall (fun θ (hθ : θ ∈ Set.Ioc midA midB) => midSet_subset_Iθ ⟨le_of_lt hθ.1, hθ.2⟩))
    exact hmono
  -- ## the `m ≥ 1` terms
  have hBm : ∀ m : ℕ, 1 ≤ m → m ≤ i →
      (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ := by
    intro m hm1 hmi
    have hmI : m ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨hm1, hmi⟩
    exact MeasureTheory.setIntegral_mono_set (hIntγ m hmI)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))))
      (Filter.Eventually.of_forall (fun θ (hθ : θ ∈ Set.Ioc midA midB) => midSet_subset_Iθ ⟨le_of_lt hθ.1, hθ.2⟩))
  -- ## the sum
  have hSum : (∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
      ≤ (i : ℝ) * (2 ^ γ * (Denη + Dens)) := by
    have hterm : ∀ m ∈ Finset.range i,
        (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) ≤ 2 ^ γ * (Denη + Dens) := by
      intro m hm
      have hlt : m < i := Finset.mem_range.mp hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        calc (∫ θ in Set.Ioc midA midB, (Un 0 θ) ^ 2 * w θ) ≤ 2 ^ γ * Denη := hB0
          _ ≤ 2 ^ γ * (Denη + Dens) := by
              apply mul_le_mul_of_nonneg_left _ h2γ_nn
              linarith [hDens_nn]
      · have hmIcc : m ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨hpos, le_of_lt hlt⟩
        have hsingle : (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ) ≤ Dens := by
          show (∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ) ≤
            ∑ a ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ, (Un a θ) ^ 2 * w θ)
          exact Finset.single_le_sum (fun a _ => MeasureTheory.setIntegral_nonneg
            measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _)
              (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _))) hmIcc
        have hb := hBm m hpos (le_of_lt hlt)
        have hS_nn : 0 ≤ Denη + Dens := by linarith
        have hfin : Dens ≤ 2 ^ γ * (Denη + Dens) := by
          have h1 := mul_le_mul_of_nonneg_right h2γ1 hS_nn
          nlinarith [h1, hDens_nn]
        calc (∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
            ≤ ∫ θ in Work.Spaces.Iθ, (Un m θ) ^ 2 * w θ := hb
          _ ≤ Dens := hsingle
          _ ≤ 2 ^ γ * (Denη + Dens) := hfin
    calc (∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ)
        ≤ ∑ m ∈ Finset.range i, (2 ^ γ * (Denη + Dens)) := Finset.sum_le_sum hterm
      _ = (Finset.range i).card • (2 ^ γ * (Denη + Dens)) := Finset.sum_const _
      _ = (i : ℝ) * (2 ^ γ * (Denη + Dens)) := by
          rw [Finset.card_range, nsmul_eq_mul]
  -- ## assembly
  calc (∫ θ in Set.Ioc midA midB, (Work.Elliptic.Dth1Iter i V θ) ^ 2 * w θ)
      ≤ ∫ θ in Set.Ioc midA midB,
          K * ((V θ) ^ 2 * w θ + ∑ m ∈ Finset.range i, (Un m θ) ^ 2 * w θ) :=
        MeasureTheory.setIntegral_mono_on hFint hΨint measurableSet_Ioc hpt
    _ = K * ((∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
          + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ) := hΨeq
    _ ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
        have hS_nn : (0 : ℝ) ≤ Denη + Dens := by linarith
        have hsum : (∫ θ in Set.Ioc midA midB, (V θ) ^ 2 * w θ)
              + ∑ m ∈ Finset.range i, ∫ θ in Set.Ioc midA midB, (Un m θ) ^ 2 * w θ
            ≤ 16 * C₁ * Denη + 16 * (Denη + Dens) := by
          have h1 : (i : ℝ) * (2 ^ γ * (Denη + Dens)) ≤ 16 * (Denη + Dens) := by
            have hi4R : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
            have h3 : 2 ^ γ * (Denη + Dens) ≤ 4 * (Denη + Dens) := by
              nlinarith [h2γle, hS_nn]
            have := mul_le_mul hi4R h3 (mul_nonneg h2γ_nn hS_nn) (by norm_num)
            nlinarith [this]
          linarith [hBV, hSum, h1]
        have hbig : K * (16 * C₁ * Denη + 16 * (Denη + Dens))
            ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
          have hC1n : (0 : ℝ) ≤ C₁ + 1 := by linarith [hC₁pos.le]
          have h16 : 16 * C₁ * Denη + 16 * (Denη + Dens) ≤ 16 * (C₁ + 1) * (Denη + Dens) := by
            nlinarith [hC₁pos.le, hDenη_nn, hDens_nn, hS_nn]
          have h100 : 16 * (C₁ + 1) * (Denη + Dens) ≤ 100 * (C₁ + 1) * (Denη + Dens) := by
            have h16le : (16 : ℝ) ≤ 100 := by norm_num
            have hprod : 0 ≤ (C₁ + 1) * (Denη + Dens) := mul_nonneg hC1n hS_nn
            nlinarith [h16le, hprod]
          calc K * (16 * C₁ * Denη + 16 * (Denη + Dens))
              ≤ K * (16 * (C₁ + 1) * (Denη + Dens)) := mul_le_mul_of_nonneg_left h16 hKpos.le
            _ ≤ K * (100 * (C₁ + 1) * (Denη + Dens)) := mul_le_mul_of_nonneg_left h100 hKpos.le
            _ ≤ (100 * K * (C₁ + 1) + 1) * (Denη + Dens) := by
                have h1 : K * (100 * (C₁ + 1) * (Denη + Dens))
                    = 100 * K * (C₁ + 1) * (Denη + Dens) := by ring
                rw [h1]
                nlinarith [hS_nn, hKpos.le, hC1n]
        exact (mul_le_mul_of_nonneg_left hsum hKpos.le).trans hbig

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.H2.STBounds2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `min θ (π/2 - θ) ≤ (π/4)·sin(2θ)` on `Iθ`. -/
theorem min_le_sin (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    min θ (π / 2 - θ) ≤ (π / 4) * Real.sin (2 * θ) := by
  have h := sin_two_ge_min θ hθ
  have h4 : ((π / 4) * (4 / π)) * min θ (π / 2 - θ) ≤ (π / 4) * Real.sin (2 * θ) := by
    calc ((π / 4) * (4 / π)) * min θ (π / 2 - θ)
        = (π / 4) * ((4 / π) * min θ (π / 2 - θ)) := by ring
      _ ≤ (π / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h (by positivity)
  have he : (π / 4) * (4 / π) = 1 := by field_simp
  rwa [he, one_mul] at h4


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bounds for the `dthU`-iterates of `deriv Γ`, and the pointwise lower bound on `|deriv Γ|`

The main content is the identity (on `(0,π/2)`)

  `D_θ^d (deriv Γ) = α · Gseq α d · Γ / sin 2θ`,

where `D_θ = sin 2θ ∂_θ` and `Gseq` is the sequence of `GamSeqDefs.lean`.  Since all the
`D_θ`-iterates of `Gseq α d` are bounded by constants (`Gseq_iter_bounded`), this gives the
first half of `Gam_deriv_bounds`; the second half is the two-sided lower bound obtained from
the explicit formula `deriv Γ = (α/3)(sin θ cos²θ)^{α/3-1} cos θ (cos²θ - 2 sin²θ)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-! ## Elementary differentiability facts -/

theorem deriv_sin_two (θ : ℝ) : deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [h2.deriv]
  ring




theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) := by
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
  linarith [hθ.2, Real.pi_pos]

/-! ## The identity `D_θ^d (Γ') = α · Gseq α d · Γ / sin 2θ` -/



/-! ## The assembly -/




end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_diff_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.DiffGreen

/-- **The sharp `L²` Green bound for a single source.**  For `0 < α ≤ 1/4`, `m : ℕ`, `z > 0` and
`d` with `∫_0^∞ d² < ∞`,

  `(m+1)·|radGreen α m d z| ≤ (2/α)·√(∫_0^∞ d²)·z^(-1/2)/√(m+1)`.

The case `m = 0` is the borderline one (`rgP α 0 = 0`): the `m`-uniform bound
`radGreen_abs_le_all` gives `|radGreen α 0 d z| ≤ 2·rgK α 0·√(∫ d²)·z^(-1/2) = (2/(5α))·…`, and
`2/(5α) ≤ 2/α`.  For `m ≥ 1` the sharper `radGreen_abs_le` gives
`√(∫ d²)·z^(-1/2)/(α(4m+5)√m)`, and `(m+1)/((4m+5)√m) ≤ 2/√(m+1)` because
`(m+1)√(m+1) ≤ 2(4m+5)√m` (square both sides: `(m+1)³ ≤ 4(4m+5)²m`, i.e.
`63m³ + 157m² + 97m - 1 ≥ 0` for `m ≥ 1`). -/
private theorem green_value_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {d : ℝ → ℝ}
    (hd2 : IntegrableOn (fun t : ℝ => d t ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m d z|
      ≤ (2 / α) * Real.sqrt (∫ t in Set.Ioi 0, d t ^ 2) * z ^ (-(1 / 2) : ℝ)
          / Real.sqrt ((m : ℝ) + 1) := by
  have hα1 : α ≤ 1 := by linarith
  set S : ℝ := Real.sqrt (∫ t in Set.Ioi 0, d t ^ 2) with hSdef
  set Z : ℝ := z ^ (-(1 / 2) : ℝ) with hZdef
  have hS : 0 ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := by
    rw [hZdef]; exact le_of_lt (Real.rpow_pos_of_pos hz _)
  have hSZ : 0 ≤ S * Z := mul_nonneg hS hZ
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    have hone : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
    rw [hone, Real.sqrt_one, div_one, one_mul]
    have hb := Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all (c := d) hα hα1 0 hd2 hz
    rw [← hSdef, ← hZdef] at hb
    have hK0 : Work.FTS.EllExist.rgK α 0 = 1 / (α * 5) := by
      rw [Work.FTS.EllExist.rgK]
      norm_num
    have hKle : 2 * Work.FTS.EllExist.rgK α 0 ≤ 2 / α := by
      rw [hK0, show 2 * (1 / (α * 5)) = 2 / (α * 5) by ring]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < α * 5) hα]
      linarith
    have hstep : 2 * Work.FTS.EllExist.rgK α 0 * S * Z ≤ (2 / α) * S * Z := by
      calc 2 * Work.FTS.EllExist.rgK α 0 * S * Z
          = (2 * Work.FTS.EllExist.rgK α 0) * (S * Z) := by ring
        _ ≤ (2 / α) * (S * Z) := mul_le_mul_of_nonneg_right hKle hSZ
        _ = (2 / α) * S * Z := by ring
    calc |Work.FTS.PhiStar.Radial.radGreen α 0 d z|
        ≤ 2 * Work.FTS.EllExist.rgK α 0 * S * Z := hb
      _ ≤ (2 / α) * S * Z := hstep
  · have hm1' : 1 ≤ m := hm1
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hb := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα hα1 m hm1' (c := d) hd2 hz
    rw [← hSdef, ← hZdef] at hb
    have hnum : ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)
        ≤ 2 * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) := by
      have hm1ℝ : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1'
      have hsq : ((m : ℝ) + 1) ^ 3 ≤ 4 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
        have h4 : (m : ℝ) + 1 ≤ 4 * (m : ℝ) := by linarith
        have hcube : ((m : ℝ) + 1) ^ 3 ≤ (4 * (m : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h4 3
        have hfin : (4 * (m : ℝ)) ^ 3 ≤ 4 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
          nlinarith [sq_nonneg (m : ℝ), sq_nonneg (4 * (m : ℝ) + 5), hmpos.le]
        linarith
      have e1 : ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)
          = Real.sqrt (((m : ℝ) + 1) ^ 3) := by
        rw [show ((m : ℝ) + 1) ^ 3 = ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) by ring,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ 2),
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
      have e2 : 2 * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)
          = Real.sqrt (4 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
        rw [show (4 : ℝ) * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)
              = (2 * (4 * (m : ℝ) + 5)) ^ 2 * (m : ℝ) by ring,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * (4 * (m : ℝ) + 5)) ^ 2),
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (4 * (m : ℝ) + 5))]
      rw [e1, e2]
      exact Real.sqrt_le_sqrt hsq
    have hden1 : 0 < α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) := by
      have h1 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hmpos
      positivity
    have hden2 : 0 < α * Real.sqrt ((m : ℝ) + 1) := by
      have h1 : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos_of_pos (by positivity)
      positivity
    have hcoef : ((m : ℝ) + 1) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))
        ≤ 2 / (α * Real.sqrt ((m : ℝ) + 1)) := by
      rw [div_le_div_iff₀ hden1 hden2]
      nlinarith [hnum, hα]
    calc ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m d z|
        ≤ ((m : ℝ) + 1) * (S * Z / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (S * Z) * (((m : ℝ) + 1) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) := by ring
      _ ≤ (S * Z) * (2 / (α * Real.sqrt ((m : ℝ) + 1))) := mul_le_mul_of_nonneg_left hcoef hSZ
      _ = (2 / α) * S * Z / Real.sqrt ((m : ℝ) + 1) := by ring

/-- **The sharp `L²` difference bound for the modal Green function.**  For `0 < α ≤ 1/4`,
`m : ℕ`, `z > 0` and two `L²((0,∞))` sources `c`, `c'` (a.e. strongly measurable),

  `(m+1)·|radGreen α m c' z - radGreen α m c z| ≤ (2/α)·√(∫_0^∞ (c'-c)²)·z^(-1/2)/√(m+1)`.

The `m = 0` case is the borderline one: `radGreen α 0` has `rgP α 0 = 0` and does not decay, so
`Work.EllipticEst.ModalSolution.radGreen_abs_le` (which needs `m ≥ 1`) does not apply there; use
`Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all` for it.

Recipe. (1) *Additivity*: for a.e.-strongly-measurable `L²` sources the two Green integrals are
honest (on `(0,z)` the integrand `t ↦ c t · t^(q-1)` is dominated by `(c t² + t^(2q-2))/2` with
`2q-2 > -1`, `q = (2m+5)/α ≥ 5`; on `(z,∞)` the integrand `t ↦ c t · t^(-p-1)` is dominated by
`(c t² + t^(-2p-2))/2` with `2p+2 > 1`, `p = 2m/α ≥ 0`), so `∫₀^z` and `∫_z^∞` are additive and
`radGreen α m c' z - radGreen α m c z = radGreen α m (fun t => c' t - c t) z`.
(2) `IntegrableOn (fun t => (c' t - c t)²) (Ioi 0)` from `(a-b)² ≤ 2a²+2b²`.
(3) Apply `radGreen_abs_le` at `c' - c` for `m ≥ 1` and `radGreen_abs_le_all` for `m = 0`, and
use the arithmetic `(m+1)/((4m+5)√m) ≤ 2/√(m+1)` (`m ≥ 1`): it is equivalent to
`(m+1)³ ≤ 4(4m+5)²m`. -/
theorem radGreen_diff_abs_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ)
    {c c' : ℝ → ℝ}
    (hc : MeasureTheory.AEStronglyMeasurable c
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc' : MeasureTheory.AEStronglyMeasurable c'
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0))
    (hc'2 : MeasureTheory.IntegrableOn (fun t : ℝ => c' t ^ 2) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m c' z
        - Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ (2 / α) * Real.sqrt (∫ t in Set.Ioi 0, (c' t - c t) ^ 2)
          * z ^ (-(1 / 2) : ℝ) / Real.sqrt ((m : ℝ) + 1) := by
  have hdae : AEStronglyMeasurable (fun t : ℝ => c' t - c t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hc'.sub hc
  have hd2 : IntegrableOn (fun t : ℝ => (c' t - c t) ^ 2) (Ioi 0) := by
    have hdom : IntegrableOn (fun t : ℝ => 2 * c' t ^ 2 + 2 * c t ^ 2) (Ioi 0) :=
      (hc'2.const_mul 2).add (hc2.const_mul 2)
    refine hdom.mono' (hdae.pow 2) ?_
    filter_upwards with t
    have hkey : (c' t - c t) ^ 2 ≤ 2 * c' t ^ 2 + 2 * c t ^ 2 := by
      nlinarith [sq_nonneg (c' t + c t)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (c' t - c t))]
    exact hkey
  rw [← Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_sub (c := c) (c' := c')
    hα hα4 m hc hc' hc2 hc'2 hz]
  exact green_value_le (d := fun t => c' t - c t) hα hα4 m hd2 hz

end Work.FTS.PhiStar.Honesty.DiffGreen
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgG1_sq_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-- **Far-field square bound for the singular Green branch.**

With `q = rgQ α m ≥ 28` and `rgG1 α m c z = z^{-q} * ∫_0^z c t * t^{q-1} dt`, the function
`z ↦ (rgG1 α m c z)²` is integrable on `(1,∞)`.

HINT (verified by two reviewers).  For `z > 1`, `∫ t in (0)..z, rgF1 α m c t = A₀ + ∫ t in 1..z, rgF1 α m c t`
with `A₀ = ∫ t in (0)..1, rgF1 α m c t` an honest finite constant:
`∫_0^1 |c t| t^{q-1} ≤ (∫_0^1 c²/t⁴)^{1/2} (1/(2q+3))^{1/2} < ∞` by Cauchy–Schwarz with weights
`|c t|/t²` and `t^{q+1}` (use `hnear`).  For this split use
`intervalIntegral.integral_add_adjacent_intervals` with `IntervalIntegrable rgF1 0 1` (from
`hnear`: `|c t| t^{q-1} ≤ (1/2)(c t)²/t⁴ + (1/2) t^{2q+2}` and `2q+2 > -1`) and
`IntervalIntegrable rgF1 1 z` (from `hfar`: `|c t| t^{q-1} ≤ (1/2)(c t)² + (1/2) t^{2q-2}`).
Then `rgG1 z = z^{-q}A₀ + z^{-q}∫ t in 1..z, rgF1 α m c t`, and:
* `∫_1^∞ (z^{-q}A₀)² dz = A₀²/(2q-1) < ∞` (`2q > 1`);
* Cauchy–Schwarz `(∫ t in 1..z, c t t^{q-1})² ≤ (∫ t in 1..z, (c t)² t^{q-1})(∫ t in 1..z, t^{q-1})`
  and `∫ t in 1..z, t^{q-1} = (z^q - 1)/q ≤ z^q/q` give
  `(z^{-q}∫ t in 1..z, c t t^{q-1})² ≤ z^{-q}/q * ∫ t in 1..z, (c t)² t^{q-1}`;
* Tonelli on the region `1 < t < z < ∞` (`Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one`)
  gives `∫_1^∞ z^{-q} ∫_1^z (c t)² t^{q-1} dt dz = ∫_1^∞ (c t)² t^{q-1} t^{1-q}/(q-1) dt
   = (1/(q-1)) ∫_1^∞ (c t)² dt < ∞` (use `integral_Ioi_rpow_of_lt` for `∫_t^∞ z^{-q} dz = t^{1-q}/(q-1)`).
Assemble with `(x+y)² ≤ 2x² + 2y²` and `IntegrableOn.union`/`IntegrableOn.congr_fun_ae`.
Measurability of `rgA` on `(1,∞)` (for `AEStronglyMeasurable`): `rgA` is continuous on any
`uIcc 0 y` with `y > 1` by `intervalIntegral.continuousOn_primitive_interval`
(`IntegrableOn rgF1 (uIcc 0 y)` from the two majorants above), so a reduction to each
`Ioc 1 (n+1)` via `Work.FTS.PhiStar.Honesty.integrableOn_Ioi_one_of_interval_bounds` is also
available. -/
theorem rgG1_sq_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.rgG1 α m c z) ^ 2) (Set.Ioi 1) := by
  have hbound := rgG1_lintegral_bound hα hα4 hm hc hnear hfar
  have hfin : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2))
      ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hmeas : AEStronglyMeasurable (fun z : ℝ => (Work.FTS.EllExist.rgG1 α m c z) ^ 2)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hcont1 : ContinuousOn (fun z : ℝ => Work.FTS.EllExist.rgG1 α m c z) (Set.Ioi (1 : ℝ)) :=
      (rgG1_cont_Ioi hα hα4 hm hc hnear hfar).mono
        (fun z hz => Set.mem_Ioi.mpr (lt_trans zero_lt_one (Set.mem_Ioi.mp hz)))
    exact (hcont1.pow 2).aestronglyMeasurable (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi
  have hfin' : HasFiniteIntegral (fun z : ℝ => (Work.FTS.EllExist.rgG1 α m c z) ^ 2)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    rw [hasFiniteIntegral_iff_norm]
    have this : (∫⁻ z, ENNReal.ofReal ‖(Work.FTS.EllExist.rgG1 α m c z) ^ 2‖
          ∂(volume.restrict (Set.Ioi (1 : ℝ))))
        = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [this]
    exact lt_top_iff_ne_top.mpr hfin
  exact ⟨hmeas, hfin'⟩

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sigmaCritWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

/-!
# Integrability of the critical angular weight `sin(2θ)^{-(1-α/10)}` with a `C/α` bound

We prove `sigmaCritWeight`: for `α ∈ (0,1]` the function `θ ↦ sin(2θ)^{-(1-α/10)}` is integrable
on `(0,π/2)` and its integral is at most `C/α` with a universal constant.

The exponent `c := -(1 - α/10) = α/10 - 1` satisfies `-1 < c ≤ 0`, i.e. it is the borderline
integrable case.  The proof is a two-sided Jordan comparison, valid for *every* `c ∈ (-1, 0]`:

* on `(0,π/4)`, `sin(2θ) ≥ (4/π) θ`, hence (the exponent being negative)
  `sin(2θ)^c ≤ (4/π)^c θ^c`; integrating `θ^c` over `(0,π/4)` with `integral_rpow` and using
  `(4/π)^c (π/4)^{c+1} = π/4` gives `∫_0^{π/4} sin(2θ)^c ≤ (π/4)/(1+c)`;
* the mirror `θ ↦ π/2 - θ` (under which `sin 2θ` is invariant) gives the same bound on
  `(π/4,π/2)`;
* adding the halves: `∫_{(0,π/2)} sin(2θ)^c ≤ (π/2)/(1+c)`.

With `c = α/10 - 1` this is `(π/2)/(α/10) = 5π/α ≤ 20/α`.
-/






/-- **Integrability.**  `θ ↦ sin(2θ)^c` is integrable on `(0,π/2)` for every `c > -1`. -/
theorem integrableOn_sin_two_rpow {c : ℝ} (hc : -1 < c) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) (Set.Ioo 0 (Real.pi / 2)) :=
  (Work.FTS.H2.intervalIntegrable_sin_rpow c hc).1.mono_set Set.Ioo_subset_Ioc_self


end Work.FTS.StrongPersist.N6Trans.SixRoute
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS_EllLimOK.BoxRegAux

/-! ## Small interval and product-metric helpers -/

/-- A `uIcc` (unordered interval) with endpoints in `[a,b]` stays inside `[a,b]`. -/
theorem uIcc_subset_Icc {a b x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    Set.uIcc x y ⊆ Set.Icc a b := by
  intro t ht
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans hx.1 h1, le_trans h2 hy.2⟩
  · exact ⟨le_trans hy.1 h1, le_trans h2 hx.2⟩

/-- A point of the unordered interval `[x,y]` is at distance at most `|y - x|` from the
endpoint `x`. -/
theorem abs_sub_left_le_abs_sub_of_mem_uIcc {x y t : ℝ} (ht : t ∈ Set.uIcc x y) :
    |t - x| ≤ |y - x| := by
  rcases le_total x y with h | h
  · rw [Set.uIcc_of_le h, Set.mem_Icc] at ht
    rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - x),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
    linarith [ht.2]
  · rw [Set.uIcc_of_ge h, Set.mem_Icc] at ht
    rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ 0),
      abs_of_nonpos (by linarith : y - x ≤ 0)]
    linarith [ht.1]

/-- The product metric on `ℝ × ℝ` is the max of the coordinate distances, written with
absolute values. -/
theorem dist_prod_eq_max' (p q : ℝ × ℝ) : dist p q = max |p.1 - q.1| |p.2 - q.2| := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]

/-- To bound `dist p q` it suffices to bound both coordinate differences by the same
constant. -/
theorem dist_prod_le_of (p q : ℝ × ℝ) {r : ℝ} (h1 : |p.1 - q.1| ≤ r) (h2 : |p.2 - q.2| ≤ r) :
    dist p q ≤ r := by
  rw [dist_prod_eq_max']
  exact max_le h1 h2

/-- **The staircase/FTC engine for the closed-box regularity of a pointwise limit.**
On the box `s = [a,b] × [c,d]` (a product of two intervals), let `H n` be a sequence of functions
whose two one-variable slices have within-derivatives `P n` (in the first variable, on `[a,b]`)
and `Q n` (in the second variable, on `[c,d]`) at every point of the box, with `H n`, `P n`, `Q n`
continuous on the box.  If `H n → H₀` pointwise on the box and `P n → P₀`, `Q n → Q₀` uniformly
on the box, with `P₀`, `Q₀` continuous on the box, then `Function.uncurry H₀` is differentiable
within the box at every point of the box, with derivative the linear map with slopes `P₀`, `Q₀`.

Intended proof: for each `n`, integrate the two slice derivatives along the staircase
`(z,θ) → (z',θ) → (z',θ')` (`Work.FTS_EllipticEst`-style `intervalIntegral` FTC:
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`), pass to the limit in the integrals
using the uniform convergence of `P n`, `Q n` on the box, and bound the remainder against
`ellCop (P₀ z θ) (Q₀ z θ)` by the *joint* continuity of `P₀`, `Q₀` on the box (the sup of
`|P₀ - P₀(z,θ)|` over the segment tends to `0`).  Please write the file in the namespace
`Work.FTS_EllLimOK` (as `BoxRegAux/Defs.lean` does) with `import Mathlib` and
`import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs`, and do NOT open `Filter` globally in a way
that shadows names. -/
theorem hasFDerivWithinAt_of_uniform_slice_partials
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {H : ℕ → ℝ → ℝ → ℝ} {H₀ : ℝ → ℝ → ℝ}
    {P : ℕ → ℝ → ℝ → ℝ} {P₀ : ℝ → ℝ → ℝ}
    {Q : ℕ → ℝ → ℝ → ℝ} {Q₀ : ℝ → ℝ → ℝ}
    (hcontH : ∀ n, ContinuousOn (Function.uncurry (H n)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hsz : ∀ n, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt (fun z' => H n z' θ) (P n z θ) (Set.Icc a b) z)
    (hth : ∀ n, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt (fun θ' => H n z θ') (Q n z θ) (Set.Icc c d) θ)
    (hcontP : ∀ n, ContinuousOn (Function.uncurry (P n)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hcontQ : ∀ n, ContinuousOn (Function.uncurry (Q n)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hH : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      Filter.Tendsto (fun n => H n z θ) Filter.atTop (nhds (H₀ z θ)))
    (hP : TendstoUniformlyOn (fun n p => P n p.1 p.2) (fun p => P₀ p.1 p.2) Filter.atTop
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hQ : TendstoUniformlyOn (fun n p => Q n p.1 p.2) (fun p => Q₀ p.1 p.2) Filter.atTop
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hcontP₀ : ContinuousOn (Function.uncurry P₀) (Set.Icc a b ×ˢ Set.Icc c d))
    (hcontQ₀ : ContinuousOn (Function.uncurry Q₀) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      HasFDerivWithinAt (Function.uncurry H₀) (Work.FTS_EllLimOK.ellCop (P₀ z θ) (Q₀ z θ))
        (Set.Icc a b ×ˢ Set.Icc c d) (z, θ) := by
  -- The proof is the staircase argument: control `H n y - H n y₀ - L (y - y₀)` by the two
  -- one-dimensional mean-value bounds on the slices, then pass to `n → ∞` using the pointwise
  -- convergence of `H n` at `y` and at `y₀`.
  -- (`hab`, `hcd` and the three continuity hypotheses `hcontH`, `hcontP`, `hcontQ` are part of the
  -- requested interface but are not needed by this argument: the slice bounds only use `hsz`,
  -- `hth` and the two uniform-convergence hypotheses.)
  intro z hz θ hθ
  rw [hasFDerivWithinAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro k hk
  -- Uniform continuity of the two limits on the compact box.
  have hPuc : UniformContinuousOn (fun p : ℝ × ℝ => P₀ p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcontP₀
  have hQuc : UniformContinuousOn (fun p : ℝ × ℝ => Q₀ p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcontQ₀
  obtain ⟨δP, hδPpos, hδP⟩ := Metric.uniformContinuousOn_iff.1 hPuc (k/4) (by linarith)
  obtain ⟨δQ, hδQpos, hδQ⟩ := Metric.uniformContinuousOn_iff.1 hQuc (k/4) (by linarith)
  have hy0 : (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc c d := ⟨hz, hθ⟩
  have hcloseP : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, dist p (z,θ) < min δP δQ →
      |P₀ p.1 p.2 - P₀ z θ| < k/4 := by
    intro p hp hpd
    have h := hδP p hp (z,θ) hy0 (lt_of_lt_of_le hpd (min_le_left _ _))
    rwa [Real.dist_eq] at h
  have hcloseQ : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, dist p (z,θ) < min δP δQ →
      |Q₀ p.1 p.2 - Q₀ z θ| < k/4 := by
    intro p hp hpd
    have h := hδQ p hp (z,θ) hy0 (lt_of_lt_of_le hpd (min_le_right _ _))
    rwa [Real.dist_eq] at h
  -- Uniform convergence of the two partials.
  have hPunif : ∀ᶠ n in Filter.atTop, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      dist (P₀ p.1 p.2) (P n p.1 p.2) < k/4 :=
    Metric.tendstoUniformlyOn_iff.1 hP (k/4) (by linarith)
  have hQunif : ∀ᶠ n in Filter.atTop, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      dist (Q₀ p.1 p.2) (Q n p.1 p.2) < k/4 :=
    Metric.tendstoUniformlyOn_iff.1 hQ (k/4) (by linarith)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨min δP δQ, lt_min hδPpos hδQpos, fun y hy hys => ?_⟩
  obtain ⟨z', θ'⟩ := y
  have hzs : z' ∈ Set.Icc a b := hys.1
  have hθs : θ' ∈ Set.Icc c d := hys.2
  have hz'm : |z' - z| ≤ dist (z',θ') (z,θ) := by
    rw [dist_prod_eq_max']; exact le_max_left _ _
  have hθ'm : |θ' - θ| ≤ dist (z',θ') (z,θ) := by
    rw [dist_prod_eq_max']; exact le_max_right _ _
  have hzero : |θ - θ| ≤ dist (z',θ') (z,θ) := by simp [dist_nonneg]
  -- The staircase bound for each `n` in the (eventual) good range.
  have hbd : ∀ᶠ n in Filter.atTop,
      ‖H n z' θ' - H n z θ - ((z' - z) * P₀ z θ + (θ' - θ) * Q₀ z θ)‖
        ≤ k * dist (z',θ') (z,θ) := by
    filter_upwards [hPunif, hQunif] with n hPn hQn
    -- first variable, angle fixed at `θ`
    have hs1 : |H n z' θ - H n z θ - (z' - z) * P₀ z θ| ≤ (k/2) * |z' - z| := by
      refine abs_sub_mul_le_of_derivWithin_bound (α := a) (β := b) (c := P₀ z θ) (C := k/2)
        (u := fun t => H n t θ) (u' := fun t => P n t θ) (x := z) (y := z')
        (fun t ht => hsz n t ht θ hθ) hz hzs (fun t ht => ?_)
      have htI : t ∈ Set.Icc a b := uIcc_subset_Icc hz hzs ht
      have htd : dist (t, θ) (z, θ) < min δP δQ :=
        lt_of_le_of_lt
          (dist_prod_le_of _ _ (le_trans (abs_sub_left_le_abs_sub_of_mem_uIcc ht) hz'm) hzero) hy
      have h1 : |P₀ t θ - P₀ z θ| < k/4 := hcloseP (t,θ) ⟨htI, hθ⟩ htd
      have h2 : |P n t θ - P₀ t θ| < k/4 := by
        have hh := hPn (t,θ) ⟨htI, hθ⟩
        simpa only [Real.dist_eq, abs_sub_comm] using hh
      have h3 : |P n t θ - P₀ z θ| ≤ |P n t θ - P₀ t θ| + |P₀ t θ - P₀ z θ| := by
        rw [show P n t θ - P₀ z θ = (P n t θ - P₀ t θ) + (P₀ t θ - P₀ z θ) from by ring]
        exact abs_add_le _ _
      linarith
    -- second variable, first coordinate fixed at `z'`
    have hs2 : |H n z' θ' - H n z' θ - (θ' - θ) * Q₀ z θ| ≤ (k/2) * |θ' - θ| := by
      refine abs_sub_mul_le_of_derivWithin_bound (α := c) (β := d) (c := Q₀ z θ) (C := k/2)
        (u := fun t => H n z' t) (u' := fun t => Q n z' t) (x := θ) (y := θ')
        (fun t ht => hth n z' hzs t ht) hθ hθs (fun t ht => ?_)
      have htI : t ∈ Set.Icc c d := uIcc_subset_Icc hθ hθs ht
      have htd : dist (z', t) (z, θ) < min δP δQ :=
        lt_of_le_of_lt
          (dist_prod_le_of _ _ hz'm (le_trans (abs_sub_left_le_abs_sub_of_mem_uIcc ht) hθ'm)) hy
      have h1 : |Q₀ z' t - Q₀ z θ| < k/4 := hcloseQ (z',t) ⟨hzs, htI⟩ htd
      have h2 : |Q n z' t - Q₀ z' t| < k/4 := by
        have hh := hQn (z',t) ⟨hzs, htI⟩
        simpa only [Real.dist_eq, abs_sub_comm] using hh
      have h3 : |Q n z' t - Q₀ z θ| ≤ |Q n z' t - Q₀ z' t| + |Q₀ z' t - Q₀ z θ| := by
        rw [show Q n z' t - Q₀ z θ = (Q n z' t - Q₀ z' t) + (Q₀ z' t - Q₀ z θ) from by ring]
        exact abs_add_le _ _
      linarith
    have hsplit : H n z' θ' - H n z θ - ((z' - z) * P₀ z θ + (θ' - θ) * Q₀ z θ)
        = (H n z' θ' - H n z' θ - (θ' - θ) * Q₀ z θ)
          + (H n z' θ - H n z θ - (z' - z) * P₀ z θ) := by ring
    rw [hsplit, Real.norm_eq_abs]
    refine le_trans (abs_add_le _ _) (le_trans (add_le_add hs2 hs1) ?_)
    nlinarith [hz'm, hθ'm, hk, abs_nonneg (z' - z), abs_nonneg (θ' - θ)]
  -- Pass to the limit in `n`, using pointwise convergence of `H n` at `y` and at `(z,θ)`.
  have hlim : Filter.Tendsto (fun n => H n z' θ' - H n z θ
      - ((z' - z) * P₀ z θ + (θ' - θ) * Q₀ z θ))
      Filter.atTop (nhds (H₀ z' θ' - H₀ z θ - ((z' - z) * P₀ z θ + (θ' - θ) * Q₀ z θ))) :=
    ((hH z' hzs θ' hθs).sub (hH z hz θ hθ)).sub tendsto_const_nhds
  have hfin := le_of_tendsto hlim.norm hbd
  simpa only [Function.uncurry, Function.uncurry_apply_pair, Real.norm_eq_abs, dist_eq_norm,
    ellCop_apply, Prod.fst_sub, Prod.snd_sub] using hfin

end Work.FTS_EllLimOK.BoxRegAux
end
end
-- ===== merged: Submission.Work.H2W.PsiSlices.weakPos2_dilate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices

set_option autoImplicit false


end Work.H2W.PsiSlices
end
