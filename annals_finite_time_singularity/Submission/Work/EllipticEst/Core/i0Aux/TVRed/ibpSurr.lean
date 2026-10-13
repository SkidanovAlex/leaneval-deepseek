import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.EllipticEst.Core.thEtaFacts

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
