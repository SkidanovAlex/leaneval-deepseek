/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Φ` cannot be bounded above by a negative constant near `θ = 0`

Let `Φ f θ = f θ · f' θ · σ θ + (η/2) f θ² (2 cos 2θ) sin(2θ)^{-(1+η)}` (`σ = sin(2θ)^{-η}`) be
the primitive of the weighted `θ`-integration by parts (`Defs.lean`), and let
`β f θ = f θ² sin(2θ)^η`.  The key point is the exact identity

  `(β f)' = 2 sin(2θ)^{2η} · Φ f`       on `(0, π/2)`,

together with the assumption `f θ² sin(2θ)^{-(1+η)} → 0` at `0⁺`, which says `β → 0` at `0⁺`
(because `β = (f² sin(2θ)^{-(1+η)}) · sin(2θ)^{1+2η}` and the second factor is bounded).
Since `β ≥ 0`, if `Φ ≤ -δ < 0` on some interval `(0, t)` then

  `β ε ≥ β t + 2δ ∫_ε^t sin(2θ)^{2η} ≥ 2δ ∫_ε^t sin(2θ)^{2η}`,

and the right-hand side is bounded below by a *positive* constant (on `[t/2, 3t/4]` the
integrand `sin(2θ)^{2η}` is bounded below by `sin(t)^{2η} > 0`).  Letting `ε → 0⁺` contradicts
`β ε → 0`.

This is the boundary-term lemma of the open-class angular Agmon inequality
(`sliceAgmonOpenCore`): it forces `liminf_{θ→0⁺} Φ ≥ 0`, hence the vanishing of the lower
boundary term of the integration by parts `PhiIdentity`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonOpen

set_option autoImplicit false

/-- The pointwise derivative of `β f = f² sin(2θ)^η`:

  `(β f)' = 2 sin(2θ)^{2η} Φ f`     on `(0, π/2)`. -/
theorem beta_hasDerivAt {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (beta f) (2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta) * Phi f θ) θ := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hcd : ContDiffAt ℝ 2 f θ := hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hdf : HasDerivAt f (deriv f θ) θ := (hcd.differentiableAt two_ne_zero).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsinD : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h := hlin.sin
    refine h.congr_deriv ?_
    ring
  have hpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (Work.Spaces.eta))
      (2 * Real.cos (2 * θ) * Work.Spaces.eta
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1)) θ :=
    hsinD.rpow_const (Or.inl hs.ne')
  have hsq : HasDerivAt (fun t : ℝ => (f t) ^ 2) (2 * f θ * deriv f θ) θ := by
    have h := hdf.pow 2
    refine h.congr_deriv ?_
    ring
  have hprod := hsq.mul hpow
  have key : 2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta) * Phi f θ
      = 2 * f θ * deriv f θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
        + (f θ) ^ 2 * (2 * Real.cos (2 * θ) * Work.Spaces.eta
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1)) := by
    have r1 : (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    have r2 : (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    simp only [Phi, Work.FTS.EllipticEst.thEta]
    rw [show (2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)) *
        (f θ * deriv f θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) +
          Work.Spaces.eta / 2 * (f θ) ^ 2 * (2 * Real.cos (2 * θ)) *
            (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        = (2 * (f θ * deriv f θ)) * ((Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + ((f θ) ^ 2 * (Work.Spaces.eta * (2 * Real.cos (2 * θ))))
            * ((Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) from by ring]
    rw [r1, r2]
    ring
  exact hprod.congr_deriv key.symm

/-- `β f` is continuous on the open interval `(0, π/2)`. -/
theorem continuousOn_beta {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (beta f) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcontf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf.continuousOn
  have hcontsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontp : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
  unfold beta
  exact (hcontf.pow 2).mul hcontp

/-- `Φ f` is continuous on the open interval `(0, π/2)`. -/
theorem continuousOn_Phi {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Phi f) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcontf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf.continuousOn
  have hcontdf : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontth : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [Work.FTS.EllipticEst.thEta] using
      hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
  have hconts2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
  have h1 : ContinuousOn
      (fun θ : ℝ => f θ * deriv f θ * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := (hcontf.mul hcontdf).mul hcontth
  have h2 : ContinuousOn
      (fun θ : ℝ => (Work.Spaces.eta / 2) * (f θ) ^ 2 * (2 * Real.cos (2 * θ))
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((continuousOn_const.mul (hcontf.pow 2)).mul (continuousOn_const.mul hcontcos)).mul hconts2
  unfold Phi
  exact h1.add h2

/-- `β f` is non-negative on `(0, π/2)`. -/
theorem beta_nonneg {f : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ beta f θ :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)

/-- The rate hypothesis at `0⁺` implies `β f → 0` there. -/
theorem beta_tendsto_zero {f : ℝ → ℝ}
    (hrate0 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (beta f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hpi4 : (0:ℝ) < Real.pi / 4 := by positivity
  have hr : Filter.Tendsto (fun θ => (rho f θ) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hrate0
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact (rho_sq f hθ).symm
  refine squeeze_zero' ?_ ?_ hr
  · filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact beta_nonneg hθ
  · filter_upwards [Ioo_mem_nhdsGT hpi4] with θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    rw [beta_eq f hθ']
    calc (rho f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 + 2 * Work.Spaces.eta)
        ≤ (rho f θ) ^ 2 * 1 := by
          gcongr
          exact Real.rpow_le_one (le_of_lt (sin_two_pos hθ')) (Real.sin_le_one (2 * θ))
            (by linarith [Work.Spaces.eta_pos])
      _ = (rho f θ) ^ 2 := mul_one _

/-- The quantitative lower bound for the integral of `sin(2θ)^{2η}` used in the proof:
for `0 < t ≤ π/8` and `0 < ε < t/2`,

  `(t/4) sin(t)^{2η} ≤ ∫_ε^t sin(2θ)^{2η} dθ`,

the left-hand side being a *positive* constant independent of `ε`. -/
theorem integral_sin_two_rpow_lower {t ε : ℝ} (ht : 0 < t) (ht8 : t ≤ Real.pi / 8)
    (hε : ε ∈ Set.Ioo 0 (t / 2)) :
    (t / 4) * (Real.sin t) ^ (2 * Work.Spaces.eta)
      ≤ ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by
  have hpi := Real.pi_pos
  have hη : 0 ≤ 2 * Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have ht2 : 0 < t / 2 := by linarith
  have ht3 : t / 2 ≤ 3 * t / 4 := by linarith
  have h3t : 3 * t / 4 ≤ t := by linarith
  have hcont : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta))
      (Set.uIcc (t / 2) (3 * t / 4)) := by
    apply ContinuousOn.rpow_const
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le ht3, Set.mem_Icc] at hx
      exact Or.inl (ne_of_gt (sin_two_pos
        ⟨by linarith [hx.1, ht2], by linarith [hx.2, h3t, ht8, hpi]⟩))
  have hint1 : IntervalIntegrable (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta))
      volume (t / 2) (3 * t / 4) := hcont.intervalIntegrable
  have hstep1 : (Real.sin t) ^ (2 * Work.Spaces.eta) * (3 * t / 4 - t / 2)
      ≤ ∫ x in t / 2..3 * t / 4, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by
    have h := intervalIntegral.integral_mono_on ht3
      (intervalIntegrable_const (c := (Real.sin t) ^ (2 * Work.Spaces.eta))) hint1
      (fun x hx => ?_)
    · simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
    · rw [Set.mem_Icc] at hx
      exact Real.rpow_le_rpow
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht]) (by linarith [ht8, hpi]))
        (Real.monotoneOn_sin ⟨by linarith, by linarith [ht8, hpi]⟩
          ⟨by linarith [hx.1, ht2], by linarith [hx.2, ht3, ht8, hpi]⟩ (by linarith [hx.1])) hη
  have hint2 : IntervalIntegrable (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta))
      volume ε t := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le (le_of_lt (lt_trans hε.2 (by linarith : t / 2 < t))), Set.mem_Icc] at hx
      exact Or.inl (ne_of_gt (sin_two_pos
        ⟨by linarith [hx.1, hε.1], by linarith [hx.2, ht8, hpi]⟩))
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc ε t)]
      (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta)) := by
    change ∀ᵐ x ∂(volume.restrict (Set.Ioc ε t)),
      (0:ℝ) ≤ (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact MeasureTheory.ae_of_all _ (fun x hx => Real.rpow_nonneg (le_of_lt
      (sin_two_pos ⟨by linarith [hx.1, hε.1], by linarith [hx.2, ht8, hpi]⟩)) _)
  have hstep2 := intervalIntegral.integral_mono_interval hε.2.le ht3 h3t hnn hint2
  calc (t / 4) * (Real.sin t) ^ (2 * Work.Spaces.eta)
      = (Real.sin t) ^ (2 * Work.Spaces.eta) * (3 * t / 4 - t / 2) := by ring
    _ ≤ ∫ x in t / 2..3 * t / 4, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := hstep1
    _ ≤ ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := hstep2

theorem PhiGeNearZero {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hrate0 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ a δ : ℝ, 0 < a → 0 < δ → ∃ θ ∈ Set.Ioo 0 a, -(δ) ≤ Phi f θ := by
  intro a δ ha hδ
  by_contra hcon
  push_neg at hcon
  have hpi := Real.pi_pos
  set t : ℝ := min a (Real.pi / 8) / 2 with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def]
    have : 0 < min a (Real.pi / 8) := lt_min ha (by linarith)
    linarith
  have ht_lt_a : t < a := by
    rw [ht_def]
    have : min a (Real.pi / 8) ≤ a := min_le_left _ _
    linarith
  have ht_le8 : t ≤ Real.pi / 8 := by
    rw [ht_def]
    have : min a (Real.pi / 8) ≤ Real.pi / 8 := min_le_right _ _
    linarith
  have ht_lt_pi2 : t < Real.pi / 2 := by linarith
  have ht2pos : 0 < t / 2 := by linarith
  set c : ℝ := (t / 4) * (Real.sin t) ^ (2 * Work.Spaces.eta) with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact mul_pos (by linarith)
      (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht_pos (by linarith)) _)
  have hc0_pos : 0 < 2 * δ * c := mul_pos (by linarith) hc_pos
  have hbeta_tend := beta_tendsto_zero (f := f) hrate0
  have hbeta_t_ge : 0 ≤ beta f t := beta_nonneg ⟨ht_pos, ht_lt_pi2⟩
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 2 * δ * c ≤ beta f ε := by
    filter_upwards [Ioo_mem_nhdsGT ht2pos] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hεt : ε ≤ t := le_of_lt (by linarith [hε.2])
    -- the derivative of `β` is the integrand of the fundamental theorem
    have hderiv : ∀ x ∈ Set.uIcc ε t,
        HasDerivAt (beta f) (2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x) x := by
      intro x hx
      rw [Set.uIcc_of_le hεt, Set.mem_Icc] at hx
      exact beta_hasDerivAt hf
        ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_pi2]⟩
    have hscont : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta))
        (Set.uIcc ε t) := by
      apply ContinuousOn.rpow_const
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      · intro x hx
        rw [Set.uIcc_of_le hεt, Set.mem_Icc] at hx
        exact Or.inl (ne_of_gt (sin_two_pos
          ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_pi2]⟩))
    have hint1 : IntervalIntegrable
        (fun x : ℝ => 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x)
        volume ε t := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.mul (hscont.const_mul 2) ?_
      exact (continuousOn_Phi hf).mono (fun x hx => by
        rw [Set.uIcc_of_le hεt, Set.mem_Icc] at hx
        exact ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_pi2]⟩)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint1
    have hmono : ∫ x in ε..t, 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x
        ≤ ∫ x in ε..t, (-2 * δ) * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by
      apply intervalIntegral.integral_mono_on hεt hint1
      · apply ContinuousOn.intervalIntegrable
        exact (hscont.const_mul (-2 * δ))
      · intro x hx
        rw [Set.mem_Icc] at hx
        have hxmem : x ∈ Set.Ioo 0 a :=
          ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_a]⟩
        have hΦ : Phi f x < -δ := hcon x hxmem
        have hxI : x ∈ Set.Ioo 0 (Real.pi / 2) :=
          ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_pi2]⟩
        have hp : 0 ≤ 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt (sin_two_pos hxI)) _)
        calc 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x
            ≤ 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * (-δ) :=
              mul_le_mul_of_nonneg_left (le_of_lt hΦ) hp
          _ = (-2 * δ) * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by ring
    have hIntEq : ∫ x in ε..t, (-2 * δ) * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta)
        = (-2 * δ) * ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) :=
      intervalIntegral.integral_const_mul _ _
    have hLow : c ≤ ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by
      rw [hc_def]
      exact integral_sin_two_rpow_lower ht_pos ht_le8 hε
    have hfin : ∫ x in ε..t, 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x
        ≤ (-2 * δ) * c := by
      calc ∫ x in ε..t, 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x
          ≤ ∫ x in ε..t, (-2 * δ) * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := hmono
        _ = (-2 * δ) * ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := hIntEq
        _ ≤ (-2 * δ) * c := mul_le_mul_of_nonpos_left hLow (by linarith)
    -- `β ε = β t - ∫ ≥ 2 δ c`
    have hbε : beta f ε
        = beta f t - ∫ x in ε..t, 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x := by
      linarith [hFTC]
    show 2 * δ * c ≤ beta f ε
    linarith [hbε, hfin, hbeta_t_ge]
  have hle := ge_of_tendsto hbeta_tend hev
  linarith [hc0_pos, hle]

end Work.EllipticEst.Core.i0Aux.SliceAgmonOpen
