import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_sq_integrable
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_weight_integrable
import Submission.Work.BoseBoxFock.SqrtKin.subordination_rpow_integrableOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.subordination_t_p_swap`

The continuum subordination identity for the heat-kernel representation of `√(−Δ)` on `ℝ³`:

`∫_0^∞ t^{-3/2}·(kinMass g − kinHeat g t) dt = 2√π · kinFirst g`

for `g` smooth with compact support.

Writing `f = kinFT g` and `h p = ‖f p‖²`, the integrand factorises a.e. as

`t^{-3/2}·(kinMass g − kinHeat g t) = (2π)^{-3} ∫_p t^{-3/2}(1 − e^{−t‖p‖²}) h p`,

and the per-mode identity `subordination_rpow_id`

`∫_0^∞ t^{-3/2}(1 − e^{−a t}) dt = 2√π √a`  (`a ≥ 0`)

together with Tonelli (the integrand is nonnegative on `t > 0`) gives the claim:
the `t`-integral and the `p`-integral may be interchanged, and the inner integral is
`2√π ‖p‖ h p`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators

namespace Work.BoseBoxFock.SqrtKin

set_option maxHeartbeats 1000000

/-! ## The per-mode subordination identity -/

/-- **Per-mode subordination.** For `a ≥ 0`,
`∫_0^∞ t ^ (-3/2) * (1 - exp (-(t * a))) dt = 2√π √a`.

Proof: for `a > 0` integrate by parts on `(0, ∞)` with `u t = 1 - e^{-a t}`,
`v t = -2 t^{-1/2}` (so `v' t = t^{-3/2}`), using the integrability of both
`(1-e^{-at})t^{-3/2}` (imported) and `a e^{-at} · (-2t^{-1/2})`; then evaluate
`∫_0^∞ t^{-1/2}e^{-at}dt = (1/a)^{1/2}Γ(1/2)` with the Gamma-function integral.
For `a = 0` both sides vanish. -/
theorem subordination_rpow_id (a : ℝ) (ha : 0 ≤ a) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * a)))
      = 2 * Real.sqrt Real.pi * Real.sqrt a := by
  have hgoal : (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * a))))
      = ∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [mul_comm t a]
    ring
  rw [hgoal]
  rcases lt_or_eq_of_le ha with hapos | hzero
  · have hder_u : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun t : ℝ => 1 - Real.exp (-(a * t))) (a * Real.exp (-(a * x))) x := by
      intro x _
      have h := (hasDerivAt_const_mul (x := x) a).neg.exp
      have h2 : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(a * t)))
          (-(Real.exp (-(a * x)) * -a)) x := h.const_sub 1
      have hval : -(Real.exp (-(a * x)) * -a) = a * Real.exp (-(a * x)) := by ring
      rw [hval] at h2
      exact h2
    have hder_v : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun t : ℝ => -2 * t ^ (-(1 : ℝ) / 2)) (x ^ (-(3 : ℝ) / 2)) x := by
      intro x hx
      have h := (Real.hasDerivAt_rpow_const (x := x) (p := -(1 : ℝ) / 2)
        (Or.inl (ne_of_gt hx))).const_mul (-2)
      have hval : (-2 : ℝ) * ((-(1 : ℝ) / 2) * x ^ ((-(1 : ℝ) / 2) - 1))
          = x ^ (-(3 : ℝ) / 2) := by
        rw [show (-(1 : ℝ) / 2) - 1 = -(3 : ℝ) / 2 by norm_num]
        ring
      rw [hval] at h
      exact h
    have h3 : IntegrableOn (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2))
        (Set.Ioi 0) := subordination_rpow_integrableOn a ha
    have h4 : IntegrableOn (fun t : ℝ => (a * Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2)))
        (Set.Ioi 0) := by
      have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 : ℝ) / 2) (b := a)
        (by norm_num) one_pos hapos
      have hb2 : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * Real.exp (-(a * t)))
          (Set.Ioi 0) := by
        refine Integrable.congr hb (Filter.Eventually.of_forall (fun t => ?_))
        dsimp only
        rw [Real.rpow_one, neg_mul]
      refine Integrable.congr (Integrable.const_mul hb2 (-2 * a))
        (Filter.Eventually.of_forall (fun t => ?_))
      ring
    have hlim0 : Tendsto (fun t : ℝ => (1 - Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hsq : Tendsto (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(1 : ℝ) / 2))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        refine squeeze_zero' (g := fun t : ℝ => a * Real.sqrt t) ?_ ?_ ?_
        · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
          have ht0 : 0 < t := ht.1
          have h1 : 0 ≤ 1 - Real.exp (-(a * t)) := by
            have h : Real.exp (-(a * t)) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by nlinarith [ha, ht0.le])
            simpa using h
          exact mul_nonneg h1 (Real.rpow_nonneg ht0.le _)
        · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
          have ht0 : 0 < t := ht.1
          have h2 : 1 - Real.exp (-(a * t)) ≤ a * t := by
            have h := Real.one_sub_le_exp_neg (a * t)
            linarith
          have h3 : 0 ≤ t ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
          calc (1 - Real.exp (-(a * t))) * t ^ (-(1 : ℝ) / 2)
              ≤ (a * t) * t ^ (-(1 : ℝ) / 2) := mul_le_mul_of_nonneg_right h2 h3
            _ = a * Real.sqrt t := by
                rw [show (a * t) * t ^ (-(1 : ℝ) / 2)
                      = a * (t ^ (1 : ℝ) * t ^ (-(1 : ℝ) / 2)) by
                      rw [Real.rpow_one]; ring,
                  ← Real.rpow_add ht0,
                  show (1 : ℝ) + (-(1 : ℝ) / 2) = (1 : ℝ) / 2 by norm_num,
                  Real.sqrt_eq_rpow]
        · have hsqrt : Tendsto (fun t : ℝ => Real.sqrt t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            have h := Real.continuous_sqrt.continuousAt (x := (0 : ℝ))
            simpa using h.mono_left nhdsWithin_le_nhds
          simpa using hsqrt.const_mul a
      have hneg : Tendsto (fun t : ℝ => -2 * ((1 - Real.exp (-(a * t))) * t ^ (-(1 : ℝ) / 2)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hsq.const_mul (-2)
      refine Tendsto.congr'
        (Filter.Eventually.of_forall (fun t => by ring)) hneg
    have hlimtop : Tendsto (fun t : ℝ => (1 - Real.exp (-(a * t))) * (-2 * t ^ (-(1 : ℝ) / 2)))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) atTop (nhds 0) := by
        have hbase : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
        refine Tendsto.congr' ?_ hbase
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by norm_num,
          Real.rpow_neg ht]
      have h2 : Tendsto (fun t : ℝ => 1 - Real.exp (-(a * t))) atTop (nhds 1) := by
        have hexp : Tendsto (fun t : ℝ => Real.exp (-(a * t))) atTop (nhds 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hapos)
        have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
        have h := hconst.sub hexp
        simpa using h
      have h := h2.mul (h1.const_mul (-2))
      simpa using h
    have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
      hder_u hder_v h3 h4 hlim0 hlimtop
    rw [key]
    have hIval : (∫ x in Set.Ioi (0 : ℝ),
          (a * Real.exp (-(a * x))) * (-2 * x ^ (-(1 : ℝ) / 2)))
        = (-2 * a) * ((Real.sqrt a)⁻¹ * Real.sqrt Real.pi) := by
      have hcongr : (∫ x in Set.Ioi (0 : ℝ),
            (a * Real.exp (-(a * x))) * (-2 * x ^ (-(1 : ℝ) / 2)))
          = ∫ x in Set.Ioi (0 : ℝ),
              (-2 * a) * (x ^ ((1 : ℝ) / 2 - 1) * Real.exp (-(a * x))) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
        rw [show -(1 : ℝ) / 2 = (1 : ℝ) / 2 - 1 by norm_num]
        ring
      rw [hcongr, integral_const_mul,
        Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 : ℝ) / 2) (r := a) (by norm_num) hapos,
        Real.Gamma_one_half_eq, one_div, Real.inv_rpow ha, ← Real.sqrt_eq_rpow]
    rw [hIval]
    have hkey : a * (Real.sqrt a)⁻¹ = Real.sqrt a := by
      rw [inv_eq_one_div, mul_one_div, div_eq_iff (Real.sqrt_pos_of_pos hapos).ne',
        Real.mul_self_sqrt (le_of_lt hapos)]
    calc 0 - 0 - (-2 * a) * ((Real.sqrt a)⁻¹ * Real.sqrt Real.pi)
        = 2 * Real.sqrt Real.pi * (a * (Real.sqrt a)⁻¹) := by ring
      _ = 2 * Real.sqrt Real.pi * Real.sqrt a := by rw [hkey]
  · subst hzero
    simp

/-! ## The pointwise mass/heat difference -/

/-- `kinMass g - kinHeat g t` is the `p`-integral of `(1 - e^{-t‖p‖²})‖kinFT g p‖²`
against the prefactor `(2π)^{-3}`, for `t > 0`. -/
theorem kinMass_sub_kinHeat {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    kinMass g - kinHeat g t
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3),
            (1 - Real.exp (-(t * ‖p‖ ^ 2))) * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
  have hA : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Submission.BoseGases.kinFT g p‖ ^ 2) := kinFT_sq_integrable hg hgc
  have hB : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    have hexp : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Real.exp (-(t * ‖p‖ ^ 2))) volume :=
      (((Real.continuous_exp.comp
        ((continuous_const.mul (continuous_norm.pow 2)).neg)).measurable).aemeasurable).aestronglyMeasurable
    refine Integrable.mono' hA (hexp.mul hA.aestronglyMeasurable) ?_
    filter_upwards with p
    have hle : Real.exp (-(t * ‖p‖ ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [ht, sq_nonneg ‖p‖]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) hle
  unfold kinMass kinHeat
  rw [← mul_sub, ← integral_sub hA hB]
  have hcongr : (∫ p : EuclideanSpace ℝ (Fin 3),
        (‖Submission.BoseGases.kinFT g p‖ ^ 2 -
          Real.exp (-(t * ‖p‖ ^ 2)) * ‖Submission.BoseGases.kinFT g p‖ ^ 2))
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          (1 - Real.exp (-(t * ‖p‖ ^ 2))) * ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))
  rw [hcongr]

/-! ## Tonelli for the `t`–`p` double integral -/

/-- **Tonelli/Fubini** for a nonnegative measurable integrand on
`(0, ∞) × ℝ³`, with prescribed inner (`t`-)integrals `w p`. -/
theorem integral_Ioi_integral_swap_of_nonneg
    {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : AEMeasurable (Function.uncurry G)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ G t p)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hint : ∀ p : EuclideanSpace ℝ (Fin 3), IntegrableOn (fun t : ℝ => G t p) (Set.Ioi 0))
    (hw0 : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ w p)
    (hw : Integrable w)
    (hinner : ∀ p : EuclideanSpace ℝ (Fin 3),
      ∫ t in Set.Ioi (0 : ℝ), G t p = w p) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ p, G t p)
      = ∫ p, ∫ t in Set.Ioi (0 : ℝ), G t p := by
  have hslice : ∀ p : EuclideanSpace ℝ (Fin 3),
      (∫⁻ t, ENNReal.ofReal (G t p) ∂(volume.restrict (Set.Ioi (0 : ℝ))))
        = ENNReal.ofReal (w p) := by
    intro p
    have h1 := ofReal_integral_eq_lintegral_ofReal (hint p) (hnn.mono (fun t ht => ht p))
    rw [hinner p] at h1
    exact h1.symm
  have hae : ∀ᵐ z ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume), 0 ≤ G z.1 z.2 := by
    rw [ae_iff]
    have hzero : (volume.restrict (Set.Ioi (0 : ℝ)))
        {t : ℝ | ¬ (∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ G t p)} = 0 := ae_iff.mp hnn
    refine measure_mono_null
      (t := {t : ℝ | ¬ (∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ G t p)} ×ˢ Set.univ)
      (fun z hz => ⟨fun h => hz (h z.2), Set.mem_univ _⟩) ?_
    · rw [Measure.prod_prod, hzero]
      simp
  have hG' : AEMeasurable (Function.uncurry fun t p => ENNReal.ofReal (G t p))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := hG.ennreal_ofReal
  have hfin : (∫⁻ z, ENNReal.ofReal (Function.uncurry G z)
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) < ⊤ := by
    have hjeq : (∫⁻ z, ENNReal.ofReal (Function.uncurry G z)
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
        = (∫⁻ z, ENNReal.ofReal (G z.1 z.2)
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := rfl
    rw [hjeq, ← lintegral_lintegral hG', lintegral_lintegral_swap hG']
    rw [lintegral_congr (fun p => hslice p)]
    rw [← ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hw0)]
    exact ENNReal.ofReal_lt_top
  have hInt : Integrable (Function.uncurry G)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    ⟨hG.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hae).mpr hfin⟩
  exact integral_integral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := volume) hInt

/-! ## The main identity -/

set_option maxHeartbeats 2000000

theorem subordination_t_p_swap {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * (kinMass g - kinHeat g t))
      = 2 * Real.sqrt Real.pi * kinFirst g := by
  have hA : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Submission.BoseGases.kinFT g p‖ ^ 2) := kinFT_sq_integrable hg hgc
  have hW : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := kinFT_weight_integrable hg hgc
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      t ^ (-(3 : ℝ) / 2) * (kinMass g - kinHeat g t)
        = ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : EuclideanSpace ℝ (Fin 3),
              (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
                ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
    intro t ht
    have h1 : t ^ (-(3 : ℝ) / 2) * (kinMass g - kinHeat g t)
        = ((2 * Real.pi) ^ 3)⁻¹ *
            (t ^ (-(3 : ℝ) / 2) *
              ∫ p : EuclideanSpace ℝ (Fin 3),
                (1 - Real.exp (-(t * ‖p‖ ^ 2))) * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
      rw [kinMass_sub_kinHeat hg hgc ht]
      ring
    rw [h1]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    ring
  have hG : AEMeasurable
      (Function.uncurry fun (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) =>
        (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
          ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    have hF : AEMeasurable (fun t : ℝ => t ^ (-(3 : ℝ) / 2))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hcont : ContinuousOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Set.Ioi (0 : ℝ)) :=
        fun x hx =>
          (Real.continuousAt_rpow_const x (-(3 : ℝ) / 2) (Or.inl (ne_of_gt hx))).continuousWithinAt
      exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
    have h1 : AEMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) => z.1 ^ (-(3 : ℝ) / 2))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := hF.comp_fst
    have h2 : AEMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
        1 - Real.exp (-(z.1 * ‖z.2‖ ^ 2)))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
      have hfst : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) => z.1) := measurable_fst
      have hsnd : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) => ‖z.2‖ ^ 2) :=
        (continuous_snd.norm.pow 2).measurable
      exact (measurable_const.sub
        (Real.continuous_exp.measurable.comp ((hfst.mul hsnd).neg))).aemeasurable
    have h3 : AEMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
        ‖Submission.BoseGases.kinFT g z.2‖ ^ 2)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
      (hA.aestronglyMeasurable.aemeasurable).comp_snd
    exact (h1.mul h2).mul h3
  have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ p : EuclideanSpace ℝ (Fin 3),
        0 ≤ (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
          ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    intro p
    refine mul_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) ?_) (sq_nonneg _)
    have h : Real.exp (-(t * ‖p‖ ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [ht0.le, sq_nonneg ‖p‖]
    linarith
  have hint : ∀ p : EuclideanSpace ℝ (Fin 3),
      IntegrableOn (fun t : ℝ => (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2) (Set.Ioi 0) := by
    intro p
    have hb := subordination_rpow_integrableOn (‖p‖ ^ 2) (sq_nonneg ‖p‖)
    have hb' : IntegrableOn (fun t : ℝ =>
        t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) (Set.Ioi 0) := by
      refine Integrable.congr hb (Filter.Eventually.of_forall (fun t => ?_))
      dsimp only
      rw [mul_comm (‖p‖ ^ 2) t]
      ring
    exact Integrable.mul_const hb' (‖Submission.BoseGases.kinFT g p‖ ^ 2)
  have hinner : ∀ p : EuclideanSpace ℝ (Fin 3),
      (∫ t in Set.Ioi (0 : ℝ), (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
          ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        = 2 * Real.sqrt Real.pi * (‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    intro p
    have hsub := subordination_rpow_id (‖p‖ ^ 2) (sq_nonneg ‖p‖)
    rw [integral_mul_const, hsub, Real.sqrt_sq (norm_nonneg p)]
    ring
  have hw0 : ∀ p : EuclideanSpace ℝ (Fin 3),
      0 ≤ 2 * Real.sqrt Real.pi * (‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    intro p
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (norm_nonneg p) (sq_nonneg _))
  have hw : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      2 * Real.sqrt Real.pi * (‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :=
    Integrable.const_mul hW (2 * Real.sqrt Real.pi)
  have hswap := integral_Ioi_integral_swap_of_nonneg
    (G := fun (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) =>
      (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2)
    (w := fun p : EuclideanSpace ℝ (Fin 3) =>
      2 * Real.sqrt Real.pi * (‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2))
    hG hnn hint hw0 hw hinner
  calc (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * (kinMass g - kinHeat g t))
      = ∫ t in Set.Ioi (0 : ℝ), ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3),
            (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
              ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        filter_upwards with t ht
        exact hpoint t ht
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ t in Set.Ioi (0 : ℝ),
            ∫ p : EuclideanSpace ℝ (Fin 3),
              (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
                ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
        rw [integral_const_mul]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3),
            ∫ t in Set.Ioi (0 : ℝ),
              (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
                ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
        rw [hswap]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3),
            2 * Real.sqrt Real.pi * (‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall (fun p => hinner p))]
    _ = 2 * Real.sqrt Real.pi * kinFirst g := by
        rw [integral_const_mul]
        unfold kinFirst
        ring

end Work.BoseBoxFock.SqrtKin
