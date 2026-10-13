/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsSqIntegration` — Minkowski's inequality for the `L²`-norm of a parameter integral

The lemma `EpsSq_integral_le` of this directory states that the weighted `L²`-size `EpsSq` of the
parameter integral `z ↦ ∫_0^τ g s z θ ds` is at most the square of the integral of the `L²`-sizes
`√(EpsSq (g s))`.  This is Minkowski's (triangle) inequality for the `L²`-norm of a Bochner
integral in the space `L²(wtG α)`, stated for the *iterated* representation of `EpsSq` used
throughout the project.

Mathlib has Minkowski's inequality for sums and for the `ℒ^p` seminorm of a sum of two functions,
but not the integral form needed here (the `L²`-norm of the integral of a curve of functions is at
most the integral of the `L²`-norms).  We prove it here, in a general form, for a curve
`F : ℝ → P → ℝ` of real functions on a measure space `(P, μ)`:

* `l2_cs` — the pointwise Cauchy–Schwarz inequality `(∫⁻ |f|)² ≤ (∫⁻ f²/b)(∫⁻ b)` in `ℝ≥0∞`
  (this is `ℚ`-Hölder with the weight `b`; written in the `ofReal`-form in which it is applied);
* `l2_integral_le` — the general statement: for an a.e.-strongly-measurable `uncurry F`, with the
  `s`-slices square-integrable in `p` a.e. and `s ↦ √(∫_p F s p²)` integrable,
  `∫_p (∫_s F s p)² ≤ (∫_s √(∫_p F s p²))²`, and the left-hand integrand is integrable.

The proof is the classical one: Cauchy–Schwarz in the parameter `s` with the weight
`b s = a s + ε` (`a s = √(∫_p F s p²)`), Tonelli in the two variables `(s,p)`, then `ε → 0`.
Everything is done in `ℝ≥0∞` via `ENNReal.ofReal`, `enorm_integral_le_lintegral_enorm` and the
Tonelli/Hölder lemmas for `lintegral`, so that only the a.e.-strong-measurability of `uncurry F`
(which is the hypothesis available in the application) is needed.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.UniformSpace.Uniformizable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `ENNReal.ofReal` turns a square into the square of the absolute value. -/
lemma ofReal_sq_abs (y : ℝ) : ENNReal.ofReal (y ^ 2) = (ENNReal.ofReal |y|) ^ 2 := by
  rw [sq, ← abs_mul_abs_self y, ENNReal.ofReal_mul (abs_nonneg y), sq]

/-- The square of the half-power is the number itself. -/
lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ ((1:ℝ)/2)) ^ (2:ℕ) = x := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num

/-- **Cauchy–Schwarz with a weight**, in the `ℝ≥0∞`-form used below:
`(∫⁻ |f|)² ≤ (∫⁻ f²/b) · (∫⁻ b)` for `b > 0`.  This is Hölder's inequality with exponents
`p = q = 2` applied to `|f|/√b` and `√b`. -/
lemma l2_cs {ν : Measure ℝ} [IsFiniteMeasure ν] {b : ℝ → ℝ} (hb_meas : AEMeasurable b ν)
    (hb_pos : ∀ s, 0 < b s) {f : ℝ → ℝ} (hf_meas : AEMeasurable f ν) :
    (∫⁻ s, ENNReal.ofReal |f s| ∂ν) ^ 2
      ≤ (∫⁻ s, ENNReal.ofReal (f s ^ 2 / b s) ∂ν) * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb_nn : ∀ s, 0 ≤ b s := fun s => (hb_pos s).le
  have hsq_meas : AEMeasurable (fun s => Real.sqrt (b s)) ν := hb_meas.sqrt
  have hf1 : AEMeasurable (fun s => ENNReal.ofReal (|f s| / Real.sqrt (b s))) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hf_meas.abs.div hsq_meas)
  have hg1 : AEMeasurable (fun s => ENNReal.ofReal (Real.sqrt (b s))) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable hsq_meas
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hf1 hg1
  have hconv : (∫⁻ a, ((fun s => ENNReal.ofReal (|f s| / Real.sqrt (b s)))
      * fun s => ENNReal.ofReal (Real.sqrt (b s))) a ∂ν) = ∫⁻ s, ENNReal.ofReal |f s| ∂ν := by
    refine lintegral_congr (fun s => ?_)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
      div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 (hb_pos s)))]
  rw [hconv] at h
  have hf1sq : (fun s => (ENNReal.ofReal (|f s| / Real.sqrt (b s))) ^ (2:ℝ))
      = fun s => ENNReal.ofReal (f s ^ 2 / b s) := by
    funext s
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
      div_pow, sq_abs, Real.sq_sqrt (hb_nn s)]
  have hg1sq : (fun s => (ENNReal.ofReal (Real.sqrt (b s))) ^ (2:ℝ))
      = fun s => ENNReal.ofReal (b s) := by
    funext s
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hb_nn s)]
  rw [hf1sq, hg1sq] at h
  calc (∫⁻ s, ENNReal.ofReal |f s| ∂ν) ^ 2
      ≤ ((∫⁻ s, ENNReal.ofReal (f s ^ 2 / b s) ∂ν) ^ ((1:ℝ)/2)
          * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) ^ ((1:ℝ)/2)) ^ 2 :=
        pow_le_pow_left₀ bot_le h 2
    _ = (∫⁻ s, ENNReal.ofReal (f s ^ 2 / b s) ∂ν) * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq]

/-- **Minkowski's inequality for the `L²`-norm of a parameter integral.**  For a curve
`F : ℝ → P → ℝ` of functions on a measure space `(P, μ)` which is a.e. strongly measurable as a
function of the pair, whose `s`-slices are square-integrable in `p` for a.e. `s`, and for which
`s ↦ √(∫_p F s p²)` is integrable,

`∫_p (∫_s F s p ∂ν)² ∂μ ≤ (∫_s √(∫_p F s p² ∂μ) ∂ν)²`,

and the left-hand integrand is `μ`-integrable. -/
theorem l2_integral_le {P : Type*} [MeasurableSpace P] {μ : Measure P} {ν : Measure ℝ}
    [SFinite μ] [IsFiniteMeasure ν] {F : ℝ → P → ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry F) (ν.prod μ))
    (hsq : ∀ᵐ s ∂ν, Integrable (fun p => (F s p) ^ 2) μ)
    (hint : Integrable (fun s => Real.sqrt (∫ p, (F s p) ^ 2 ∂μ)) ν) :
    Integrable (fun p => (∫ s, F s p ∂ν) ^ 2) μ ∧
      ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ
        ≤ (∫ s, Real.sqrt (∫ p, (F s p) ^ 2 ∂μ) ∂ν) ^ 2 := by
  classical
  set a : ℝ → ℝ := fun s => Real.sqrt (∫ p, (F s p) ^ 2 ∂μ) with ha_def
  have ha_nn : ∀ s, 0 ≤ a s := fun s => Real.sqrt_nonneg _
  have ha_sq : ∀ s, a s ^ 2 = ∫ p, (F s p) ^ 2 ∂μ := fun s => by
    rw [ha_def]; exact Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)
  have ha_meas : AEMeasurable a ν := hint.aemeasurable
  set A : ℝ := ∫ s, a s ∂ν with hA_def
  have hA_nn : 0 ≤ A := integral_nonneg ha_nn
  have hslice_p : ∀ᵐ p ∂μ, AEStronglyMeasurable (fun s => F s p) ν := hmeas.prodMk_right
  -- The main chain, with the weight `b = a + ε`.
  have key : ∀ ε : ℝ, 0 < ε →
      ∫⁻ p, ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2) ∂μ
        ≤ ENNReal.ofReal ((A + ε * (ν Set.univ).toReal) * A) := by
    intro ε hε
    set b : ℝ → ℝ := fun s => a s + ε with hb_def
    have hb_pos : ∀ s, 0 < b s := fun s => by rw [hb_def]; linarith [ha_nn s, hε]
    have hb_nn : ∀ s, 0 ≤ b s := fun s => (hb_pos s).le
    have hb_meas : AEMeasurable b ν := ha_meas.add aemeasurable_const
    have hb_int : Integrable b ν := hint.add (integrable_const ε)
    have hBval : ∫ s, b s ∂ν = A + ε * (ν Set.univ).toReal := by
      rw [hb_def, integral_add hint (integrable_const ε), hA_def, integral_const]
      simp only [Measure.real, smul_eq_mul]
      ring
    have hofB : ENNReal.ofReal (∫ s, b s ∂ν) = ∫⁻ s, ENNReal.ofReal (b s) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hb_int (ae_of_all _ hb_nn)
    -- the pointwise (a.e. in `p`) Cauchy–Schwarz inequality
    have hpt : ∀ᵐ p ∂μ, ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2)
        ≤ (∫⁻ s, ENNReal.ofReal (F s p ^ 2 / b s) ∂ν) * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
      filter_upwards [hslice_p] with p hp
      calc ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2)
          = (ENNReal.ofReal |∫ s, F s p ∂ν|) ^ 2 := ofReal_sq_abs _
        _ ≤ (∫⁻ s, ENNReal.ofReal |F s p| ∂ν) ^ 2 := by
              refine pow_le_pow_left₀ bot_le ?_ 2
              have h := enorm_integral_le_lintegral_enorm (μ := ν) (fun s => F s p)
              simpa [Real.enorm_eq_ofReal_abs] using h
        _ ≤ _ := l2_cs hb_meas hb_pos hp.aemeasurable
    -- joint measurability for Tonelli
    have hmeasG : AEMeasurable (fun q : P × ℝ => ENNReal.ofReal (F q.2 q.1 ^ 2 / b q.2))
        (μ.prod ν) := by
      have h1 : AEMeasurable (fun q : P × ℝ => F q.2 q.1) (μ.prod ν) :=
        hmeas.prod_swap.aemeasurable
      have h2 : AEMeasurable (fun q : P × ℝ => b q.2) (μ.prod ν) := hb_meas.comp_snd
      exact ENNReal.measurable_ofReal.comp_aemeasurable ((h1.pow_const 2).div h2)
    -- the `s`-slices of `F ·²/b` are integrable for a.e. `s`
    have hGint : ∀ᵐ s ∂ν, Integrable (fun p => F s p ^ 2 / b s) μ :=
      hsq.mono fun s hs => hs.div_const (b s)
    -- the inner integral collapses to `ofReal (a s)`
    have hinner : ∀ᵐ s ∂ν, (∫⁻ p, ENNReal.ofReal (F s p ^ 2 / b s) ∂μ)
        ≤ ENNReal.ofReal (a s) := by
      filter_upwards [hGint] with s hs
      rw [← ofReal_integral_eq_lintegral_ofReal hs
        (ae_of_all _ (fun p => div_nonneg (sq_nonneg _) (hb_nn s))), integral_div, ← ha_sq s]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ (hb_pos s)]
      nlinarith [ha_nn s, hε]
    calc ∫⁻ p, ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2) ∂μ
        ≤ ∫⁻ p, (∫⁻ s, ENNReal.ofReal (F s p ^ 2 / b s) ∂ν)
            * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) ∂μ :=
          lintegral_mono_ae hpt
      _ = (∫⁻ p, ∫⁻ s, ENNReal.ofReal (F s p ^ 2 / b s) ∂ν ∂μ)
            * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) :=
          lintegral_mul_const' _ _ (by rw [← hofB]; exact ENNReal.ofReal_lt_top.ne)
      _ = (∫⁻ s, ∫⁻ p, ENNReal.ofReal (F s p ^ 2 / b s) ∂μ ∂ν)
            * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
          rw [lintegral_lintegral_swap hmeasG]
      _ ≤ (∫⁻ s, ENNReal.ofReal (a s) ∂ν) * (∫⁻ s, ENNReal.ofReal (b s) ∂ν) := by
          exact mul_le_mul_of_nonneg_right (lintegral_mono_ae hinner) bot_le
      _ = ENNReal.ofReal A * ENNReal.ofReal (∫ s, b s ∂ν) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ ha_nn), hofB]
      _ = ENNReal.ofReal (A * (A + ε * (ν Set.univ).toReal)) := by
          rw [← hBval, ← ENNReal.ofReal_mul hA_nn]
      _ = ENNReal.ofReal ((A + ε * (ν Set.univ).toReal) * A) := by
          rw [mul_comm]
  have hnorm : ENNReal.ofReal (∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ)
      ≤ ∫⁻ p, ENNReal.ofReal ((∫ s, F s p ∂ν) ^ 2) ∂μ := by
    have h := enorm_integral_le_lintegral_enorm (μ := μ) (fun p => (∫ s, F s p ∂ν) ^ 2)
    rw [Real.enorm_eq_ofReal (integral_nonneg (fun p => sq_nonneg _))] at h
    refine h.trans_eq (lintegral_congr (fun p => ?_))
    exact Real.enorm_eq_ofReal (sq_nonneg _)
  -- the integrand is a.e. strongly measurable
  have hmeas_int : AEStronglyMeasurable (fun p => (∫ s, F s p ∂ν) ^ 2) μ :=
    hmeas.prod_swap.integral_prod_right'.pow 2
  -- and has finite `lintegral` of its norm
  have hfin : ∫⁻ p, ‖(∫ s, F s p ∂ν) ^ 2‖ₑ ∂μ < ∞ := by
    rw [lintegral_congr (fun p => Real.enorm_eq_ofReal (sq_nonneg _))]
    exact lt_of_le_of_lt (key 1 one_pos) ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas_int, hasFiniteIntegral_iff_enorm.mpr hfin⟩, ?_⟩
  -- the bound
  have hle : ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ ≤ A * A := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have hc_nn : 0 ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
    have hden : 0 < (ν Set.univ).toReal * A + 1 := by nlinarith
    have h := hnorm.trans (key (δ / ((ν Set.univ).toReal * A + 1)) (by positivity))
    have hY : 0 ≤ (A + δ / ((ν Set.univ).toReal * A + 1) * (ν Set.univ).toReal) * A :=
      mul_nonneg (add_nonneg hA_nn (mul_nonneg (div_nonneg hδ.le hden.le) hc_nn)) hA_nn
    have h' : ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ
        ≤ (A + δ / ((ν Set.univ).toReal * A + 1) * (ν Set.univ).toReal) * A :=
      (ENNReal.ofReal_le_ofReal_iff hY).mp h
    have h4 : δ * ((ν Set.univ).toReal * A) / ((ν Set.univ).toReal * A + 1) ≤ δ := by
      rw [div_le_iff₀ hden]
      exact mul_le_mul_of_nonneg_left (by linarith) hδ.le
    calc ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ
        ≤ (A + δ / ((ν Set.univ).toReal * A + 1) * (ν Set.univ).toReal) * A := h'
      _ = A * A + δ * ((ν Set.univ).toReal * A) / ((ν Set.univ).toReal * A + 1) := by ring
      _ ≤ A * A + δ := by linarith
  calc ∫ p, (∫ s, F s p ∂ν) ^ 2 ∂μ ≤ A * A := hle
    _ = (∫ s, Real.sqrt (∫ p, (F s p) ^ 2 ∂μ) ∂ν) ^ 2 := by rw [hA_def, ha_def, sq]

end Work.FTS.StrongEps.EpsLocalPStar
