import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.integral_heatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat kernel escapes every ball as `t → 0⁺`

For `δ > 0` the mass of the heat kernel `γ_t z = (4πt)^{-3/2} exp (-‖z‖²/(4t))` on `ℝ³` outside
the ball of radius `δ` tends to `0` as `t → 0⁺`: the kernel concentrates at the origin.

The pointwise input is the exact split of the exponent

  `γ_t z = 2^{3/2} γ_{2t} z · exp (-‖z‖²/(8t))`,

so for `‖z‖ ≥ δ`

  `γ_t z ≤ 2^{3/2} exp (-δ²/(8t)) · γ_{2t} z`.

Integrating over the tail and using the normalisation `∫ γ_{2t} = 1`
(`Work.FTS.PressureOn.Auxiliary.integral_heatKernel`) gives

  `∫_{‖z‖ ≥ δ} γ_t ≤ 2^{3/2} exp (-δ²/(8t))`,

and `exp (-δ²/(8t)) → 0` because `δ²/(8t) → +∞` as `t → 0⁺`.
-/

open MeasureTheory Set Filter Topology
open scoped Topology

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- `2^{3/2} · 2^{-3/2} = 1`. -/
private lemma two_rpow_three_halves_mul_inv :
    (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ) = 1 := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_inv_cancel₀
    (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (3 / 2 : ℝ)))

/-- `(4πt)^{-3/2} = 2^{3/2} (8πt)^{-3/2}` for `t > 0`. -/
private lemma four_pi_mul_rpow_eq (t : ℝ) (ht : 0 < t) :
    (2 : ℝ) ^ (3 / 2 : ℝ) * (8 * Real.pi * t) ^ (-(3 / 2) : ℝ)
      = (4 * Real.pi * t) ^ (-(3 / 2) : ℝ) := by
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  rw [show (8 : ℝ) * Real.pi * t = 2 * (4 * Real.pi * t) by ring,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) h4.le, ← mul_assoc,
    two_rpow_three_halves_mul_inv, one_mul]

/-- The heat kernel at time `2t`, written with the Gaussian `exp (-‖z‖²/(8t))`. -/
private lemma heatKernel_two_mul_apply (t : ℝ) (z : R3) :
    heatKernel (2 * t) z
      = (8 * Real.pi * t) ^ (-(3 / 2) : ℝ) * Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
  rw [heatKernel_apply, show (4 : ℝ) * Real.pi * (2 * t) = 8 * Real.pi * t by ring,
    show (4 : ℝ) * (2 * t) = 8 * t by ring]

/-- Splitting the exponent: `exp (-‖z‖²/(4t)) = exp (-‖z‖²/(8t)) ^ 2` for `t ≠ 0`. -/
private lemma exp_split (t : ℝ) (ht : t ≠ 0) (z : R3) :
    Real.exp (-(‖z‖ ^ 2 / (4 * t)))
      = Real.exp (-(‖z‖ ^ 2 / (8 * t))) * Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
  rw [← Real.exp_add]
  congr 1
  have h4t : (4 : ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have h8t : (8 : ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have h : ‖z‖ ^ 2 / (4 * t) = ‖z‖ ^ 2 / (8 * t) + ‖z‖ ^ 2 / (8 * t) := by
    rw [← add_div, div_eq_iff h4t, div_mul_eq_mul_div₀, eq_div_iff h8t]
    ring
  linarith

/-- **The self-similarity identity for the heat kernel on `ℝ³`**:
`γ_t z = 2^{3/2} γ_{2t} z · exp (-‖z‖²/(8t))` for `t > 0`. -/
private lemma heatKernel_eq_const_mul (t : ℝ) (ht : 0 < t) (z : R3) :
    heatKernel t z
      = (2 : ℝ) ^ (3 / 2 : ℝ) * (heatKernel (2 * t) z * Real.exp (-(‖z‖ ^ 2 / (8 * t)))) := by
  rw [heatKernel_apply, ← four_pi_mul_rpow_eq t ht, heatKernel_two_mul_apply,
    exp_split t (ne_of_gt ht) z]
  ring

/-- **Pointwise comparison.**  Outside the ball of radius `δ` the heat kernel at time `t` is
dominated by `exp (-δ²/(8t))` times `2^{3/2}` times the heat kernel at time `2t`. -/
private lemma heatKernel_le_const_mul {t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) {z : R3}
    (hz : δ ≤ ‖z‖) :
    heatKernel t z
      ≤ Real.exp (-(δ ^ 2 / (8 * t))) * ((2 : ℝ) ^ (3 / 2 : ℝ) * heatKernel (2 * t) z) := by
  have h2t : (0 : ℝ) ≤ 2 * t := by linarith
  have hexp : Real.exp (-(‖z‖ ^ 2 / (8 * t))) ≤ Real.exp (-(δ ^ 2 / (8 * t))) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : δ ^ 2 / (8 * t) ≤ ‖z‖ ^ 2 / (8 * t) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hδ hz 2) (by positivity)
    linarith
  calc heatKernel t z
      = (2 : ℝ) ^ (3 / 2 : ℝ) * (heatKernel (2 * t) z * Real.exp (-(‖z‖ ^ 2 / (8 * t)))) :=
        heatKernel_eq_const_mul t ht z
    _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (heatKernel (2 * t) z * Real.exp (-(δ ^ 2 / (8 * t)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (heatKernel_nonneg h2t z))
          (Real.rpow_nonneg (by norm_num) _)
    _ = Real.exp (-(δ ^ 2 / (8 * t))) * ((2 : ℝ) ^ (3 / 2 : ℝ) * heatKernel (2 * t) z) := by
        ring

/-- The heat kernel is integrable at positive times (its mass is `1`). -/
private lemma integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) := by
  by_contra hf
  have h := integral_heatKernel t ht
  rw [integral_undef hf] at h
  exact one_ne_zero h.symm

theorem tendsto_tail_heatKernel (δ : ℝ) (hδ : 0 < δ) :
    Filter.Tendsto (fun t : ℝ =>
        ∫ z in {z : Work.FTS.PressureOn.R3 | δ ≤ ‖z‖}, Work.FTS.PressureOn.Auxiliary.heatKernel t z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set S : Set R3 := {z : R3 | δ ≤ ‖z‖} with hS
  have hSmeas : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  -- the majorant tends to `0` at `0⁺`
  have hlim : Filter.Tendsto
      (fun t : ℝ => Real.exp (-(δ ^ 2 / (8 * t))) * (2 : ℝ) ^ (3 / 2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => δ ^ 2 / 8 * t⁻¹) (nhdsWithin 0 (Set.Ioi 0))
        atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero
    have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-(δ ^ 2 / (8 * t))))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      refine Real.tendsto_exp_neg_atTop_nhds_zero.comp h1 |>.congr' ?_
      filter_upwards with t
      simp only [Function.comp_apply]
      rw [show δ ^ 2 / 8 * t⁻¹ = δ ^ 2 / (8 * t) by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring]
    simpa using h2.mul_const ((2 : ℝ) ^ (3 / 2 : ℝ))
  refine squeeze_zero' ?_ ?_ hlim
  · -- nonnegativity of the tail mass
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact integral_nonneg fun z => heatKernel_nonneg ht.le z
  · -- the tail estimate
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := by simpa using ht
    have h2t : (0 : ℝ) < 2 * t := by linarith
    have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
    calc ∫ z in S, heatKernel t z
        ≤ ∫ z in S,
            Real.exp (-(δ ^ 2 / (8 * t))) * ((2 : ℝ) ^ (3 / 2 : ℝ) * heatKernel (2 * t) z) := by
          refine setIntegral_mono_on (integrable_heatKernel ht).integrableOn ?_ hSmeas
            (fun z hz => heatKernel_le_const_mul ht hδ.le hz)
          exact (((integrable_heatKernel h2t).const_mul ((2 : ℝ) ^ (3 / 2 : ℝ))).const_mul
            (Real.exp (-(δ ^ 2 / (8 * t))))).integrableOn
      _ = Real.exp (-(δ ^ 2 / (8 * t)))
            * ((2 : ℝ) ^ (3 / 2 : ℝ) * ∫ z in S, heatKernel (2 * t) z) := by
          rw [integral_const_mul, integral_const_mul]
      _ ≤ Real.exp (-(δ ^ 2 / (8 * t)))
            * ((2 : ℝ) ^ (3 / 2 : ℝ) * ∫ z : R3, heatKernel (2 * t) z) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          refine mul_le_mul_of_nonneg_left ?_ hc
          exact setIntegral_le_integral (integrable_heatKernel h2t)
            (Filter.Eventually.of_forall fun z => heatKernel_nonneg h2t.le z)
      _ = Real.exp (-(δ ^ 2 / (8 * t))) * (2 : ℝ) ^ (3 / 2 : ℝ) := by
          rw [integral_heatKernel (2 * t) h2t, mul_one]

end

end Work.FTS.PressureOn.Auxiliary
