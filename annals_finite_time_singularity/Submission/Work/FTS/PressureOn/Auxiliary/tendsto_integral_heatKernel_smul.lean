import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.heatKernel_integral_one
import Submission.Work.FTS.PressureOn.Auxiliary.heatKernel_tail_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat kernel on `ℝ³` is an approximate identity at `t → 0⁺`

For a continuous bounded `u : ℝ³ → ℝ` and every `x`,

  `∫ y, u (x - y) * γ_t y → u x`  as `t → 0⁺`,

where `γ_t z = (4πt)^{-3/2} exp (-‖z‖²/(4t))` is the heat kernel
(`Work.FTS.PressureOn.Auxiliary.heatKernel`).

The proof is the textbook `ε/δ` argument for an approximate identity, in the form needed for a
merely *bounded* (not necessarily integrable) `u`:

* the kernel is a probability density, `∫ γ_t = 1` and `γ_t ∈ L¹`
  (`Work.FTS.PressureOn.Auxiliary.heatKernel_integral_one`);
* its mass outside the ball of radius `δ` decays like `2^{3/2} exp (-δ²/(8t))`
  (`Work.FTS.PressureOn.Auxiliary.heatKernel_tail_le`);
* by continuity of `u` at `x`, `u (x - y)` is close to `u x` for `‖y‖ < δ` and `γ_t` has total
  mass `1`, so the inner part contributes at most `ε/4`; the outer part is bounded by
  `2‖u‖_∞ · (tail mass)`, which is `< ε/4` for `t` small enough.
-/

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

theorem tendsto_integral_heatKernel_smul (u : Work.FTS.PressureOn.R3 → ℝ) (hu : Continuous u)
    (hbdd : ∃ C, ∀ x, |u x| ≤ C) (x : Work.FTS.PressureOn.R3) :
    Filter.Tendsto (fun t : ℝ =>
        ∫ y, u (x - y) * Work.FTS.PressureOn.Auxiliary.heatKernel t y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x)) := by
  obtain ⟨C, hC⟩ := hbdd
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (u x)) (hC x)
  -- `A` is the constant multiplying the tail mass in the outer estimate.
  set A : ℝ := 2 * C * 2 ^ (3 / 2 : ℝ) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h4 : 0 < ε / 4 := by linarith
  -- Continuity of `u` at `x`, transported to the shifted variable `x - y`.
  have hcontAt : ContinuousAt u x := hu.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousAt_iff.mp hcontAt) (ε / 4) h4
  have hδ' : ∀ y : R3, ‖y‖ < δ → |u (x - y) - u x| < ε / 4 := by
    intro y hy
    have hdist : dist (x - y) x < δ := by
      rw [dist_eq_norm]
      have hxy : x - y - x = -y := by abel
      rw [hxy, norm_neg]
      exact hy
    have hd : dist (u (x - y)) (u x) < ε / 4 := hδ hdist
    rwa [Real.dist_eq] at hd
  -- The tolerance for the tail mass: `A * ε' ≤ ε/4`.
  set ε' : ℝ := ε / (4 * (A + 1)) with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; positivity
  have hAε' : A * ε' ≤ ε / 4 := by
    rw [hε'def]
    have h1 : A * (ε / (4 * (A + 1))) = (ε / 4) * (A / (A + 1)) := by
      field_simp
    rw [h1]
    have h2 : A / (A + 1) ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < A + 1)]
      linarith
    calc (ε / 4) * (A / (A + 1)) ≤ (ε / 4) * 1 :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = ε / 4 := by ring
  -- The time scale on which the tail mass is `< ε'`.
  set M : ℝ := max (Real.log (1 / ε')) 1 with hMdef
  set t₀ : ℝ := δ ^ 2 / (8 * M) with ht₀def
  have hM1 : (1:ℝ) ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have ht₀pos : 0 < t₀ := by
    rw [ht₀def]; exact div_pos (pow_pos hδpos 2) (by linarith)
  have hmem : Ioo (0:ℝ) t₀ ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT ht₀pos
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, htt₀⟩ := ht
  have hexp_le : Real.exp (-(δ ^ 2 / (8 * t))) ≤ ε' := by
    have h1 : Real.log (1 / ε') ≤ δ ^ 2 / (8 * t) := by
      have hMle : M ≤ δ ^ 2 / (8 * t) := by
        have h8t : (0:ℝ) < 8 * t := by linarith
        have h8M : (0:ℝ) < 8 * M := by linarith
        have hlt : t * (8 * M) < t₀ * (8 * M) := mul_lt_mul_of_pos_right htt₀ h8M
        rw [ht₀def, div_mul_cancel₀ _ (ne_of_gt h8M)] at hlt
        exact le_of_lt ((lt_div_iff₀ h8t).mpr (by nlinarith))
      exact le_trans (by rw [hMdef]; exact le_max_left _ _) hMle
    calc Real.exp (-(δ ^ 2 / (8 * t))) ≤ Real.exp (-(Real.log (1 / ε'))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = ε' := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  -- Integrability bookkeeping.
  obtain ⟨hIntγ, hγ1⟩ := heatKernel_integral_one t ht0
  have hcontu : Continuous fun y : R3 => u (x - y) :=
    hu.comp (continuous_const.sub continuous_id)
  have hIntU : Integrable (fun y : R3 => u (x - y) * heatKernel t y) := by
    refine Integrable.mono' (hIntγ.const_mul C) ?_ ?_
    · exact hcontu.aestronglyMeasurable.mul hIntγ.aestronglyMeasurable
    · filter_upwards with y
      have h1 : |u (x - y)| ≤ C := hC (x - y)
      have h2 : 0 ≤ heatKernel t y := heatKernel_nonneg ht0.le y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
      exact mul_le_mul_of_nonneg_right h1 h2
  have hIntUx : Integrable (fun y : R3 => u x * heatKernel t y) := hIntγ.const_mul (u x)
  have h2C : ∀ y : R3, |u (x - y) - u x| ≤ 2 * C := by
    intro y
    have h1 : |u (x - y)| ≤ C := hC (x - y)
    have h2 : |u x| ≤ C := hC x
    calc |u (x - y) - u x| ≤ |u (x - y)| + |u x| := abs_sub _ _
      _ ≤ C + C := add_le_add h1 h2
      _ = 2 * C := by ring
  have hIntAbs : Integrable (fun y : R3 => |u (x - y) - u x| * heatKernel t y) := by
    refine Integrable.mono' (hIntγ.const_mul (2 * C)) ?_ ?_
    · exact (((hcontu.sub continuous_const).abs).aestronglyMeasurable).mul
        hIntγ.aestronglyMeasurable
    · filter_upwards with y
      have h2 : 0 ≤ heatKernel t y := heatKernel_nonneg ht0.le y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg (abs_nonneg _)]
      exact mul_le_mul_of_nonneg_right (h2C y) h2
  -- Rewrite the difference `∫ u(x-y)γ_t - u x` as the integral of the difference.
  have hsub : (∫ y, u (x - y) * heatKernel t y) - u x
      = ∫ y, (u (x - y) - u x) * heatKernel t y := by
    have hconst : u x = ∫ y, u x * heatKernel t y := by
      rw [MeasureTheory.integral_const_mul, hγ1, mul_one]
    conv_lhs => rw [hconst]
    rw [← MeasureTheory.integral_sub hIntU hIntUx]
    congr 1
    ext y
    ring
  have hnorm : |(∫ y, u (x - y) * heatKernel t y) - u x|
      ≤ ∫ y, |u (x - y) - u x| * heatKernel t y := by
    rw [hsub]
    calc |∫ y, (u (x - y) - u x) * heatKernel t y|
        ≤ ∫ y, |(u (x - y) - u x) * heatKernel t y| := abs_integral_le_integral_abs
      _ = ∫ y, |u (x - y) - u x| * heatKernel t y := by
          congr 1
          ext y
          rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht0.le y)]
  -- Split into the inner ball and the outer tail.
  have hsplit : (∫ y, |u (x - y) - u x| * heatKernel t y)
      = (∫ y in Metric.ball (0 : R3) δ, |u (x - y) - u x| * heatKernel t y)
        + (∫ y in (Metric.ball (0 : R3) δ)ᶜ, |u (x - y) - u x| * heatKernel t y) :=
    (integral_add_compl Metric.isOpen_ball.measurableSet hIntAbs).symm
  have hpiece1 : (∫ y in Metric.ball (0 : R3) δ, |u (x - y) - u x| * heatKernel t y)
      ≤ ε / 4 := by
    have h1 : (∫ y in Metric.ball (0 : R3) δ, |u (x - y) - u x| * heatKernel t y)
        ≤ ∫ y in Metric.ball (0 : R3) δ, (ε / 4) * heatKernel t y := by
      apply setIntegral_mono_on hIntAbs.integrableOn
        ((hIntγ.const_mul (ε / 4)).integrableOn) Metric.isOpen_ball.measurableSet
      intro y hy
      have hy' : ‖y‖ < δ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
        exact hy
      exact mul_le_mul_of_nonneg_right (le_of_lt (hδ' y hy')) (heatKernel_nonneg ht0.le y)
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul]
    calc (ε / 4) * ∫ y in Metric.ball (0 : R3) δ, heatKernel t y
        ≤ (ε / 4) * ∫ y : R3, heatKernel t y :=
          mul_le_mul_of_nonneg_left
            (setIntegral_le_integral hIntγ (Eventually.of_forall fun y => heatKernel_nonneg ht0.le y))
            (by linarith)
      _ = ε / 4 := by rw [hγ1, mul_one]
  have hpiece2 : (∫ y in (Metric.ball (0 : R3) δ)ᶜ, |u (x - y) - u x| * heatKernel t y)
      ≤ ε / 4 := by
    have h1 : (∫ y in (Metric.ball (0 : R3) δ)ᶜ, |u (x - y) - u x| * heatKernel t y)
        ≤ ∫ y in (Metric.ball (0 : R3) δ)ᶜ, (2 * C) * heatKernel t y := by
      apply setIntegral_mono_on hIntAbs.integrableOn
        ((hIntγ.const_mul (2 * C)).integrableOn) Metric.isOpen_ball.measurableSet.compl
      intro y _
      exact mul_le_mul_of_nonneg_right (h2C y) (heatKernel_nonneg ht0.le y)
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul]
    have hset : (Metric.ball (0 : R3) δ)ᶜ = {y : R3 | δ ≤ ‖y‖} := by
      ext y
      rw [Set.mem_compl_iff, Metric.mem_ball, dist_eq_norm, sub_zero]
      exact not_lt
    have htail : (∫ y in (Metric.ball (0 : R3) δ)ᶜ, heatKernel t y)
        ≤ 2 ^ (3 / 2 : ℝ) * Real.exp (-(δ ^ 2 / (8 * t))) := by
      rw [hset]
      exact heatKernel_tail_le t δ ht0 hδpos
    calc (2 * C) * ∫ y in (Metric.ball (0 : R3) δ)ᶜ, heatKernel t y
        ≤ (2 * C) * (2 ^ (3 / 2 : ℝ) * Real.exp (-(δ ^ 2 / (8 * t)))) :=
          mul_le_mul_of_nonneg_left htail (by linarith)
      _ = A * Real.exp (-(δ ^ 2 / (8 * t))) := by rw [hAdef]; ring
      _ ≤ A * ε' := mul_le_mul_of_nonneg_left hexp_le hA0
      _ ≤ ε / 4 := hAε'
  calc dist (∫ y, u (x - y) * heatKernel t y) (u x)
      = |(∫ y, u (x - y) * heatKernel t y) - u x| := Real.dist_eq _ _
    _ ≤ ∫ y, |u (x - y) - u x| * heatKernel t y := hnorm
    _ = (∫ y in Metric.ball (0 : R3) δ, |u (x - y) - u x| * heatKernel t y)
        + (∫ y in (Metric.ball (0 : R3) δ)ᶜ, |u (x - y) - u x| * heatKernel t y) := hsplit
    _ ≤ ε / 4 + ε / 4 := add_le_add hpiece1 hpiece2
    _ = ε / 2 := by ring
    _ < ε := by linarith

end

end Work.FTS.PressureOn.Auxiliary
