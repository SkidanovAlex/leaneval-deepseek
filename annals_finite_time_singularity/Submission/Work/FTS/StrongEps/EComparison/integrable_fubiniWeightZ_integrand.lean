import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- **Integrability of the `FubiniWeightZ` integrand on `[a,b] × [a,b]`.**

On the product `(volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))` the first coordinate
lies a.e. in the compact interval `[a,b]`, where `deriv (deriv ρ)` is bounded (it is continuous,
`ρ` being `C^∞`), and the second factor `(if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)` is
dominated by `(b - a) * ‖W p.2‖` (the indicator only cuts the integrand down, and
`p.2 - p.1 ≤ b - a`).  Because `[a,b] ⊆ (0,∞)` (as `a > 0`), the local integrability of `W` on
`(0,∞)` gives `IntegrableOn W (Icc a b)`, hence `fun p => ‖W p.2‖` is integrable on the product
measure; multiplying by the two constants and applying `Integrable.mono'` gives the claim. -/
theorem integrable_fubiniWeightZ_integrand {a b : ℝ} {W ρ : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) (ha : 0 < a) (hab : a < b)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => deriv (deriv ρ) p.1
        * (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0))
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc a b))) := by
  let ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc a b)
  change MeasureTheory.Integrable (fun p : ℝ × ℝ => deriv (deriv ρ) p.1 *
    (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)) (ν.prod ν)
  -- `W` is integrable on `[a,b]`, which sits inside `(0,∞)`.
  have hWint : MeasureTheory.Integrable W ν :=
    hW.integrableOn_compact_subset (fun x hx => lt_of_lt_of_le ha hx.1) isCompact_Icc
  -- `deriv (deriv ρ)` is continuous, hence bounded on the compact interval `[a,b]`.
  have hcont : Continuous (deriv (deriv ρ)) := by
    have h2 := (hρ 2).continuous_iteratedDeriv 2 le_rfl
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  -- The dominating function.
  have hdom : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => C * ((b - a) * ‖W p.2‖)) (ν.prod ν) :=
    ((hWint.norm.const_mul (b - a)).const_mul C).comp_snd ν
  -- A.e. the two coordinates lie in `[a,b]`.
  have hmem : ∀ᵐ p ∂(ν.prod ν), p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b := by
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem (μ := ν) (ν := ν)
      (s := Set.Icc a b ×ˢ Set.Icc a b) (measurableSet_Icc.prod measurableSet_Icc)).mpr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Icc] with x hx
    filter_upwards
      [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Icc] with y hy
    exact ⟨hx, hy⟩
  -- A.e. strong measurability of the integrand.
  have hF_aesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => deriv (deriv ρ) p.1 *
        (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)) (ν.prod ν) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => deriv (deriv ρ) p.1) (ν.prod ν) :=
      (hcont.comp continuous_fst).stronglyMeasurable.aestronglyMeasurable
    have hWsm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => W p.2) (ν.prod ν) :=
      ((hWint.aestronglyMeasurable).aemeasurable.comp_snd (μ := ν)).aestronglyMeasurable
    have hlin : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (p.2 - p.1)) (ν.prod ν) :=
      ((continuous_snd.sub continuous_fst).stronglyMeasurable.aestronglyMeasurable)
    have hind : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => if p.1 ≤ p.2 then (1 : ℝ) else 0) (ν.prod ν) :=
      (Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
        measurable_const).stronglyMeasurable.aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)) (ν.prod ν) := by
      rw [show (fun p : ℝ × ℝ => (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0))
          = (fun p : ℝ × ℝ => (if p.1 ≤ p.2 then (1 : ℝ) else 0) * ((p.2 - p.1) * W p.2)) from by
            funext p; by_cases h : p.1 ≤ p.2 <;> simp [h]]
      exact hind.mul (hlin.mul hWsm)
    exact h1.mul h2
  -- The a.e. pointwise domination.
  have hbound : ∀ᵐ p ∂(ν.prod ν), ‖deriv (deriv ρ) p.1 *
      (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0)‖ ≤ C * ((b - a) * ‖W p.2‖) := by
    filter_upwards [hmem] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hCb : ‖deriv (deriv ρ) p.1‖ ≤ C := hC p.1 hp1
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) hCb
    rw [norm_mul]
    refine mul_le_mul hCb ?_ (norm_nonneg _) hCnn
    by_cases h : p.1 ≤ p.2
    · rw [ite_eq_left h, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h)]
      have hle : p.2 - p.1 ≤ b - a := by linarith [hp1.1, hp2.2]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    · rw [ite_eq_right h, norm_zero]
      positivity
  exact MeasureTheory.Integrable.mono' hdom hF_aesm hbound

end Work.FTS.StrongEps.EComparison
