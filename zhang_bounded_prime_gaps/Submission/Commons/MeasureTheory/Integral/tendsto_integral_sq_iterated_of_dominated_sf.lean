import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory Filter
open scoped Topology

/-- Dominated convergence for iterated integrals of squares: if `f n u x → g u x` pointwise
a.e. on the product, all `f n` are dominated by `b`, and the marginal `u ↦ ∫ x, b u x` is in
`L²(ν)`, then `∫ u, (∫ x, f n u x)² ∂ν → ∫ u, (∫ x, g u x)² ∂ν`.  (`μ` is required to be
σ-finite so that a.e. statements on the product may be sliced.) -/
theorem tendsto_integral_sq_iterated_of_dominated_sf {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : _root_.MeasureTheory.Measure α} [SFinite μ]
    {ν : _root_.MeasureTheory.Measure β}
    {f : ℕ → β → α → ℝ} {g b : β → α → ℝ}
    (hb : _root_.MeasureTheory.Integrable (fun u => (∫ x, b u x ∂μ) ^ 2) ν)
    (hbm : ∀ᵐ u ∂ν, _root_.MeasureTheory.Integrable (b u) μ)
    (hf : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable
      (fun p : β × α => f n p.1 p.2) (ν.prod μ))
    (hg : _root_.MeasureTheory.AEStronglyMeasurable
      (fun p : β × α => g p.1 p.2) (ν.prod μ))
    (hconv : ∀ᵐ p ∂(ν.prod μ), Tendsto (fun n => f n p.1 p.2) atTop (𝓝 (g p.1 p.2)))
    (hbound : ∀ᵐ p ∂(ν.prod μ), ∀ n, |f n p.1 p.2| ≤ b p.1 p.2) :
    Tendsto (fun n => ∫ u, (∫ x, f n u x ∂μ) ^ 2 ∂ν) atTop
      (𝓝 (∫ u, (∫ x, g u x ∂μ) ^ 2 ∂ν)) := by
  -- Slice the product-a.e. hypotheses.
  have hconv_slice : ∀ᵐ u ∂ν, ∀ᵐ x ∂μ, Tendsto (fun n => f n u x) atTop (𝓝 (g u x)) :=
    Measure.ae_ae_of_ae_prod hconv
  have hbound_slice : ∀ᵐ u ∂ν, ∀ᵐ x ∂μ, ∀ n, ‖f n u x‖ ≤ b u x := by
    filter_upwards [Measure.ae_ae_of_ae_prod hbound] with u hu
    filter_upwards [hu] with x hx
    intro n
    simpa [Real.norm_eq_abs] using hx n
  have hfsec : ∀ᵐ u ∂ν, ∀ n, AEStronglyMeasurable (fun x => f n u x) μ :=
    ae_all_iff.2 fun n => (hf n).prodMk_left
  -- Pointwise bound of each inner integral.
  have hbound_outer : ∀ n, ∀ᵐ u ∂ν,
      ‖(∫ x, f n u x ∂μ) ^ 2‖ ≤ (∫ x, b u x ∂μ) ^ 2 := by
    intro n
    filter_upwards [hbm, hbound_slice, (hf n).prodMk_left] with u hbu hbd hfmu
    have hint : Integrable (fun x => f n u x) μ :=
      Integrable.mono' hbu hfmu (hbd.mono fun x hx => hx n)
    have hab : ‖∫ x, f n u x ∂μ‖ ≤ ∫ x, b u x ∂μ :=
      calc ‖∫ x, f n u x ∂μ‖
          ≤ ∫ x, ‖f n u x‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ x, b u x ∂μ := integral_mono_ae hint.norm hbu (hbd.mono fun x hx => hx n)
    rw [Real.norm_of_nonneg (sq_nonneg (∫ x, f n u x ∂μ))]
    have h2 := pow_le_pow_left₀ (norm_nonneg (∫ x, f n u x ∂μ)) hab 2
    have h3 : ‖∫ x, f n u x ∂μ‖ ^ 2 = (∫ x, f n u x ∂μ) ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    simpa only [h3] using h2
  -- Pointwise convergence of the squares of the inner integrals.
  have hlim_outer : ∀ᵐ u ∂ν,
      Tendsto (fun n => (∫ x, f n u x ∂μ) ^ 2) atTop (𝓝 ((∫ x, g u x ∂μ) ^ 2)) := by
    filter_upwards [hbm, hconv_slice, hbound_slice, hfsec] with u hbu hcv hbd hfmu
    have hinner : Tendsto (fun n => ∫ x, f n u x ∂μ) atTop (𝓝 (∫ x, g u x ∂μ)) :=
      tendsto_integral_of_dominated_convergence (b u) hfmu hbu
        (fun n => hbd.mono fun x hx => hx n) hcv
    exact hinner.pow 2
  -- Outer dominated convergence.
  exact tendsto_integral_of_dominated_convergence (fun u => (∫ x, b u x ∂μ) ^ 2)
    (fun n => ((hf n).integral_prod_right').pow 2) hb hbound_outer hlim_outer

end Commons.MeasureTheory.Integral