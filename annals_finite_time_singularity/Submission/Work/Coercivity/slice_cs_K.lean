import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.tail_l2_cauchy_schwarz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Cauchy–Schwarz on an angular slice: for every `z`, if `θ ↦ (f z θ)²` is integrable on
`Iθ` then the squared angular average against `K = 3 sin θ cos²θ` is bounded by `3` times the
`θ`-energy of `f z ·`.

Intended proof: set `μ := volume.restrict Spaces.Iθ`. From `hL2` get
`AEStronglyMeasurable (fun θ => (f z θ) ^ 2) μ`, hence (composing with the continuous
`Real.sqrt` and using `Real.sqrt_sq_eq_abs`) `AEStronglyMeasurable (fun θ => |f z θ|) μ`;
`simp only [sq_abs]` turns `hL2` into `Integrable (fun θ => |f z θ| ^ 2) μ`, so
`MemLp (fun θ => |f z θ|) 2 μ` by `MeasureTheory.memLp_two_iff_integrable_sq`. Likewise
`hKi` plus continuity of `K` gives `MemLp Spaces.K 2 μ`. Then
`Work.Elliptic.integral_mul_sq_le_sq_mul_sq_aux μ` applied to `K` and `|f z ·|` (both
nonnegative a.e.; `0 ≤ᵐ K` from `hKnn` and `ae_restrict_of_forall_mem`) gives
`(∫ θ in Iθ, K θ * |f z θ|)² ≤ (∫ θ in Iθ, (K θ)²) * (∫ θ in Iθ, |f z θ|²)`.
Combine with `|∫ θ, K θ * f z θ| ≤ ∫ θ, |K θ * f z θ| = ∫ θ, K θ * |f z θ|`
(`abs_integral_le_integral_abs`; the equality uses `0 ≤ K` on `Iθ`), `hK2`, and
`∫ θ, |f z θ|² = ∫ θ, (f z θ)²`. Note no measurability of `f` is assumed: it is derived. -/
theorem slice_cs_K (f : ℝ → ℝ → ℝ) (z : ℝ)
    (hKnn : ∀ θ ∈ Spaces.Iθ, 0 ≤ Spaces.K θ)
    (hKi : MeasureTheory.IntegrableOn (fun θ => (Spaces.K θ) ^ 2) Spaces.Iθ)
    (hK2 : (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ 3)
    (hL2 : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ) :
    (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 ≤ 3 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2 := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Spaces.Iθ with hμ
  have hIθ_meas : MeasurableSet Spaces.Iθ := by
    rw [Spaces.Iθ]; exact measurableSet_Icc
  -- `K` is nonnegative a.e. on the slice
  have hKnn_ae : 0 ≤ᵐ[μ] Spaces.K := by
    rw [hμ]
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
    exact hKnn θ hθ
  -- `K` is measurable and `L²`
  have hKcont : Continuous Spaces.K := by
    unfold Spaces.K; fun_prop
  have hKmeas : MeasureTheory.AEStronglyMeasurable Spaces.K μ := hKcont.aestronglyMeasurable
  have hKint : MeasureTheory.Integrable (fun θ => (Spaces.K θ) ^ 2) μ := by
    rw [hμ]; exact hKi
  have hKmem : MeasureTheory.MemLp Spaces.K 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hKmeas).mpr hKint
  -- `|f z ·|` is measurable and `L²`
  have hf2_int : MeasureTheory.Integrable (fun θ => (f z θ) ^ 2) μ := by
    rw [hμ]; exact hL2
  have hmeas_sq : MeasureTheory.AEStronglyMeasurable (fun θ => (f z θ) ^ 2) μ :=
    hf2_int.aestronglyMeasurable
  have hmeas_abs : MeasureTheory.AEStronglyMeasurable (fun θ => |f z θ|) μ := by
    have h := Real.continuous_sqrt.comp_aestronglyMeasurable hmeas_sq
    simpa only [Real.sqrt_sq_eq_abs] using h
  have hint_abs2 : MeasureTheory.Integrable (fun θ => |f z θ| ^ 2) μ := by
    refine hf2_int.congr ?_
    filter_upwards with θ
    rw [sq_abs]
  have hmem_abs : MeasureTheory.MemLp (fun θ => |f z θ|) 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmeas_abs).mpr hint_abs2
  have habs_nn_ae : 0 ≤ᵐ[μ] (fun θ => |f z θ|) :=
    Filter.Eventually.of_forall fun θ => abs_nonneg _
  -- Cauchy–Schwarz
  have hcs := Work.Elliptic.integral_mul_sq_le_sq_mul_sq_aux μ hKmem hmem_abs hKnn_ae habs_nn_ae
  have hK2' : (∫ x, (Spaces.K x) ^ 2 ∂μ) ≤ 3 := by
    rw [hμ]; exact hK2
  have hfnn : 0 ≤ ∫ x, (f z x) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg (f z x))
  have habs2eq : (∫ x, |f z x| ^ 2 ∂μ) = ∫ x, (f z x) ^ 2 ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [sq_abs]
  -- Step 1: `∫ K * |f|` controls the square of the signed integral.
  have hstep1 : |∫ x, Spaces.K x * f z x ∂μ| ≤ ∫ x, Spaces.K x * |f z x| ∂μ := by
    refine (MeasureTheory.abs_integral_le_integral_abs (μ := μ)
      (f := fun x => Spaces.K x * f z x)).trans ?_
    apply le_of_eq
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hKnn_ae] with x hx
    rw [abs_mul, abs_of_nonneg hx]
  -- Step 2: Cauchy–Schwarz bound for `∫ K * |f|`.
  have hstep2 : (∫ x, Spaces.K x * |f z x| ∂μ) ^ 2 ≤ 3 * ∫ x, (f z x) ^ 2 ∂μ := by
    calc (∫ x, Spaces.K x * |f z x| ∂μ) ^ 2
        ≤ (∫ x, (Spaces.K x) ^ 2 ∂μ) * (∫ x, |f z x| ^ 2 ∂μ) := hcs
      _ = (∫ x, (Spaces.K x) ^ 2 ∂μ) * (∫ x, (f z x) ^ 2 ∂μ) := by rw [habs2eq]
      _ ≤ 3 * (∫ x, (f z x) ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_right hK2' hfnn
  calc (∫ x, Spaces.K x * f z x ∂μ) ^ 2
      = |∫ x, Spaces.K x * f z x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x, Spaces.K x * |f z x| ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hstep1 2
    _ ≤ 3 * ∫ x, (f z x) ^ 2 ∂μ := hstep2

end Work.Coercivity
