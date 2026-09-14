import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

namespace Commons.Measure.Mollification

open MeasureTheory Metric Set Filter Function VectorMeasure ContinuousLinearMap
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution

/-- The mollification of `ψ` by the normed bump `k`, written as an integral over the first
variable, is the convolution of `k.normed volume` with `ψ`. -/
lemma mollify_eq_convolution {n : ℕ} (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (k : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (t : EuclideanSpace ℝ (Fin n)) :
    (∫ z, ψ z * (k.normed volume) (z - t))
      = (k.normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t := by
  rw [convolution_lsmul_swap]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [← neg_sub z t, ContDiffBump.normed_neg]
  rw [smul_eq_mul, mul_comm]

/-- Uniform convergence of the mollification, in the form needed below: for every `ε > 0`, along
the filter the mollified functions are pointwise within `ε` of `ψ`. -/
lemma eventually_dist_convolution_le {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    {ι : Type*} {k : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))} {l : Filter ι}
    (h : Tendsto (fun i => (k i).rOut) l (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ t, dist (((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t) (ψ t) ≤ ε := by
  have huc : UniformContinuous ψ :=
    hψ.continuous.uniformContinuous_of_tendsto_cocompact hψc.is_zero_at_infty
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  filter_upwards [h.eventually (eventually_lt_nhds hδpos)] with i hi
  intro t
  refine ContDiffBump.dist_normed_convolution_le (φ := k i) (x₀ := t) (ε := ε)
    hψ.continuous.aestronglyMeasurable (fun x hx => ?_)
  rw [mem_ball] at hx
  exact le_of_lt (hδ (lt_trans hx hi))

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem tendsto_pairing_mollMeasure {n : ℕ} {ν : SignedMeasure (EuclideanSpace ℝ (Fin n))}
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    {ι : Type*} {k : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))} {l : Filter ι}
    (h : Tendsto (fun i => (k i).rOut) l (𝓝 0)) :
    Tendsto (fun i => ∫ᵛ t, (∫ z, ψ z * ((k i).normed volume) (z - t)) ∂•ν) l
      (𝓝 (∫ᵛ t, ψ t ∂•ν)) := by
  -- A signed measure has finite total variation.
  haveI hfin : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation ν]
    infer_instance
  -- Rewrite the integrand as a convolution.
  rw [show (fun i => ∫ᵛ t, (∫ z, ψ z * ((k i).normed volume) (z - t)) ∂•ν)
        = fun i => ∫ᵛ t, ((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t ∂•ν from
      funext fun i => by
        congr 1
        funext t
        exact mollify_eq_convolution ψ (k i) t]
  -- Now estimate.
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ.continuous
  set K : ℝ := ‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ * ν.variation.real univ with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; exact mul_nonneg (norm_nonneg _) measureReal_nonneg
  set ε₀ : ℝ := ε / (2 * (K + 1)) with hε₀def
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; positivity
  have hε₀K : ε₀ * K < ε := by
    rw [hε₀def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (K + 1))]
    nlinarith [hK0, hε]
  filter_upwards [eventually_dist_convolution_le hψ hψc h hε₀] with i hi
  -- `hi : ∀ t, dist (mollified i t) (ψ t) ≤ ε₀`.
  have hi' : ∀ t, ‖((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t - ψ t‖ ≤ ε₀ := fun t => by
    rw [← dist_eq_norm]; exact hi t
  have hcont : Continuous ((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) :=
    hψc.continuous_convolution_right (L := lsmul ℝ ℝ)
      ((k i).continuous_normed.locallyIntegrable) hψ.continuous
  have hCi : Integrable (fun t => ((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t)
      ν.variation :=
    Integrable.of_bound hcont.aestronglyMeasurable (M + ε₀) (Eventually.of_forall fun t => by
      have h1 : ‖((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t‖
          ≤ ‖ψ t‖ + ‖ψ t - ((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t‖ :=
        norm_le_norm_add_norm_sub (ψ t) (((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t)
      rw [norm_sub_rev] at h1
      exact h1.trans (add_le_add (hM t) (hi' t)))
  have hψint : Integrable ψ ν.variation :=
    Integrable.of_bound hψ.continuous.aestronglyMeasurable M (Eventually.of_forall hM)
  have hkey : dist (∫ᵛ t, ((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t ∂•ν)
        (∫ᵛ t, ψ t ∂•ν) ≤ ε₀ * K := by
    rw [dist_eq_norm, ← VectorMeasure.integral_fun_sub hCi hψint]
    calc ‖∫ᵛ t, (((k i).normed volume ⋆[lsmul ℝ ℝ, volume] ψ) t - ψ t) ∂•ν‖
        ≤ ε₀ * ‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ * ν.variation.real univ :=
          VectorMeasure.norm_integral_le_of_norm_le_const
            (Eventually.of_forall fun t => by rw [← dist_eq_norm]; exact hi t)
      _ = ε₀ * K := by rw [hKdef]; ring
  exact lt_of_le_of_lt hkey hε₀K

end Commons.Measure.Mollification