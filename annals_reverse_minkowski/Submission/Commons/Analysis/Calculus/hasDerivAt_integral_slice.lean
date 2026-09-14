import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace Commons.Analysis.Calculus

open MeasureTheory Set Real Filter
open scoped Real Topology InnerProductSpace

/-- Parametric differentiation under the integral sign for a slice integral
`y ↦ ∫ z, Φ (z, y)`, with a uniform bound on the partial `y`-derivative. -/
theorem hasDerivAt_integral_slice {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    (Φ : G × ℝ → ℝ) (y₀ : ℝ) (bound : G → ℝ)
    (hΦ : ContDiff ℝ 1 Φ) (hbound : Integrable bound)
    (hint : Integrable (fun z : G => Φ (z, y₀)))
    (hdom : ∀ z : G, ∀ y : ℝ, y ∈ Set.Ioo (y₀ - 1) (y₀ + 1) →
      ‖fderiv ℝ Φ (z, y) (0, 1)‖ ≤ bound z) :
    HasDerivAt (fun y => ∫ z : G, Φ (z, y))
      (∫ z : G, fderiv ℝ Φ (z, y₀) (0, 1)) y₀ := by
  have h1 : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  -- derivative with respect to the second coordinate (chain rule)
  have hdiff : ∀ z : G, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Φ (z, y)) (fderiv ℝ Φ (z, x) (0, 1)) x := by
    intro z x
    have hg : HasFDerivAt (fun y : ℝ => (z, y)) (ContinuousLinearMap.inr ℝ G ℝ) x :=
      hasFDerivAt_prodMk_right z x
    have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (z, x)) (z, x) :=
      ((hΦ.differentiable h1) (z, x)).hasFDerivAt
    have hcomp : HasFDerivAt (fun y : ℝ => Φ (z, y))
        ((fderiv ℝ Φ (z, x)).comp (ContinuousLinearMap.inr ℝ G ℝ)) x := by
      have := hΦd.comp x hg
      simpa [Function.comp_def] using this
    rw [hasFDerivAt_iff_hasDerivAt] at hcomp
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using hcomp
  have hF_int : Integrable (fun z : G => Φ (z, y₀)) (volume : Measure G) := hint
  have hF_meas : ∀ᶠ x in 𝓝 y₀, AEStronglyMeasurable (fun z : G => Φ (z, x))
      (volume : Measure G) :=
    Filter.Eventually.of_forall fun x =>
      (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hmap : Continuous (fun z : G => ((z, y₀), ((0 : G), (1 : ℝ)))) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hfderiv_cont : Continuous (fun z : G => fderiv ℝ Φ (z, y₀) (0, 1)) :=
    Continuous.comp (g := fun p : (G × ℝ) × (G × ℝ) => (fderiv ℝ Φ p.1) p.2)
      (f := fun z : G => ((z, y₀), ((0 : G), (1 : ℝ)))) (hΦ.continuous_fderiv_apply h1) hmap
  have hF'_meas : AEStronglyMeasurable (fun z : G => fderiv ℝ Φ (z, y₀) (0, 1))
      (volume : Measure G) := hfderiv_cont.aestronglyMeasurable
  have h_bound : ∀ᵐ a ∂(volume : Measure G), ∀ x ∈ Set.Ioo (y₀ - 1) (y₀ + 1),
      ‖fderiv ℝ Φ (a, x) (0, 1)‖ ≤ bound a :=
    Filter.Eventually.of_forall fun a => fun x hx => hdom a x hx
  have h_diff : ∀ᵐ a ∂(volume : Measure G), ∀ x ∈ Set.Ioo (y₀ - 1) (y₀ + 1),
      HasDerivAt (fun y : ℝ => Φ (a, y)) (fderiv ℝ Φ (a, x) (0, 1)) x :=
    Filter.Eventually.of_forall fun a => fun x _ => hdiff a x
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure G)) (x₀ := y₀) (s := Set.Ioo (y₀ - 1) (y₀ + 1))
    (F := fun y z => Φ (z, y))
    (F' := fun y z => fderiv ℝ Φ (z, y) (0, 1))
    (bound := bound)
    (Ioo_mem_nhds (by linarith) (by linarith))
    hF_meas hF_int hF'_meas h_bound hbound h_diff
  simpa using hkey.2

end Commons.Analysis.Calculus