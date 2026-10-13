import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.VopTransfer

/-- Differentiation under the integral sign for the angular integral
`z ↦ ∫_θ^{π/2} cos s · W z s ds`, over a (non-degenerate) subinterval of `(0, π/2)`.

The proof is the standard dominated-differentiation theorem for interval integrals
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`): the integrand
`cos s * W z s` is jointly continuous on `V × (θ, π/2)`, its `z`-derivative
`cos s * W' z s` is uniformly bounded by the constant `C`, and `C ≥ 0` because `W` is
bounded by `C` and the strip is non-empty. -/
theorem derivUnderIntegralIoo {W W' : ℝ → ℝ → ℝ} {θ C : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {V : Set ℝ} (hV : IsOpen V) {z₀ : ℝ} (hz₀ : z₀ ∈ V)
    (hW : ContinuousOn (Function.uncurry W) (V ×ˢ Set.Ioo θ (π / 2)))
    (hW' : ContinuousOn (Function.uncurry W') (V ×ˢ Set.Ioo θ (π / 2)))
    (hWb : ∀ x ∈ V, ∀ s ∈ Set.Ioo θ (π / 2), |W x s| ≤ C)
    (hW'b : ∀ x ∈ V, ∀ s ∈ Set.Ioo θ (π / 2), |W' x s| ≤ C)
    (hd : ∀ s ∈ Set.Ioo θ (π / 2), ∀ x ∈ V, HasDerivAt (fun x' => W x' s) (W' x s) x) :
    HasDerivAt (fun z => ∫ s in θ..(π / 2), Real.cos s * W z s)
      (∫ s in θ..(π / 2), Real.cos s * W' z₀ s) z₀ := by
  have hle : θ ≤ π / 2 := le_of_lt hθ.2
  -- the constant `C` is nonnegative: `W` is bounded by `C` on the non-empty strip.
  have hC : 0 ≤ C := by
    have hs : (θ + π / 2) / 2 ∈ Set.Ioo θ (π / 2) :=
      ⟨by linarith [hθ.2], by linarith [hθ.2]⟩
    have h1 : |W z₀ ((θ + π / 2) / 2)| ≤ C := hWb z₀ hz₀ _ hs
    have h2 : (0 : ℝ) ≤ |W z₀ ((θ + π / 2) / 2)| := abs_nonneg _
    linarith
  -- slices of a jointly continuous function are continuous on the open interval
  have hslice : ∀ (f : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry f) (V ×ˢ Set.Ioo θ (π / 2)) →
      ∀ x ∈ V, ContinuousOn (fun t => f x t) (Set.Ioo θ (π / 2)) := by
    intro f hf x hx
    have hg : Continuous fun t : ℝ => (x, t) := continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) (Set.Ioo θ (π / 2))
        (V ×ˢ Set.Ioo θ (π / 2)) := fun t ht => ⟨hx, ht⟩
    have hcomp := hf.comp hg.continuousOn hmaps
    have heq : (Function.uncurry f ∘ fun t : ℝ => (x, t)) = fun t => f x t := by
      funext t
      rfl
    rwa [heq] at hcomp
  -- the measure `volume.restrict (θ, π/2)` does not see the right endpoint
  have hμ : volume.restrict (Set.uIoc θ (π / 2)) = volume.restrict (Set.Ioo θ (π / 2)) := by
    rw [Set.uIoc_of_le hle]
    exact (MeasureTheory.restrict_Ioo_eq_restrict_Ioc).symm
  have hmeasIoo : ∀ (f : ℝ → ℝ → ℝ),
      ContinuousOn (Function.uncurry f) (V ×ˢ Set.Ioo θ (π / 2)) → ∀ x ∈ V,
      AEStronglyMeasurable (fun t => Real.cos t * f x t)
        (volume.restrict (Set.Ioo θ (π / 2))) := by
    intro f hf x hx
    exact (Real.continuous_cos.continuousOn.mul (hslice f hf x hx)).aestronglyMeasurable
      isOpen_Ioo.measurableSet
  have hF_meas : ∀ᶠ x in 𝓝 z₀, AEStronglyMeasurable (fun t => Real.cos t * W x t)
      (volume.restrict (Set.uIoc θ (π / 2))) := by
    filter_upwards [hV.mem_nhds hz₀] with x hx
    rw [hμ]
    exact hmeasIoo W hW x hx
  have hF'_meas : AEStronglyMeasurable (fun t => Real.cos t * W' z₀ t)
      (volume.restrict (Set.uIoc θ (π / 2))) := by
    rw [hμ]
    exact hmeasIoo W' hW' z₀ hz₀
  have hF_int : IntervalIntegrable (fun t => Real.cos t * W z₀ t) volume θ (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
    refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioo θ (π / 2)) ?_ ?_ C ?_
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    · exact hmeasIoo W hW z₀ hz₀
    · refine MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioo.measurableSet fun t ht => ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |Real.cos t| * |W z₀ t| ≤ 1 * C :=
            mul_le_mul (Real.abs_cos_le_one t) (hWb z₀ hz₀ t ht) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc θ (π / 2) → ∀ x ∈ V,
      ‖Real.cos t * W' x t‖ ≤ C :=
    Eventually.of_forall fun t ht x hx => by
      rw [Set.uIoc_of_le hle] at ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · subst h
        rw [Real.cos_pi_div_two, zero_mul, norm_zero]
        exact hC
      · rw [Real.norm_eq_abs, abs_mul]
        calc |Real.cos t| * |W' x t| ≤ 1 * C :=
              mul_le_mul (Real.abs_cos_le_one t) (hW'b x hx t ⟨ht.1, h⟩) (abs_nonneg _)
                zero_le_one
          _ = C := one_mul C
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc θ (π / 2) → ∀ x ∈ V,
      HasDerivAt (fun x' => Real.cos t * W x' t) (Real.cos t * W' x t) x :=
    Eventually.of_forall fun t ht x hx => by
      rw [Set.uIoc_of_le hle] at ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · subst h
        have hfun : (fun x' : ℝ => Real.cos (π / 2) * W x' (π / 2)) = fun _ : ℝ => 0 := by
          funext x'
          rw [Real.cos_pi_div_two, zero_mul]
        rw [hfun, show Real.cos (π / 2) * W' x (π / 2) = 0 by
          rw [Real.cos_pi_div_two, zero_mul]]
        exact hasDerivAt_const x 0
      · exact (hd t ⟨ht.1, h⟩ x hx).const_mul (Real.cos t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := ℝ) (a := θ) (b := π / 2) (bound := fun _ => C)
    (F := fun z s => Real.cos s * W z s) (F' := fun z s => Real.cos s * W' z s)
    (x₀ := z₀) (s := V)
    (hV.mem_nhds hz₀) hF_meas hF_int hF'_meas hbound intervalIntegrable_const hdiff).2

end Work.FTS_EllLimOK.VopTransfer
