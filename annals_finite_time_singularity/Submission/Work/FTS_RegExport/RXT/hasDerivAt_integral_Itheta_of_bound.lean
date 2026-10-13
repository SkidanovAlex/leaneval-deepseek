import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

/-- **Differentiation under the angular integral sign, with an a.e. bound on the derivative.**
If, a.e. in `θ ∈ (0,π/2)`, every `z`-slice `z' ↦ G z' θ * φ θ` is differentiable on the
neighbourhood `(z₀/2, 2 z₀)` of `z₀ > 0` with derivative `G' z θ * φ θ`, and if `‖G' z θ‖`
is a.e. bounded by the constant `K ≥ 0` there, then (given measurability and integrability of
the slice at `z₀`) the parametric integral `z ↦ ∫_θ G z θ * φ θ` is differentiable at `z₀`
with derivative `∫_θ G' z₀ θ * φ θ`.

This is `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the dominating function
`θ ↦ K * M`, where `M` bounds `‖φ‖` on the compact interval `Iθ` (so the bound is integrable
for the finite measure `volume.restrict (Ioo 0 (π/2))`). -/

theorem hasDerivAt_integral_Itheta_of_bound {G G' : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {z₀ K : ℝ}
    (hz₀ : 0 < z₀) (hK : 0 ≤ K) (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hG_meas : ∀ᶠ z in nhds z₀,
      MeasureTheory.AEStronglyMeasurable (fun θ => G z θ * φ θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hG_int : MeasureTheory.Integrable (fun θ => G z₀ θ * φ θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hG'_meas : MeasureTheory.AEStronglyMeasurable (fun θ => G' z₀ θ * φ θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀), ‖G' z θ‖ ≤ K)
    (hderiv : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀),
        HasDerivAt (fun z' => G z' θ * φ θ) (G' z θ * φ θ) z) :
    HasDerivAt (fun z => ∫ θ, G z θ * φ θ
        ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
      (∫ θ, G' z₀ θ * φ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) z₀ := by
  -- `‖φ‖` is bounded on the compact interval `Iθ` by some constant `M ≥ 0`
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [Work.Spaces.Iθ] using hφ)
  have hMn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
  have hphi_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))), ‖φ θ‖ ≤ M := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun θ hθ => hM θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- combine the two a.e. bounds: `‖G' z θ * φ θ‖ ≤ K * M`
  have hbound' : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀), ‖G' z θ * φ θ‖ ≤ K * M := by
    filter_upwards [hbound, hphi_ae] with θ hb hφb z hz
    rw [norm_mul]
    exact mul_le_mul (hb z hz) hφb (norm_nonneg _) hK
  -- the constant bound is integrable for the finite restricted measure
  have hfin : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))
    (F := fun z θ => G z θ * φ θ) (F' := fun z θ => G' z θ * φ θ)
    (bound := fun _ => K * M) (x₀ := z₀) (s := Set.Ioo (z₀ / 2) (2 * z₀))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) hG_meas hG_int hG'_meas hbound'
    (MeasureTheory.integrable_const_iff.mpr (Or.inr hfin)) hderiv
  exact key.2

end Work.FTS_RegExport.RXT
