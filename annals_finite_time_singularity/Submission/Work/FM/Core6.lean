/-
# The fundamental model: right-continuity of the tail integral `L₁₂^K(f)`
-/

import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.FM.Core2
import Submission.Work.FM.Core4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-- **Right-continuity of the tail integral**: if the density is integrable on `(ρ,∞)`,
then `σ ↦ L₁₂^K(f)(σ)` tends to `L₁₂^K(f)(ρ)` as `σ ↓ ρ`.  This discharges the
`hcontV` hypothesis of `L12_explicitSol` (via `hasDerivAt_L12`, which supplies the
density integrability). -/
theorem continuousWithinAt_L12 {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ}
    (hint : IntegrableOn (L12dens K f) (Ioi ρ)) :
    ContinuousWithinAt (fun σ => L12 K f σ) (Ici ρ) ρ := by
  have : (nhdsWithin ρ (Ici ρ)).IsCountablyGenerated := inferInstance
  have hmain : Tendsto (fun σ : ℝ => ∫ s in Ioi ρ, (Ioi σ).indicator (L12dens K f) s)
      (nhdsWithin ρ (Ici ρ)) (𝓝 (∫ s in Ioi ρ, (Ioi ρ).indicator (L12dens K f) s)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi ρ)) (l := nhdsWithin ρ (Ici ρ))
      (fun s => ‖L12dens K f s‖) ?_ ?_ hint.norm ?_
    · filter_upwards with σ
      exact hint.aestronglyMeasurable.indicator measurableSet_Ioi
    · refine Filter.Eventually.of_forall (fun σ => ?_)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      by_cases h : s ∈ Ioi σ
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]
        simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hmem : Iio s ∈ nhdsWithin ρ (Ici ρ) := by
        refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨Iio s, Iio_mem_nhds hs, ?_⟩
        intro x hx
        exact hx.1
      have hev : (fun _ : ℝ => (Ioi ρ).indicator (L12dens K f) s)
          =ᶠ[nhdsWithin ρ (Ici ρ)] fun σ : ℝ => (Ioi σ).indicator (L12dens K f) s := by
        filter_upwards [hmem, self_mem_nhdsWithin] with σ hσ1 _
        rw [Set.indicator_of_mem hs, Set.indicator_of_mem (Set.mem_Ioi.mpr hσ1)]
      exact tendsto_const_nhds.congr' hev
  have hlim_eq : (∫ s in Ioi ρ, (Ioi ρ).indicator (L12dens K f) s)
      = ∫ s in Ioi ρ, L12dens K f s := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    rw [Set.indicator_of_mem hs]
  rw [hlim_eq] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [L12]
  have hset : Ioi ρ ∩ Ioi σ = Ioi σ :=
    Set.inter_eq_right.mpr (fun x hx => (Set.mem_Ici.mp hσ).trans_lt hx)
  rw [setIntegral_indicator measurableSet_Ioi, hset]



/-- Convenience wrapper: `∂_ρ L₁₂^K(f) = -L12dens K f` from integrability of the
density on `(a,∞)` and its continuity on `(a,∞)`. -/
theorem hasDerivAt_L12_of_integrable {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {a ρ : ℝ}
    (hint : IntegrableOn (L12dens K f) (Ioi a))
    (hcont : ∀ s, a < s → ContinuousAt (L12dens K f) s) (ha : a < ρ) :
    HasDerivAt (fun σ => L12 K f σ) (-(L12dens K f ρ)) ρ :=
  hasDerivAt_L12 hint (hcont ρ ha) ha

/-- The hypotheses of `L12_explicitSol` in the form in which they arise from a
solution of the model: `V := L₁₂^K(f₀)` has radial derivative `-density`, is
right-continuous, and the modified density is integrable. -/
theorem L12_explicitSol_of_data {K : ℝ → ℝ} {f₀ : ℝ → ℝ → ℝ} {a ρ t : ℝ}
    (hint0 : IntegrableOn (L12dens K f₀) (Ioi a))
    (hcont0 : ∀ s, a < s → ContinuousAt (L12dens K f₀) s)
    (haρ : a < ρ)
    (hint : IntegrableOn (fun s => L12dens K f₀ s / (1 - t * L12 K f₀ s / 2) ^ 2) (Ioi ρ))
    (hden : ∀ s ∈ Ioi ρ, 1 - t * L12 K f₀ s / 2 ≠ 0)
    (hdenρ : 1 - t * L12 K f₀ ρ / 2 ≠ 0)
    (htend : Tendsto (fun σ => L12 K f₀ σ) atTop (𝓝 0)) :
    L12 K (fun s θ => f₀ s θ / (1 - t * L12 K f₀ s / 2) ^ 2) ρ
      = L12 K f₀ ρ / (1 - t * L12 K f₀ ρ / 2) := by
  refine L12_explicitSol (fun s hs => ?_) ?_ hint hden hdenρ htend
  · exact hasDerivAt_L12_of_integrable (hint0.mono_set fun x hx => haρ.trans hx)
      (fun s hs => hcont0 s (haρ.trans hs)) hs.out
  · exact continuousWithinAt_L12 (hint0.mono_set fun x hx => haρ.trans hx)

/-- **Well-definedness**: a bounded decaying profile has an integrable density, so
`L₁₂^K(f)(ρ) = ∫_ρ^∞ L12dens K f s ds` is a genuine Lebesgue integral. -/
theorem integrableOn_L12dens_of_decay {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {ρ C δ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hK : ∀ θ ∈ Icc 0 (Real.pi / 2), 0 ≤ K θ)
    (hKint : IntegrableOn K (Icc 0 (Real.pi / 2)))
    (hcont : ContinuousOn (L12dens K f) (Ioi ρ))
    (hf : ∀ s ∈ Ioi ρ, ∀ θ ∈ Icc 0 (Real.pi / 2), ‖f s θ‖ ≤ C * s ^ (-δ)) :
    IntegrableOn (L12dens K f) (Ioi ρ) := by
  have hKnn : 0 ≤ ∫ θ in Icc 0 (Real.pi / 2), K θ := setIntegral_nonneg measurableSet_Icc hK
  have hmaj : IntegrableOn
      (fun s : ℝ => (∫ θ in Icc 0 (Real.pi / 2), K θ) * C * s ^ (-δ - 1)) (Ioi ρ) := by
    have hpow : IntegrableOn (fun s : ℝ => s ^ (-δ - 1)) (Ioi ρ) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -δ - 1 < -1) hρ
    exact hpow.const_mul _
  refine Integrable.mono' hmaj (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := lt_trans hρ hs
  have hgi : IntegrableOn (fun θ => K θ * (C * s ^ (-δ) / s)) (Icc 0 (Real.pi / 2)) :=
    hKint.mul_const _
  have hbound : ‖L12dens K f s‖ ≤ (∫ θ in Icc 0 (Real.pi / 2), K θ) * (C * s ^ (-δ) / s) := by
    rw [L12dens]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hstep : ∫ θ in Icc 0 (Real.pi / 2), ‖K θ * f s θ / s‖
        ≤ ∫ θ in Icc 0 (Real.pi / 2), K θ * (C * s ^ (-δ) / s) := by
      refine setIntegral_mono_of_nonneg (fun θ _ => norm_nonneg (K θ * f s θ / s))
        (fun θ hθ => ?_) hgi
      have h1 := hf s hs θ hθ
      have h2 : 0 ≤ K θ / s := div_nonneg (hK θ hθ) hs0.le
      calc ‖K θ * f s θ / s‖ = (K θ / s) * ‖f s θ‖ := by
            simp only [norm_div, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hK θ hθ),
              abs_of_pos hs0]
            ring
        _ ≤ (K θ / s) * (C * s ^ (-δ)) := mul_le_mul_of_nonneg_left h1 h2
        _ = K θ * (C * s ^ (-δ) / s) := by ring
    have h2 : ∫ θ in Icc 0 (Real.pi / 2), K θ * (C * s ^ (-δ) / s)
        = (∫ θ in Icc 0 (Real.pi / 2), K θ) * (C * s ^ (-δ) / s) := integral_mul_const _ _
    exact hstep.trans h2.le
  refine hbound.trans (le_of_eq ?_)
  rw [show s ^ (-δ - 1) = s ^ (-δ) / s from Real.rpow_sub_one (ne_of_gt hs0) (-δ)]
  ring

end Work.FM
