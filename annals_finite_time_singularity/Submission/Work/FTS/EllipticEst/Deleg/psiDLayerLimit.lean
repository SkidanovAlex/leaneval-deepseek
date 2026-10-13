/-
# `psiDLayerLimit` — the two angular layers of the truncation carry no mass

This module proves `Work.FTS.EllipticEst.Deleg.psiDLayerLimit`, the `δ → 0⁺` limit of the
`z`-integral of the two angular layer pieces cut out by the bump `psiD δ`:

```
Tendsto (fun δ => (∫ z, c z * (∫ θ in (0,δ), G z θ)) + (∫ z, c z * (∫ θ in (π/2-δ,π/2), G z θ)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0)
```

for a jointly measurable `G`, nonnegative on the strip `(0, π/2)`, whose `θ`-slices are
integrable for a.e. `z` and whose `θ`-mass is `|c|`-dominated in the sense that
`z ↦ |c z| ∫ θ, |G z θ|` is integrable on `(0,∞)`.

It is the two-layer companion of `Deleg.psiDIntegralLimit` and the `c`-weighted companion of
`HonGaps.psiCutZLayerLimit`.

The proof is dominated convergence in `z` with respect to `μ = volume.restrict (Ioi 0)`:
* for each `δ` the integrand `z ↦ c z * (∫ θ in S δ, G z θ)` is a.e. strongly measurable:
  the inner integral is obtained from the joint measurability hypothesis by Fubini
  (`AEStronglyMeasurable.integral_prod_right'`) on `μ.prod ν`, `ν = volume.restrict (0,π/2)`;
* domination on the a.e. set where the `θ`-slice of `G` is integrable: the layer integral is
  `≥ 0` and `≤ ∫ θ, |G z θ|` (monotonicity of the integral for the pointwise bound
  `S δ.indicator (G z) ≤ |G z|`), and the dominating function is `z ↦ |c z| ∫ θ, |G z θ|`,
  integrable by hypothesis;
* pointwise convergence for a.e. `z`: each layer mass is a set integral of the fixed integrable
  function `θ ↦ G z θ` over a set whose `ν`-measure tends to `0`
  (`Integrable.tendsto_setIntegral_nhds_zero`).

The two actual layers `(0, δ)` and `(π/2 - δ, π/2)` are sandwiched as
`(0, min δ (π/2))` and `(max (π/2 - δ) 0, π/2)`, which are *always* contained in `(0, π/2)` —
this makes the domination and the measurability statements unconditional (no `∀ᶠ δ` inside).
The two formulations agree for `δ < π/2`.

The main workhorse `layerTendstoZero` is stated for an *arbitrary* family `S : ℝ → Set ℝ` of
layers contained in `(0, π/2)` whose `ν`-measure tends to `0`.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts
import Submission.Work.FTS.EllipticEst.HonGaps.psiCutZLayerLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Deleg

/-! ## The general layer limit -/

/-- **Dominated convergence for a family of angular layers.**  Let `c` be a.e. strongly
measurable on `(0,∞)`, let `G` be jointly measurable on `(0,∞) × (0,π/2)` with a.e. integrable
`θ`-slices and nonnegative on the strip, and let `z ↦ |c z| ∫_θ |G z θ|` be integrable.  If
`S δ ⊆ (0, π/2)` are measurable layers whose `θ`-measure tends to `0` as `δ → 0⁺`, then the
`z`-integral of `c · (θ-mass of `G` on `S δ`)` tends to `0`. -/
theorem layerTendstoZero {c : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {S : ℝ → Set ℝ}
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))))
    (hjoint : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2)))))
    (hGz : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.Integrable (fun θ => G z θ) (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2))))
    (hGnn : ∀ z θ, θ ∈ Set.Ioo 0 (Real.pi/2) → 0 ≤ G z θ)
    (hdom : MeasureTheory.Integrable (fun z => |c z| * ∫ θ, |G z θ| ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2))))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hSmeas : ∀ δ, MeasurableSet (S δ))
    (hSsub : ∀ δ, S δ ⊆ Set.Ioo 0 (Real.pi/2))
    (hSν : Tendsto (fun δ => (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2))) (S δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun δ => ∫ z, c z * (∫ θ in S δ, G z θ) ∂(MeasureTheory.volume.restrict (Set.Ioi 0)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin 0 (Ioi 0) with hl
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  set ν : Measure ℝ := volume.restrict (Ioo 0 (Real.pi/2)) with hν
  have hjoint' : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2) (μ.prod ν) := by
    rw [hμ, hν]; exact hjoint
  have hνrestr : ∀ δ, ν.restrict (S δ) = volume.restrict (S δ) := fun δ => by
    rw [hν, Measure.restrict_restrict_of_subset (hSsub δ)]
  -- (1) a.e. strong measurability of the integrands, uniformly in `δ`
  have hmeas : ∀ᶠ δ in l, AEStronglyMeasurable (fun z => c z * (∫ θ, (S δ).indicator (G z) θ ∂ν)) μ := by
    refine Eventually.of_forall fun δ => ?_
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ S δ} := (hSmeas δ).preimage measurable_snd
    have h1 : AEStronglyMeasurable ({p : ℝ × ℝ | p.2 ∈ S δ}.indicator
        (fun p : ℝ × ℝ => G p.1 p.2)) (μ.prod ν) := hjoint'.indicator hset
    have h2 : AEStronglyMeasurable (fun z => ∫ θ,
        ({p : ℝ × ℝ | p.2 ∈ S δ}.indicator (fun p : ℝ × ℝ => G p.1 p.2)) (z, θ) ∂ν) μ :=
      h1.integral_prod_right'
    have h3 : AEStronglyMeasurable (fun z => ∫ θ, (S δ).indicator (G z) θ ∂ν) μ := by
      refine h2.congr (Eventually.of_forall fun z => ?_)
      apply integral_congr_ae
      filter_upwards with θ
      by_cases h : θ ∈ S δ
      · rw [Set.indicator_of_mem (show (z, θ) ∈ {p : ℝ × ℝ | p.2 ∈ S δ} from h)
            (fun p : ℝ × ℝ => G p.1 p.2), Set.indicator_of_mem h (G z)]
      · rw [Set.indicator_of_notMem (show (z, θ) ∉ {p : ℝ × ℝ | p.2 ∈ S δ} from h)
            (fun p : ℝ × ℝ => G p.1 p.2), Set.indicator_of_notMem h (G z)]
    exact hc.mul h3
  -- (2) domination by the weighted full `θ`-mass
  have hbound : ∀ᶠ δ in l, ∀ᵐ z ∂μ,
      ‖c z * (∫ θ, (S δ).indicator (G z) θ ∂ν)‖ ≤ |c z| * ∫ θ, |G z θ| ∂ν := by
    refine Eventually.of_forall fun δ => ?_
    filter_upwards [hGz] with z hz
    have hnn : 0 ≤ ∫ θ, (S δ).indicator (G z) θ ∂ν :=
      integral_nonneg (Set.indicator_nonneg fun θ hθ => hGnn z θ (hSsub δ hθ))
    have hle : ∫ θ, (S δ).indicator (G z) θ ∂ν ≤ ∫ θ, |G z θ| ∂ν :=
      integral_mono_ae (hz.indicator (hSmeas δ)) hz.norm
        (Eventually.of_forall fun θ => by
          by_cases h : θ ∈ S δ
          · rw [Set.indicator_of_mem h]; exact le_abs_self _
          · rw [Set.indicator_of_notMem h]; exact abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  -- (3) pointwise convergence for a.e. `z`
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun δ => c z * (∫ θ, (S δ).indicator (G z) θ ∂ν)) l (nhds 0) := by
    filter_upwards [hGz] with z hz
    have h1 : Tendsto (fun δ => ∫ θ, (S δ).indicator (G z) θ ∂ν) l (nhds 0) :=
      Tendsto.congr' (Eventually.of_forall fun δ =>
        (integral_indicator (hSmeas δ) (f := G z) (μ := ν)).symm)
        (hz.tendsto_setIntegral_nhds_zero (l := l) (s := S) hSν)
    have h2 : Tendsto (fun δ => c z * (∫ θ, (S δ).indicator (G z) θ ∂ν)) l (nhds (c z * 0)) :=
      tendsto_const_nhds.mul h1
    simpa using h2
  have hBd : Integrable (fun z => |c z| * ∫ θ, |G z θ| ∂ν) μ := hdom
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := l) (F := fun δ z => c z * (∫ θ, (S δ).indicator (G z) θ ∂ν))
    (f := fun _ => (0:ℝ)) (fun z => |c z| * ∫ θ, |G z θ| ∂ν) hmeas hbound hBd hlim
  have hmain' : Tendsto (fun δ => ∫ z, c z * (∫ θ, (S δ).indicator (G z) θ ∂ν) ∂μ) l (nhds 0) := by
    simpa using hmain
  -- back to the honest set integrals, with respect to the unrestricted measure
  refine Tendsto.congr' (Eventually.of_forall fun δ => ?_) hmain'
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  rw [integral_indicator (hSmeas δ) (f := G z) (μ := ν), hνrestr δ]

/-! ## The measures of the two layers tend to zero -/

/-- The `(0, π/2)`-measure of the lower layer `(0, min δ (π/2))` tends to `0` as `δ → 0⁺`. -/
theorem tendsto_nu_min :
    Tendsto (fun δ : ℝ => (volume.restrict (Ioo 0 (Real.pi/2))) (Ioo 0 (min δ (Real.pi/2))))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin 0 (Ioi 0) with hl
  set ν : Measure ℝ := volume.restrict (Ioo 0 (Real.pi/2)) with hν
  have hev : (fun δ : ℝ => ν (Ioo 0 (min δ (Real.pi/2))))
      = fun δ : ℝ => ENNReal.ofReal (min δ (Real.pi/2)) := by
    funext δ
    have hsub : Ioo 0 (min δ (Real.pi/2)) ⊆ Ioo 0 (Real.pi/2) :=
      fun θ hθ => ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩
    rw [hν, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left hsub, Real.volume_Ioo, sub_zero]
  have hmin : Tendsto (fun δ : ℝ => min δ (Real.pi/2)) l (nhds 0) := by
    have h : Tendsto (fun δ : ℝ => min δ (Real.pi/2)) l (nhds (min 0 (Real.pi/2))) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).min tendsto_const_nhds
    rwa [min_eq_left (by linarith [Real.pi_pos])] at h
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (min δ (Real.pi/2))) l (nhds 0) := by
    have h3 : Tendsto (fun δ : ℝ => ENNReal.ofReal (min δ (Real.pi/2))) l
        (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp hmin
    simpa using h3
  exact Tendsto.congr' (Filter.EventuallyEq.of_eq hev.symm) h2

/-- The `(0, π/2)`-measure of the upper layer `(max (π/2 - δ) 0, π/2)` tends to `0` as `δ → 0⁺`. -/
theorem tendsto_nu_max :
    Tendsto (fun δ : ℝ => (volume.restrict (Ioo 0 (Real.pi/2))) (Ioo (max (Real.pi/2 - δ) 0) (Real.pi/2)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin 0 (Ioi 0) with hl
  set ν : Measure ℝ := volume.restrict (Ioo 0 (Real.pi/2)) with hν
  have hlt : ∀ᶠ δ : ℝ in l, δ < Real.pi/2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hev : (fun δ : ℝ => ν (Ioo (max (Real.pi/2 - δ) 0) (Real.pi/2)))
      =ᶠ[l] fun δ : ℝ => ENNReal.ofReal δ := by
    filter_upwards [hlt] with δ hδ
    have hsub : Ioo (Real.pi/2 - δ) (Real.pi/2) ⊆ Ioo 0 (Real.pi/2) :=
      fun θ hθ => ⟨lt_of_le_of_lt (by linarith : (0:ℝ) ≤ Real.pi/2 - δ) hθ.1, hθ.2⟩
    rw [hν, Measure.restrict_apply measurableSet_Ioo, max_eq_left (by linarith),
      Set.inter_eq_self_of_subset_left hsub, Real.volume_Ioo,
      show Real.pi/2 - (Real.pi/2 - δ) = δ from by ring]
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) l (nhds 0) := by
    have h3 : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) l (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_id.mono_left nhdsWithin_le_nhds)
    simpa using h3
  exact Tendsto.congr' hev.symm h2

/-! ## The requested lemma -/

theorem psiDLayerLimit {c : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hc : MeasureTheory.AEStronglyMeasurable c
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hjoint : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))))
    (hGz : Filter.Eventually (fun z => MeasureTheory.Integrable (fun θ => G z θ)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))))
    (hGnn : ∀ z θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → 0 ≤ G z θ)
    (hdom : MeasureTheory.Integrable (fun z => |c z| *
        ∫ θ, |G z θ| ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    Filter.Tendsto (fun δ : ℝ =>
        (∫ z, c z * (∫ θ in Set.Ioo (0 : ℝ) δ, G z θ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
      + (∫ z, c z * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), G z θ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin 0 (Ioi 0) with hl
  have hlt : ∀ᶠ δ : ℝ in l, δ < Real.pi/2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hlo : Tendsto (fun δ : ℝ => ∫ z, c z * (∫ θ in Set.Ioo 0 (min δ (Real.pi/2)), G z θ)
      ∂(volume.restrict (Set.Ioi 0))) l (nhds 0) :=
    layerTendstoZero (S := fun δ => Set.Ioo 0 (min δ (Real.pi/2))) hc hjoint hGz hGnn hdom
      (fun δ => measurableSet_Ioo)
      (fun δ θ hθ => ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩) tendsto_nu_min
  have hlo' : Tendsto (fun δ : ℝ => ∫ z, c z * (∫ θ in Set.Ioo 0 δ, G z θ)
      ∂(volume.restrict (Set.Ioi 0))) l (nhds 0) := by
    refine Tendsto.congr' ?_ hlo
    filter_upwards [hlt] with δ hδ
    rw [min_eq_left (le_of_lt hδ)]
  have hhi : Tendsto (fun δ : ℝ => ∫ z, c z * (∫ θ in Set.Ioo (max (Real.pi/2 - δ) 0) (Real.pi/2), G z θ)
      ∂(volume.restrict (Set.Ioi 0))) l (nhds 0) :=
    layerTendstoZero (S := fun δ => Set.Ioo (max (Real.pi/2 - δ) 0) (Real.pi/2)) hc hjoint hGz hGnn hdom
      (fun δ => measurableSet_Ioo)
      (fun δ θ hθ => ⟨lt_of_le_of_lt (le_max_right _ _) hθ.1, hθ.2⟩) tendsto_nu_max
  have hhi' : Tendsto (fun δ : ℝ => ∫ z, c z * (∫ θ in Set.Ioo (Real.pi/2 - δ) (Real.pi/2), G z θ)
      ∂(volume.restrict (Set.Ioi 0))) l (nhds 0) := by
    refine Tendsto.congr' ?_ hhi
    filter_upwards [hlt] with δ hδ
    rw [max_eq_left (by linarith : (0:ℝ) ≤ Real.pi/2 - δ)]
  have hsum := hlo'.add hhi'
  simpa [l] using hsum

end Work.FTS.EllipticEst.Deleg
