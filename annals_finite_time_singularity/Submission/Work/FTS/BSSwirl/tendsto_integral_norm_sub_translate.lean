/-
# Continuity of translation in `L¹(ℝ³; E)`

`Work.FTS.BSSwirl.tendsto_integral_norm_sub_translate`: for an integrable function
`A : R3 → E` with values in an arbitrary `NormedAddCommGroup`,

  `∫ z, ‖A (z + h) - A z‖  ⟶  0`   as `h → 0`,

i.e. the map `h ↦ A (· + h)` is continuous at `0` in `L¹`.  Nothing is assumed on `E` beyond
`NormedAddCommGroup` (in particular `E` need not be a normed `ℝ`-vector space), so the classical
"approximate `A` by continuous compactly supported functions and use uniform continuity" route is
not directly available; instead the argument is the abstract one, phrased in `L¹`:

* `A` defines an element `F` of `L¹(ℝ³; E)` (`MemLp.toLp`), and the integral we are interested in
  is exactly the `L¹`-distance of the translate of `F` by `h` from `F`
  (`Lp.norm_def` + `eLpNorm_one_eq_lintegral_enorm` + `ofReal_integral_norm_eq_lintegral_enorm`);
* the action `g ↦ g ∘ f` of a measure-preserving continuous `f` on `L¹` is continuous in the pair
  `(g, f)` (`MeasureTheory.Lp.compMeasurePreserving_continuous`, i.e.
  `Filter.Tendsto.compMeasurePreservingLp`), and the translations `z ↦ z + h` converge to the
  identity in the compact-open topology of `C(ℝ³, ℝ³)` (`tendsto_continuousMap_addRight` below,
  proved from `IsCompact.exists_cthickening_subset_open` and the characterisation
  `ContinuousMap.tendsto_nhds_compactOpen` of the compact-open topology).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric Filter Topology
open scoped Topology ENNReal NNReal

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The translations of `ℝ³` tend to the identity in the compact-open topology.**  Equivalently:
for every compact `K` and every open `U ⊇ K`, the translate `z ↦ z + h` maps `K` into `U` for all
`h` close enough to `0` (take the thickening of `K` inside `U`, which exists by compactness). -/
theorem tendsto_continuousMap_addRight :
    Filter.Tendsto (fun h : R3 => (⟨fun z => z + h, continuous_id.add continuous_const⟩ : C(R3, R3)))
      (nhds 0) (nhds (⟨id, continuous_id⟩ : C(R3, R3))) := by
  rw [ContinuousMap.tendsto_nhds_compactOpen]
  intro K hK U hU hKU
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with h hh x hx
  exact hεU (Metric.cthickening_mono (le_of_lt (by simpa [dist_eq_norm] using hh)) K
    (Metric.mem_cthickening_of_dist_le (x + h) x ‖h‖ K hx (by simp [dist_eq_norm])))

theorem tendsto_integral_norm_sub_translate {E : Type*} [NormedAddCommGroup E]
    (A : Work.FTS.BSSwirl.R3 → E) (hA : MeasureTheory.Integrable A MeasureTheory.volume) :
    Filter.Tendsto (fun h : Work.FTS.BSSwirl.R3 =>
      MeasureTheory.integral MeasureTheory.volume (fun z => ‖A (z + h) - A z‖))
      (nhds 0) (nhds 0) := by
  -- `A` as an element `F` of `L¹(ℝ³; E)`.
  have hmem : MemLp A (1 : ℝ≥0∞) volume := memLp_one_iff_integrable.mpr hA
  let F : Lp E (1 : ℝ≥0∞) volume := hmem.toLp A
  have hFcoe : (↑↑F : R3 → E) =ᵐ[volume] A := hmem.coeFn_toLp
  -- Continuity of the measure-preserving action on `L¹` at `(F, id)`, combined with the
  -- compact-open continuity of the translations.
  have hcont : Tendsto (fun h : R3 =>
      Lp.compMeasurePreserving (fun z => z + h) (measurePreserving_add_right volume h) F)
      (nhds 0) (nhds F) := by
    have h := Filter.Tendsto.compMeasurePreservingLp (μ := volume) (ν := volume)
      (f := fun _ : R3 => F) (f₀ := F)
      (g := fun h : R3 => (⟨fun z => z + h, continuous_id.add continuous_const⟩ : C(R3, R3)))
      (g₀ := (⟨id, continuous_id⟩ : C(R3, R3))) tendsto_const_nhds tendsto_continuousMap_addRight
      (fun h => measurePreserving_add_right volume h) (MeasurePreserving.id volume) (by norm_num)
    simpa using h
  -- Therefore the `L¹`-distance of the translate from `F` tends to `0`.
  have hnorm : Tendsto (fun h : R3 => ‖Lp.compMeasurePreserving (fun z => z + h)
      (measurePreserving_add_right volume h) F - F‖) (nhds 0) (nhds 0) := by
    have h2 : Tendsto (fun h : R3 => Lp.compMeasurePreserving (fun z => z + h)
        (measurePreserving_add_right volume h) F - F) (nhds 0) (nhds 0) := by
      have h3 := hcont.sub (tendsto_const_nhds (x := F))
      simpa using h3
    simpa using h2.norm
  -- That `L¹`-distance is precisely the integral appearing in the statement.
  have key : ∀ h : R3, ‖Lp.compMeasurePreserving (fun z => z + h)
      (measurePreserving_add_right volume h) F - F‖ = ∫ z, ‖A (z + h) - A z‖ := by
    intro h
    have hX : (↑↑(Lp.compMeasurePreserving (fun z => z + h) (measurePreserving_add_right volume h) F)
        : R3 → E) =ᵐ[volume] (fun z => A (z + h)) := by
      have h2 := Lp.coeFn_compMeasurePreserving F (measurePreserving_add_right volume h)
      have h3 := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hFcoe
      filter_upwards [h2, h3] with z Hz2 Hz3
      rw [Hz2, Hz3]
      rfl
    rw [Lp.norm_def]
    have hae : (↑↑(Lp.compMeasurePreserving (fun z => z + h)
          (measurePreserving_add_right volume h) F - F) : R3 → E)
        =ᵐ[volume] (fun z => A (z + h) - A z) :=
      (Lp.coeFn_sub (Lp.compMeasurePreserving (fun z => z + h)
        (measurePreserving_add_right volume h) F) F).trans (hX.sub hFcoe)
    have hint : Integrable (fun z => A (z + h) - A z) volume := (hA.comp_add_right h).sub hA
    rw [eLpNorm_congr_ae hae, eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hint]
    exact ENNReal.toReal_ofReal (integral_nonneg fun z => norm_nonneg _)
  exact (tendsto_congr' (Eventually.of_forall key)).mp hnorm

end

end Work.FTS.BSSwirl
