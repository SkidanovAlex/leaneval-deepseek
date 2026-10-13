import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Interval Topology

namespace Work.FTS.EllipticEst.remov.coerc

/-- If `Φ` has derivative `ψ` at every point of `(0, L)` and `ψ` is integrable on `[0, L]`,
then `Φ` has finite limits at both ends `0⁺` and `L⁻`.

This is the elementary "improper integral converges ⟹ primitive has endpoint limits" fact:
fix `c = L/2`; then on `(0, L)` the fundamental theorem of calculus gives
`Φ θ = Φ c + ∫_c^θ ψ`, and the primitive `θ ↦ ∫_c^θ ψ` is continuous on the closed halves
`[0, c]` and `[c, L]` (`intervalIntegral.continuousOn_primitive_interval`), hence has the
required one-sided limits. -/
theorem hasDerivAt_tendsto_at_ends {Φ ψ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hder : ∀ θ ∈ Set.Ioo 0 L, HasDerivAt Φ (ψ θ) θ)
    (hint : MeasureTheory.IntegrableOn ψ (Set.Icc 0 L)) :
    (∃ β, Filter.Tendsto Φ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds β)) ∧
      (∃ γ, Filter.Tendsto Φ (nhdsWithin L (Set.Iio L)) (nhds γ)) := by
  -- the middle point
  set c : ℝ := L / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hcL : c < L := by rw [hc]; linarith
  -- the fundamental theorem of calculus on `(0, L)`
  have hrel : ∀ θ ∈ Ioo (0 : ℝ) L, Φ θ = Φ c + ∫ x in c..θ, ψ x := by
    intro θ hθ
    have hder' : ∀ x ∈ uIcc c θ, HasDerivAt Φ (ψ x) x := by
      intro x hx
      simp only [uIcc, mem_Icc] at hx
      exact hder x ⟨lt_of_lt_of_le (lt_min hc0 hθ.1) hx.1,
        lt_of_le_of_lt hx.2 (max_lt hcL hθ.2)⟩
    have hsub : uIcc c θ ⊆ Icc 0 L := by
      intro x hx
      simp only [uIcc, mem_Icc] at hx
      exact ⟨le_of_lt (lt_of_lt_of_le (lt_min hc0 hθ.1) hx.1),
        le_of_lt (lt_of_le_of_lt hx.2 (max_lt hcL hθ.2))⟩
    have hii : IntervalIntegrable ψ volume c θ := (hint.mono_set hsub).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder' hii
    linarith [hftc]
  -- continuity of the primitive on each half
  have hcont0 : ContinuousOn (fun θ => ∫ x in c..θ, ψ x) (Icc 0 c) := by
    have hI : IntegrableOn ψ [[c, 0]] volume := by
      rw [uIcc_of_ge hc0.le]
      exact hint.mono_set (Icc_subset_Icc le_rfl hcL.le)
    have h := intervalIntegral.continuousOn_primitive_interval (a := c) (b := 0) hI
    simpa [uIcc_of_ge hc0.le] using h
  have hcontL : ContinuousOn (fun θ => ∫ x in c..θ, ψ x) (Icc c L) := by
    have hI : IntegrableOn ψ [[c, L]] volume := by
      rw [uIcc_of_le hcL.le]
      exact hint.mono_set (Icc_subset_Icc hc0.le le_rfl)
    have h := intervalIntegral.continuousOn_primitive_interval (a := c) (b := L) hI
    simpa [uIcc_of_le hcL.le] using h
  -- the two halves are neighbourhoods of the corresponding endpoints
  have hmem0 : Icc (0 : ℝ) c ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio c, Iio_mem_nhds hc0, fun x hx => ?_⟩
    exact ⟨le_of_lt hx.2, le_of_lt hx.1⟩
  have hmemL : Icc c L ∈ 𝓝[<] L := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Ioi c, Ioi_mem_nhds hcL, fun x hx => ?_⟩
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- one-sided limits of the primitive
  have hleft : Tendsto (fun θ => ∫ x in c..θ, ψ x) (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in c..0, ψ x)) :=
    Filter.Tendsto.mono_left (hcont0.continuousWithinAt ⟨le_rfl, hc0.le⟩)
      (nhdsWithin_le_iff.mpr hmem0)
  have hright : Tendsto (fun θ => ∫ x in c..θ, ψ x) (𝓝[<] L) (𝓝 (∫ x in c..L, ψ x)) :=
    Filter.Tendsto.mono_left (hcontL.continuousWithinAt ⟨hcL.le, le_rfl⟩)
      (nhdsWithin_le_iff.mpr hmemL)
  -- `Φ` agrees with `Φ c + ∫_c^{·} ψ` near each endpoint
  have hev0 : Φ =ᶠ[𝓝[>] (0 : ℝ)] (fun θ => Φ c + ∫ x in c..θ, ψ x) :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT hc0) fun θ hθ =>
      hrel θ ⟨hθ.1, lt_trans hθ.2 hcL⟩
  have hevL : Φ =ᶠ[𝓝[<] L] (fun θ => Φ c + ∫ x in c..θ, ψ x) :=
    Filter.eventually_of_mem (Ioo_mem_nhdsLT hcL) fun θ hθ =>
      hrel θ ⟨lt_trans hc0 hθ.1, hθ.2⟩
  exact ⟨⟨Φ c + ∫ x in c..0, ψ x, (hleft.const_add (Φ c)).congr' hev0.symm⟩,
    ⟨Φ c + ∫ x in c..L, ψ x, (hright.const_add (Φ c)).congr' hevL.symm⟩⟩

end Work.FTS.EllipticEst.remov.coerc
