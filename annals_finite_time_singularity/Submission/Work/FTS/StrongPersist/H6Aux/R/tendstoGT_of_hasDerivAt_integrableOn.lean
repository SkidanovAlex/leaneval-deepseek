import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.StrongPersist.H6Aux.R

/-- **Right-hand limit of a primitive.**  If `F` has derivative `v'` on `(0, c)`, `v'` is
interval integrable on `(0, c)` and `F` is continuous at `c`, then `F` has a right limit at
`0⁺`, given by `F c - ∫_0^c v'`.

Indeed, for `x ∈ (0, c)` the fundamental theorem of calculus on `[x, c]` gives
`F x = F c - ∫_x^c v'`, and `x ↦ ∫_x^c v'` is continuous on `[0, c]` (continuity of the
primitive of an interval integrable function), so it tends to `∫_0^c v'` as `x → 0⁺`. -/
theorem tendstoGT_of_hasDerivAt_integrableOn {F v' : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) c, HasDerivAt F (v' x) x)
    (hcont : ContinuousAt F c)
    (hint : IntervalIntegrable v' MeasureTheory.volume (0 : ℝ) c) :
    Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (F c - ∫ x in (0 : ℝ)..c, v' x)) := by
  -- `v'` is integrable on the *closed* interval `[0, c]`, hence the primitive `∫_x^c v'`
  -- is continuous on `[0, c]`.
  have hintIcc : IntegrableOn v' (uIcc (0 : ℝ) c) volume :=
    (intervalIntegrable_iff' (f := v') (a := (0 : ℝ)) (b := c)).mp hint
  have hpri : ContinuousOn (fun x => ∫ t in x..c, v' t) (uIcc (0 : ℝ) c) :=
    intervalIntegral.continuousOn_primitive_interval_left hintIcc
  -- hence `∫_x^c v' → ∫_0^c v'` as `x → 0⁺`, because `[0, c]` is a neighbourhood of `0`
  -- within `Ioi 0`.
  have hprim : Tendsto (fun x => ∫ t in x..c, v' t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ t in (0 : ℝ)..c, v' t)) := by
    have hmem : uIcc (0 : ℝ) c ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio c, Iio_mem_nhds hc, ?_⟩
      rintro x ⟨hxc, hx0⟩
      exact ⟨le_trans (min_le_left _ _) hx0.le, le_trans hxc.le (le_max_right _ _)⟩
    refine ((hpri.continuousWithinAt (left_mem_uIcc (a := (0 : ℝ)) (b := c))).tendsto).mono_left ?_
    exact nhdsWithin_le_iff.mpr hmem
  -- For `x ∈ (0, c)`, the FTC on `[x, c]` identifies `F x` with `F c - ∫_x^c v'`.
  have hF : (fun x => F c - ∫ t in x..c, v' t) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] F := by
    filter_upwards [Ioo_mem_nhdsGT hc] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hxc : x < c := hx.2
    have hint' : IntervalIntegrable v' volume x c := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxc.le]
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).mp hint).mono_set
        (Ioc_subset_Ioc hx0.le le_rfl)
    have ha : Tendsto F (𝓝[>] x) (𝓝 (F x)) :=
      ((hderiv x ⟨hx0, hxc⟩).continuousAt.tendsto).mono_left inf_le_left
    have hb : Tendsto F (𝓝[<] c) (𝓝 (F c)) := hcont.tendsto.mono_left inf_le_left
    have hEq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hxc
      (fun z hz => hderiv z ⟨hx0.trans hz.1, hz.2⟩) hint' ha hb
    linarith
  exact Filter.Tendsto.congr' hF (tendsto_const_nhds.sub hprim)

end Work.FTS.StrongPersist.H6Aux.R
