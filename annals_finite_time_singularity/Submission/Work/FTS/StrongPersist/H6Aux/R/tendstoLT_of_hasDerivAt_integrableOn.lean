import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

open MeasureTheory Set Filter
open scoped Topology

/-- If `F` has derivative `v'` on the open interval `(a, b)`, is continuous at `a`, and `v'` is
interval integrable on `a..b`, then `F` has the left limit `F a + ∫ x in a..b, v' x` at `b`.

This is the "indefinite integral is continuous" form of the fundamental theorem of calculus: for
`x ∈ (a, b)` the (second) FTC gives `F x = F a + ∫ y in a..x, v' y`, and `x ↦ ∫ y in a..x, v' y`
is absolutely continuous (hence continuous) on `[a, b]`, so it tends at `b⁻` to
`∫ y in a..b, v' y`. -/
theorem tendstoLT_of_hasDerivAt_integrableOn {F v' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt F (v' x) x)
    (hcont : ContinuousAt F a)
    (hint : IntervalIntegrable v' MeasureTheory.volume a b) :
    Filter.Tendsto F (nhdsWithin b (Set.Iio b))
      (nhds (F a + ∫ x in a..b, v' x)) := by
  -- The second fundamental theorem of calculus on each closed subinterval `[a, x]`, `x < b`.
  have hFTC : ∀ x ∈ Ioo a b, F x = F a + ∫ y in a..x, v' y := by
    intro x hx
    have hcont' : ContinuousOn F (Icc a x) := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with hya | hya
      · subst hya; exact hcont.continuousWithinAt
      · exact ((hderiv y ⟨hya, lt_of_le_of_lt hy.2 hx.2⟩).continuousAt).continuousWithinAt
    have hderiv' : ∀ y ∈ Ioo a x, HasDerivAt F (v' y) y :=
      fun y hy => hderiv y ⟨hy.1, lt_trans hy.2 hx.2⟩
    have hint' : IntervalIntegrable v' volume a x :=
      hint.mono_set (by
        rw [uIcc_of_le hx.1.le, uIcc_of_le hab.le]
        exact Icc_subset_Icc_right hx.2.le)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1.le hcont' hderiv' hint']
    ring
  -- The indefinite integral `x ↦ ∫ y in a..x, v' y` is continuous at `b`.
  have hAC : AbsolutelyContinuousOnInterval (fun x => ∫ y in a..x, v' y) a b :=
    hint.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by
      rw [uIcc_of_le hab.le]; exact ⟨le_rfl, hab.le⟩)
  have hg : Tendsto (fun x => ∫ y in a..x, v' y) (𝓝[Iio b] b) (𝓝 (∫ y in a..b, v' y)) := by
    have hcw : ContinuousWithinAt (fun x => ∫ y in a..x, v' y) (Icc a b) b := by
      have h := hAC.continuousOn
      rw [uIcc_of_le hab.le] at h
      exact h b ⟨hab.le, le_rfl⟩
    refine hcw.mono_left ?_
    rw [nhdsWithin_le_iff]
    refine mem_of_superset (inter_mem_nhdsWithin (Iio b) (Ici_mem_nhds hab)) ?_
    intro x hx
    exact ⟨hx.2, hx.1.le⟩
  -- Replace `F a + ∫ y in a..x, v' y` by `F x` eventually (`x > a`).
  refine Tendsto.congr' ?_ (hg.const_add (F a))
  filter_upwards [show Ioo a b ∈ 𝓝[Iio b] b from
      mem_of_superset (inter_mem_nhdsWithin (Iio b) (Ioi_mem_nhds hab))
        (fun x hx => ⟨hx.2, hx.1⟩)] with x hx
  exact (hFTC x hx).symm

end Work.FTS.StrongPersist.H6Aux.R
