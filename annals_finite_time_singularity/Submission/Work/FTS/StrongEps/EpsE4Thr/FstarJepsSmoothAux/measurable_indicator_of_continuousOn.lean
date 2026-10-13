import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-- The indicator of an open set, times a function which is continuous on that set, is Borel
measurable: on the open set `s` we may test measurability of `g` on open preimages (`s ∩ g ⁻¹' U`
is open by `ContinuousOn.isOpen_inter_preimage`), while off `s` the indicator is constantly `0`. -/
theorem measurable_indicator_of_continuousOn {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [BorelSpace α] {s : Set α} (hs : IsOpen s) {g : α → ℝ}
    (hg : ContinuousOn g s) : Measurable (Set.indicator s g) := by
  classical
  -- Borel measurability of a real-valued function may be checked on open preimages.
  refine measurable_of_isOpen fun U hU => ?_
  have hA : MeasurableSet (s ∩ g ⁻¹' U) := (hg.isOpen_inter_preimage hs hU).measurableSet
  by_cases h0 : (0 : ℝ) ∈ U
  · -- the fibre of `U` is `(s ∩ g ⁻¹' U) ∪ sᶜ`
    have hpre : (Set.indicator s g) ⁻¹' U = (s ∩ g ⁻¹' U) ∪ sᶜ := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx, h0]
    rw [hpre]
    exact hA.union hs.measurableSet.compl
  · -- the fibre of `U` is `s ∩ g ⁻¹' U`
    have hpre : (Set.indicator s g) ⁻¹' U = s ∩ g ⁻¹' U := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx, h0]
    rw [hpre]
    exact hA

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
