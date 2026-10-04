import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- If `F` is positive on a nonempty compact set `s` and continuous on an open neighbourhood
`O` of `s`, then `F` stays positive on a closed thickening of `s`. -/
theorem cthickening_pos_of_isCompact
    {X : Type*} [PseudoMetricSpace X] {F : X → ℝ} {s : Set X}
    (hs : IsCompact s) (hne : s.Nonempty) {O : Set X} (hO : IsOpen O) (hsub : s ⊆ O)
    (hFc : ContinuousOn F O) (hpos : ∀ x ∈ s, 0 < F x) :
    ∃ δ > 0, ∀ x ∈ Metric.cthickening δ s, 0 < F x := by
  -- The set where `F` is positive inside `O` is open in `X` (as `O` itself is open).
  have hAopen : IsOpen (O ∩ F ⁻¹' Set.Ioi 0) :=
    hFc.isOpen_inter_preimage hO isOpen_Ioi
  have hsubA : s ⊆ O ∩ F ⁻¹' Set.Ioi 0 := fun x hx => ⟨hsub hx, hpos x hx⟩
  -- A compact set contained in an open set has a closed thickening contained in it.
  obtain ⟨δ, hδpos, hδsub⟩ := hs.exists_cthickening_subset_open hAopen hsubA
  exact ⟨δ, hδpos, fun x hx => (hδsub hx).2⟩

end Work.Diff.EXT
