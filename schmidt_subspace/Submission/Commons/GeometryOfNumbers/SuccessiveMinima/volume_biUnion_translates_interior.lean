import Mathlib.Analysis.Convex.Measure
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Order.CompletePartialOrder

namespace Commons.GeometryOfNumbers.SuccessiveMinima

open MeasureTheory Set
open scoped Pointwise

/-- For a convex set `A` in `ℝ^N` and a finite set `S` of translation vectors, the union of the
translates `z + A` has the same Lebesgue measure as the union of the translates of the interior
`z + interior A`.

Proof sketch: `A = interior A ∪ frontier A` and `frontier A` is null for convex `A`
(`Convex.addHaar_frontier`), so
`⋃_{z∈S} (z +ᵥ A) ⊆ (⋃_{z∈S} (z +ᵥ interior A)) ∪ (⋃_{z∈S} (z +ᵥ frontier A))`
with the second union null (`Finset.measure_biUnion_null` / `measure_iUnion_null_iff`); the
reverse inclusion is immediate by `measure_mono`. -/
theorem volume_biUnion_translates_interior {N : ℕ} {A : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    (S : Finset (Fin N → ℝ)) :
    volume (⋃ z ∈ S, (z +ᵥ A)) = volume (⋃ z ∈ S, (z +ᵥ interior A)) := by
  -- The union of the translates of the frontier is null: the frontier of a convex set is null
  -- and `volume` is translation invariant.
  have hfr : volume (⋃ z ∈ S, (z +ᵥ frontier A)) = 0 := by
    rw [show (⋃ z ∈ S, (z +ᵥ frontier A))
        = ⋃ z ∈ (S : Set (Fin N → ℝ)), (z +ᵥ frontier A) from rfl]
    rw [measure_biUnion_null_iff S.finite_toSet.countable]
    intro z _
    rw [measure_vadd]
    exact Convex.addHaar_frontier volume hA
  -- A set is contained in its interior together with its frontier.
  have hAsub : A ⊆ interior A ∪ frontier A :=
    subset_closure.trans (le_of_eq (closure_eq_interior_union_frontier A))
  -- Every translate of `A` is covered by the translate of the interior together with the
  -- translate of the frontier.
  have hsub : (⋃ z ∈ S, (z +ᵥ A)) ⊆
      (⋃ z ∈ S, (z +ᵥ interior A)) ∪ (⋃ z ∈ S, (z +ᵥ frontier A)) := by
    intro x hx
    simp only [mem_iUnion, mem_union, mem_vadd_set] at hx ⊢
    obtain ⟨z, hz, a, ha, rfl⟩ := hx
    rcases hAsub ha with ha' | ha'
    · exact Or.inl ⟨z, hz, a, ha', rfl⟩
    · exact Or.inr ⟨z, hz, a, ha', rfl⟩
  refine le_antisymm ?_ ?_
  · calc volume (⋃ z ∈ S, (z +ᵥ A))
        ≤ volume ((⋃ z ∈ S, (z +ᵥ interior A)) ∪ (⋃ z ∈ S, (z +ᵥ frontier A))) :=
          measure_mono hsub
      _ ≤ volume (⋃ z ∈ S, (z +ᵥ interior A)) + volume (⋃ z ∈ S, (z +ᵥ frontier A)) :=
          measure_union_le _ _
      _ = volume (⋃ z ∈ S, (z +ᵥ interior A)) := by rw [hfr, add_zero]
  · apply measure_mono
    intro x hx
    simp only [mem_iUnion, mem_vadd_set] at hx ⊢
    obtain ⟨z, hz, a, ha, rfl⟩ := hx
    exact ⟨z, hz, a, interior_subset ha, rfl⟩

end Commons.GeometryOfNumbers.SuccessiveMinima