import Mathlib

namespace Work.WilE9G.Sard

theorem glueNull {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) (A : Set (Fin d → ℝ))
    (h : ∀ x ∈ A, ∃ V : Set (Fin d → ℝ), V ∈ nhds x ∧ MeasureTheory.volume (F '' (A ∩ V)) = 0) :
    MeasureTheory.volume (F '' A) = 0 := by
  classical
  -- For each `x ∈ A` choose a neighbourhood `g x` witnessing the hypothesis.
  choose g hg using fun x : A => h x.1 x.2
  -- Shrink `g x` to an open neighbourhood `U x` of `x` contained in `g x`.
  choose U hU using fun x : A => mem_nhds_iff.mp (hg x).1
  -- Second countability of `Fin d → ℝ` yields a countable subcover.
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U (fun x => (hU x).2.1)
  -- `A` is covered by the `U x`.
  have hAU : A ⊆ ⋃ x, U x := by
    intro a ha
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, (hU ⟨a, ha⟩).2.2⟩
  -- Hence `F '' A` is covered by countably many null sets.
  have hsub : F '' A ⊆ ⋃ x ∈ T, F '' (A ∩ g x) := by
    rintro y ⟨a, ha, rfl⟩
    have hau : a ∈ ⋃ x, U x := hAU ha
    rw [← hTU] at hau
    obtain ⟨x, hxT, hax⟩ := Set.mem_iUnion₂.mp hau
    exact Set.mem_iUnion₂.mpr ⟨x, hxT, a, ⟨ha, (hU x).1 hax⟩, rfl⟩
  refine MeasureTheory.measure_mono_null hsub ?_
  rw [MeasureTheory.measure_biUnion_null_iff hTc]
  intro x _
  exact (hg x).2

end Work.WilE9G.Sard
