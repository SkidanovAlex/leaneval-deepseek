import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Horn.Basins

/-- The union of the capturing pieces is forward invariant for `f`. -/
theorem mapsTo_iUnion {f : ℂ → ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hVmap : ∀ i, ∀ z ∈ V i, f z ∈ V i) :
    Set.MapsTo f (⋃ i, V i) (⋃ i, V i) := by
  intro y hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨i, hVmap i y hi⟩

/-- Iterating and then applying `f` is the same as applying `f` first. -/
theorem iterate_apply_comm {f : ℂ → ℂ} (k : ℕ) (y : ℂ) :
    f^[k] (f y) = f (f^[k] y) := by
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

/-- The parabolic basin is forward invariant, given the capture/reach data. -/
theorem basin_forward {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hVmap : ∀ i, ∀ z ∈ V i, f z ∈ V i)
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ n : ℕ, f^[n] z ∈ ⋃ i, V i)
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, f^[k] z ∈ D) ∧ f^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin f D) :
    ∀ z ∈ MandelDim.ParabolicBasin f D, f z ∈ MandelDim.ParabolicBasin f D := by
  intro z hz
  -- `z` eventually reaches the capturing union.
  obtain ⟨m, hm⟩ := hVcapture z hz
  -- the basin hypothesis gives a neighbourhood `U` of `z` all of whose iterates stay in `D`.
  obtain ⟨U, hUne, hUmap, -⟩ := hz
  have hzU : z ∈ U := mem_of_mem_nhds hUne
  have hfzD : f z ∈ D := by simpa using hUmap 1 hzU
  have hVinv := mapsTo_iUnion hVmap
  refine hVreach (f z) hfzD ⟨m, ?_, ?_⟩
  · intro k _
    rw [← Function.iterate_succ_apply]
    exact hUmap k.succ hzU
  · rw [iterate_apply_comm m z]
    exact hVinv hm

end Work.Horn.Basins
