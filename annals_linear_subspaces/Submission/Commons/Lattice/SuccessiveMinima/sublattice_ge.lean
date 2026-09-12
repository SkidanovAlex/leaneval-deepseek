import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic

namespace Commons.Lattice.SuccessiveMinima

/-- The defining sets of successive minima are monotone with respect to lattice inclusion:
if `L₁ ≤ L₂`, any radius admitting `i` independent points of `L₁` admits `i` independent
points of `L₂` (the very same points, viewed in `L₂`). -/
lemma successiveMinimumSet_subset_of_le {E : Type*} [NormedAddCommGroup E]
    (L₁ L₂ : Submodule ℤ E) (hle : L₁ ≤ L₂) (i : ℕ) :
    successiveMinimumSet L₁ i ⊆ successiveMinimumSet L₂ i := by
  intro r hr
  rcases hr with ⟨hr0, f, hlin, hnorm⟩
  let g : Fin i → L₂ := fun j => ⟨(f j : E), hle (f j).2⟩
  have hg : (fun j : Fin i => (g j : E)) = fun j : Fin i => (f j : E) := by
    ext j
    rfl
  refine ⟨hr0, g, ?_, ?_⟩
  · rw [hg]
    exact hlin
  · intro j
    simpa [g] using hnorm j

theorem sublattice_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L₁ L₂ : Submodule ℤ E) (hle : L₁ ≤ L₂) (i : ℕ)
    (hS : (successiveMinimumSet L₁ i).Nonempty) :
    successiveMinimum L₂ i ≤ successiveMinimum L₁ i := by
  unfold successiveMinimum
  exact csInf_le_csInf (bddBelow_successiveMinimumSet L₂ i) hS
    (successiveMinimumSet_subset_of_le L₁ L₂ hle i)

end Commons.Lattice.SuccessiveMinima
