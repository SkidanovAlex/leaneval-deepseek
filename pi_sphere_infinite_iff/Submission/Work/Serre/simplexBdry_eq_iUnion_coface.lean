import Mathlib
import Submission.Work.Serre.E0SimplexDefs
import Submission.Work.Serre.E0SbdryMatching
import Submission.Work.RatHurewicz.Bridge.Defs

namespace Work.Serre

/-- The simplicial boundary `∂Δ^{n+1}` of the standard `(n+1)`-simplex is the union of the images
of its `n`-dimensional faces, i.e. of the cofaces `Δⁿ → Δⁿ⁺¹`. -/
theorem simplexBdry_eq_iUnion_coface (n : ℕ) :
    Work.Serre.simplexBdry (n + 1) =
      (⋃ i : Fin (n + 2), Set.range (Work.RatHurewicz.Bridge.coface n i)) := by
  ext z
  constructor
  · rintro ⟨i, hi⟩
    exact Set.mem_iUnion.mpr
      ⟨i, ⟨⟨uncoface n i z, uncoface_mem n i z hi⟩, coface_uncoface n i z hi⟩⟩
  · intro hz
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hz
    exact ⟨i, by rw [← hy]; exact Work.RatHurewicz.Bridge.coface_apply_self n i y⟩

end Work.Serre
