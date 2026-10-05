import Mathlib
import Submission.Work.RPB.B1a.Maehara.Defs

set_option linter.style.haveILetI false

namespace Work.RPB.B1a.Maehara

open Set Metric Complex

/-- A point of the unbounded component of the complement of a closed set `K`, reached by a path
starting at `x` and staying in `Kᶜ`.

Since `RectC` is bounded, an unbounded subset of `Kᶜ` contains a point `y` outside `RectC`.  The
complement `Kᶜ` is open, so its connected components are the path components of the open subpace
`↥(Kᶜ)`: in particular the connected component of `x` in `Kᶜ` is path connected, and a path inside
it runs from `x` to `y` without meeting `K`. -/
theorem exists_path_to_outside_of_unbounded_component (K : Set ℂ) (hK : IsClosed K) (x : ℂ)
    (hxK : x ∉ K) (hnotbdd : ¬ Bornology.IsBounded (connectedComponentIn (Kᶜ) x)) :
    ∃ y : ℂ, y ∉ RectC ∧ ∃ p : ℝ → ℂ, Continuous p ∧ p 0 = x ∧ p 1 = y ∧ ∀ t, p t ∉ K := by
  -- The unbounded component is not contained in the bounded rectangle `RectC`.
  have hy : ∃ y ∈ connectedComponentIn (Kᶜ) x, y ∉ RectC := by
    by_contra hcon
    have hsub : connectedComponentIn (Kᶜ) x ⊆ RectC := by
      intro z hz
      by_contra hzR
      exact hcon ⟨z, hz, hzR⟩
    exact hnotbdd (isBounded_RectC.subset hsub)
  obtain ⟨y, hycomp, hyRect⟩ := hy
  refine ⟨y, hyRect, ?_⟩
  -- `Kᶜ` is open, hence its connected components agree with its path components.
  haveI : LocallyPathConnectedSpace ↥(Kᶜ) := hK.isOpen_compl.locallyPathConnectedSpace
  rw [connectedComponentIn_eq_image hxK] at hycomp
  obtain ⟨w, hw, hwy⟩ := hycomp
  rw [← pathComponent_eq_connectedComponent] at hw
  have hjoin : Joined (⟨x, hxK⟩ : ↥(Kᶜ)) w := mem_pathComponent_iff.mp hw
  obtain ⟨γ⟩ := hjoin
  -- Extend the path in the subpace `↥(Kᶜ)` to a path in `ℂ` parametrised on `ℝ`.
  refine ⟨fun t => (γ.extend t : ℂ), ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp γ.continuous_extend
  · show ((γ.extend 0 : ↥(Kᶜ)) : ℂ) = x
    rw [γ.extend_zero]
  · show ((γ.extend 1 : ↥(Kᶜ)) : ℂ) = y
    rw [γ.extend_one]
    exact hwy
  · intro t
    exact (γ.extend t).2

end Work.RPB.B1a.Maehara
