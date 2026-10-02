import Mathlib
import Submission.Work.LandLeaves.snailDescentDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Set
open scoped Topology

/-- If the directions `q t / ‖q t‖` of a path `q` at all sufficiently large times lie in a closed
set `U`, then the set `Work.LandLeaves.directionLimitSet q` of limit directions is contained in
`U`. -/
theorem directionLimitSet_subset_of_eventually {q : ℝ → ℂ} {U : Set ℂ} (hU : IsClosed U)
    {T : ℝ} (h : ∀ t ∈ Set.Ici T, q t / ((‖q t‖ : ℝ) : ℂ) ∈ U) :
    Work.LandLeaves.directionLimitSet q ⊆ U := by
  intro x hx
  -- Unfold the definition of the limit set into a pointwise statement about every `T ≥ 0`.
  simp only [directionLimitSet, Set.mem_iInter, Set.mem_Ici] at hx
  -- Look at the threshold `max T 0`, which is `≥ 0` (so the limit-set description applies to it)
  -- and also `≥ T` (so the eventual hypothesis applies beyond it).
  have hx' : x ∈ closure ((fun t : ℝ => q t / ((‖q t‖ : ℝ) : ℂ)) '' Set.Ici (max T 0)) :=
    hx (max T 0) (le_max_right _ _)
  have hsub : ((fun t : ℝ => q t / ((‖q t‖ : ℝ) : ℂ)) '' Set.Ici (max T 0)) ⊆ U := by
    rintro y ⟨t, ht, rfl⟩
    exact h t (le_trans (le_max_left T 0) ht)
  -- Since `U` is closed, it contains the closure of any of its subsets.
  exact closure_minimal hsub hU hx'

end Work.LandLeaves
