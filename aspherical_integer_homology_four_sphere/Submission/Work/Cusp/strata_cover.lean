import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The three layer strata of the filling piece cover the square.  Since `nrm p = max |p 0| |p 1|`,
`Sq` is the set `{nrm p ≤ 1}`, while `coreStratum = {nrm p < 1/12}` and
`polarStratum = {1/24 < nrm p ≤ 1}` already cover everything with `nrm p ≤ 1` (note
`1/24 < 1/12`).  The collar stratum `cuspStratum = {1/2 < nrm p ≤ 1}` is redundant for the cover. -/
theorem strata_cover : coreStratum ∪ polarStratum ∪ cuspStratum = Sq := by
  ext p
  simp only [coreStratum, polarStratum, cuspStratum, Sq, Set.mem_union, Set.mem_ofPred_eq, nrm]
  rw [← max_le_iff]
  constructor
  · rintro ((h | ⟨-, h⟩) | ⟨-, h⟩)
    · linarith
    · exact h
    · exact h
  · intro h
    rcases lt_or_ge (max |p 0| |p 1|) (1 / 12) with hlt | hge
    · exact Or.inl (Or.inl hlt)
    · exact Or.inl (Or.inr ⟨by linarith, h⟩)

end Work.Cusp
