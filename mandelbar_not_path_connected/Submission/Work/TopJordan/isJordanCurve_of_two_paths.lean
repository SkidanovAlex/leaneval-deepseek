/-
# Jordan curves from two paths

`Commons.Topology.Jordan.two_arcs_through` splits a Jordan curve through `-1` and `1` into two
injective paths whose ranges meet exactly in the two endpoints.  Here is the converse: two such
paths glue back to a Jordan curve.  This is the form produced by the endgame's crossing
arguments.
-/
import Mathlib
import Submission.Work.Top.Jordan
import Submission.Work.TopJordan.CurveModel
import Submission.Work.TopJordan.isJordanCurve_of_two_arcs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Set

namespace Work.TopJordan

noncomputable section

/-- **Two injective paths in the plane with the same endpoints, whose ranges meet exactly in the
two endpoints, form a Jordan curve.** -/
theorem isJordanCurve_of_two_paths (P Q : Path (-1 : ℂ) 1)
    (hP : Function.Injective ⇑P) (hQ : Function.Injective ⇑Q)
    (hinter : Set.range ⇑P ∩ Set.range ⇑Q = {(-1 : ℂ), 1}) :
    Work.Top.IsJordanCurve (Set.range ⇑P ∪ Set.range ⇑Q) := by
  refine isJordanCurve_of_two_arcs P.toContinuousMap Q.toContinuousMap hP hQ ?_ ?_ ?_ ?_
  · exact (Path.source P).trans (Path.source Q).symm
  · exact (Path.target P).trans (Path.target Q).symm
  · intro h
    exact absurd ((Path.source P).symm.trans (h.trans (Path.target P))) (by norm_num)
  · intro s t hst
    have hmem : (⇑P) s ∈ Set.range ⇑P ∩ Set.range ⇑Q := ⟨⟨s, rfl⟩, ⟨t, hst.symm⟩⟩
    rw [hinter] at hmem
    rcases hmem with h | h
    · exact Or.inl (hP (h.trans (Path.source P).symm))
    · exact Or.inr (hP (h.trans (Path.target P).symm))

end

end Work.TopJordan
