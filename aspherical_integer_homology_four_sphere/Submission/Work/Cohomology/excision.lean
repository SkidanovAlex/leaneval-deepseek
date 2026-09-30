import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.coker_smallOfU_iso_relChains

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cohomology

theorem excision (X : TopCat) (A Z : Set X) (h : closure Z ⊆ interior A) (n : ℕ) :
    Nonempty (((Work.Cohomology.relChains X A).homology n) ≅
      ((Work.Cohomology.relChains (TopCat.of {x : X | x ∉ Z})
        {x : {x : X | x ∉ Z} | (x : X) ∈ A}).homology n)) := by
  have hcov : interior A ∪ interior {x : X | x ∉ Z} = Set.univ :=
    univ_eq_interior_union_compl A Z h
  obtain ⟨e⟩ := coker_smallOfU_iso_relChains X A {x : X | x ∉ Z}
  exact excision_iso_rel_of_iso A {x : X | x ∉ Z} hcov n ⟨e⟩

end Work.Cohomology
