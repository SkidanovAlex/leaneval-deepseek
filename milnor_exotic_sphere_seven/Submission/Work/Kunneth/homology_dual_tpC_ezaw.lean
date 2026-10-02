import Mathlib
import Submission.Work.Kunneth.TensorCo
import Submission.Work.Kunneth.ez_aw_homotopy
import Submission.Work.Kunneth.aw_ez_homotopy
import Submission.Work.Cohomology.homotopyEquivDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Homology of the dual of the tensor product of the singular complexes of `X` and `Y`

The Eilenberg–Zilber / Alexander–Whitney theorem states that the Alexander–Whitney chain map
`awMap X Y : C_*(X ⊗ Y) ⟶ C_*(X) ⊗_ℤ C_*(Y)` and the shuffle map
`ezMap X Y : C_*(X) ⊗_ℤ C_*(Y) ⟶ C_*(X ⊗ Y)` are inverse up to chain homotopy
(`Work.Kunneth.aw_ez_homotopy`, `Work.Kunneth.ez_aw_homotopy`).  Dualising this homotopy
equivalence (`Work.Cohomology.homotopyEquivDual`) and applying
`HomotopyEquiv.toHomologyIso`, a homotopy equivalence of cochain complexes induces an isomorphism
of cohomology in every degree, which is the assertion of the present lemma.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The Eilenberg–Zilber homotopy equivalence at the level of the singular chain complexes**,
assembled from the two chain homotopies `awMap ≫ ezMap ~ id` and `ezMap ≫ awMap ~ id`. -/
def ezawHomotopyEquiv (X Y : SSet) : HomotopyEquiv (sChain (sProd X Y)) (tChain X Y) where
  hom := awMap X Y
  inv := ezMap X Y
  homotopyHomInvId := (aw_ez_homotopy X Y).some
  homotopyInvHomId := (ez_aw_homotopy X Y).some

/-- The Eilenberg–Zilber homotopy equivalence dualises to a homotopy equivalence between the
dual cochain complexes. -/
theorem nonempty_homotopyEquiv_dualComplex (X Y : SSet) :
    Nonempty (HomotopyEquiv
      (Work.Cohomology.dualComplex ℤ (tChain X Y))
      (Work.Cohomology.dualComplex ℤ (sChain (sProd X Y)))) :=
  Work.Cohomology.homotopyEquivDual ℤ (ezawHomotopyEquiv X Y)

/-- The singular cochain complex of the product `X ⊗ Y` is the dual of the tensor product of the
singular chain complexes of `X` and `Y`, up to a homotopy equivalence; hence their cohomology
groups are canonically isomorphic in every degree. -/
theorem homology_dual_tpC_ezaw (X Y : SSet) (n : ℕ) :
    Nonempty (CategoryTheory.Iso ((Work.Cohomology.cochainC ℤ (Work.Kunneth.sProd X Y)).homology n)
      ((Work.Cohomology.dualComplex ℤ
        (Work.Kunneth.tpC (Work.Kunneth.sChain X) (Work.Kunneth.sChain Y))).homology n)) := by
  obtain ⟨e⟩ := nonempty_homotopyEquiv_dualComplex X Y
  exact ⟨(e.toHomologyIso n).symm⟩

end

end Work.Kunneth
