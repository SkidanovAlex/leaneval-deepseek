import Mathlib
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.Splitting
import Submission.Work.Cohomology.uctDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Kunneth

/-- **A chain complex of projective `ℤ`-modules with projective homology splits.**

There are maps `π : D ⟶ homSum D` and `ι : homSum D ⟶ D` with `ι ≫ π = 𝟙` and
`π ≫ ι ≃ 𝟙`, i.e. `D` is homotopy equivalent to its homology complex (with zero
differentials).  This is the algebraic input of the Künneth theorem. -/
theorem exists_splitting (D : ChainComplex (ModuleCat ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) :
    ∃ (π : Work.Kunneth.chHom D (Work.Kunneth.homSum D))
      (ι : Work.Kunneth.chHom (Work.Kunneth.homSum D) D),
      CategoryTheory.CategoryStruct.comp ι π
          = CategoryTheory.CategoryStruct.id (Work.Kunneth.homSum D)
        ∧ Nonempty (Homotopy (CategoryTheory.CategoryStruct.comp π ι)
            (CategoryTheory.CategoryStruct.id D)) :=
  ⟨piHom D hD hH, iotaHom D hD hH, iota_comp_pi D hD hH, ⟨homotopyData D hD hH⟩⟩

end Work.Kunneth
