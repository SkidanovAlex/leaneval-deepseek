import Mathlib
import Submission.Work.Kunneth.TensorCo
import Submission.Work.Kunneth.Algebra
import Submission.Work.Cohomology.homotopyEquivDual
import Submission.Work.Kunneth.EZAWTensor
import Submission.Work.Kunneth.Splitting
import Submission.Work.Kunneth.tpMapHomotopyGen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `H^n` of the dual of the tensor product depends only on the homology of the second factor

For a chain complex `C` of `ℤ`-modules and a chain complex `D` all of whose terms and homology
modules are projective, the cohomology of the dual of the Koszul tensor product
`Work.Kunneth.tpC C D` is the cohomology of `tpC C (homSum D)`, where
`Work.Kunneth.homSum D` is the complex with `D`'s homology in each degree and zero differentials.

Indeed `Work.Kunneth.piHom` and `Work.Kunneth.iotaHom` (`Submission/Work/Kunneth/Splitting.lean`)
exhibit `homSum D` as a deformation retract of `D`; tensoring with `C` and dualising
(`Work.Cohomology.homotopyEquivDual`) produces a homotopy equivalence of the dual cochain
complexes, hence an isomorphism on cohomology in every degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

theorem homology_dual_tpC_homSum (C D : ChainComplex (ModuleCat ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q)) (hH : ∀ q, Module.Projective ℤ ↥(D.homology q))
    (n : ℕ) :
    Nonempty (CategoryTheory.Iso
      ((Work.Cohomology.dualComplex ℤ (Work.Kunneth.tpC C D)).homology n)
      ((Work.Cohomology.dualComplex ℤ (Work.Kunneth.tpC C (Work.Kunneth.homSum D))).homology n)) := by
  have hhom : Homotopy (Work.Kunneth.tpMap C C D D (𝟙 C)
        (Work.Kunneth.piHom D hD hH ≫ Work.Kunneth.iotaHom D hD hH))
      (Work.Kunneth.tpMap C C D D (𝟙 C) (𝟙 D)) :=
    Classical.choice (Work.Kunneth.tpMapHomotopyGen C C D D (𝟙 C) (𝟙 C)
      (Work.Kunneth.piHom D hD hH ≫ Work.Kunneth.iotaHom D hD hH) (𝟙 D)
      (Homotopy.ofEq rfl) (Work.Kunneth.homotopyData D hD hH))
  have h1 : Work.Kunneth.tpMap C C D (Work.Kunneth.homSum D) (𝟙 C) (Work.Kunneth.piHom D hD hH)
        ≫ Work.Kunneth.tpMap C C (Work.Kunneth.homSum D) D (𝟙 C) (Work.Kunneth.iotaHom D hD hH)
      = Work.Kunneth.tpMap C C D D (𝟙 C)
          (Work.Kunneth.piHom D hD hH ≫ Work.Kunneth.iotaHom D hD hH) := by
    rw [Work.Kunneth.tpMap_comp, Category.id_comp]
  have h2 : Work.Kunneth.tpMap C C (Work.Kunneth.homSum D) D (𝟙 C) (Work.Kunneth.iotaHom D hD hH)
        ≫ Work.Kunneth.tpMap C C D (Work.Kunneth.homSum D) (𝟙 C) (Work.Kunneth.piHom D hD hH)
      = 𝟙 (Work.Kunneth.tpC C (Work.Kunneth.homSum D)) := by
    rw [Work.Kunneth.tpMap_comp, Category.id_comp, Work.Kunneth.iota_comp_pi,
      Work.Kunneth.tpMap_id]
  have e : HomotopyEquiv (Work.Kunneth.tpC C D) (Work.Kunneth.tpC C (Work.Kunneth.homSum D)) := by
    refine { hom := Work.Kunneth.tpMap C C D (Work.Kunneth.homSum D) (𝟙 C) (Work.Kunneth.piHom D hD hH)
             inv := Work.Kunneth.tpMap C C (Work.Kunneth.homSum D) D (𝟙 C) (Work.Kunneth.iotaHom D hD hH)
             homotopyHomInvId := ?_
             homotopyInvHomId := ?_ }
    · rw [h1]
      rw [Work.Kunneth.tpMap_id] at hhom
      exact hhom
    · exact Homotopy.ofEq h2
  obtain ⟨e'⟩ := Work.Cohomology.homotopyEquivDual ℤ e
  exact ⟨e'.symm.toHomologyIso n⟩

end

end Work.Kunneth
