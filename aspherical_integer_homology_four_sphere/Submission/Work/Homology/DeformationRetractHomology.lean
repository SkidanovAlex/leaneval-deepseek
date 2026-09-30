import Mathlib
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Homology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-- A deformation retraction induces an isomorphism on singular homology with
coefficients in any `R : ModuleCat ℤ`, in every degree.

The retraction `r : X ⟶ A` and the inclusion `i : A ⟶ X` give mutually inverse
maps on homology: `i ≫ r = 𝟙_A` directly, while `r ≫ i` is homotopic to `𝟙_X`
by hypothesis, and homotopic maps induce equal maps on singular homology. -/
theorem DeformationRetractHomology (R : ModuleCat ℤ) (k : ℕ) {X : TopCat} {A : Set X}
    (h : DeformationRetract X A) :
    Nonempty (singHomology R k X ≅ singHomology R k (TopCat.of A)) := by
  -- `retract ≫ incl` is homotopic to the identity of `X`, hence equal to it on homology.
  obtain ⟨H⟩ := h.homotopy
  have hhom : singHomologyMap R k (h.retract ≫ incl A) = singHomologyMap R k (𝟙 X) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat ℤ) H R k
  refine ⟨{ hom := singHomologyMap R k h.retract
            inv := singHomologyMap R k (incl A)
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [← singHomologyMap_comp, hhom, singHomologyMap_id]
  · rw [← singHomologyMap_comp, h.retract_incl, singHomologyMap_id]

end Work.Homology
