import Mathlib
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Point

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

theorem ContractibleHomology (R : ModuleCat ℤ) (X : TopCat)
    [ContractibleSpace X] (k : ℕ) : CategoryTheory.Limits.IsZero (singHomology R (k + 1) X) := by
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨p, hp⟩ := id_nullhomotopic X
  -- Homotopy invariance: the identity and the constant map at `p` induce the same
  -- map on homology.
  have hhom : singHomologyMap R (k + 1) (𝟙 X) =
      singHomologyMap R (k + 1) (TopCat.ofHom (ContinuousMap.const X p)) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (C := ModuleCat ℤ) (H := hp.some) R (k + 1)
  rw [← singHomologyMap_id R (k + 1) X, hhom]
  -- The constant map factors through the one-point space.
  have hcq : (TopCat.ofHom (ContinuousMap.const X p) : X ⟶ X) =
      (TopCat.ofHom (ContinuousMap.const X PUnit.unit) : X ⟶ TopCat.of PUnit) ≫
        (TopCat.ofHom (ContinuousMap.const PUnit p) : TopCat.of PUnit ⟶ X) := by
    ext x
    rfl
  rw [hcq, singHomologyMap_comp R (k + 1)]
  -- `H_{k+1}(pt; R)` is a zero object, so the first factor is zero.
  rw [IsZero.eq_zero_of_src (isZero_singHomology_point R k)
    (singHomologyMap R (k + 1) (TopCat.ofHom (ContinuousMap.const PUnit p)))]
  exact comp_zero

end Work.Homology
