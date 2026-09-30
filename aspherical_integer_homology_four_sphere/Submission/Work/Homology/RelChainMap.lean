import Mathlib
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Functoriality of the relative chain complex

A map of pairs `Φ : (X, A) ⟶ (Y, B)` induces a chain map
`φ : C_*(X, A; R) ⟶ C_*(Y, B; R)` making the square
`C_*(X;R) --π_A--> C_*(X,A;R) --φ--> C_*(Y,B;R)` commute with
`C_*(X;R) --Φ#--> C_*(Y;R) --π_B--> C_*(Y,B;R)`.

The relative chain complex is the cokernel of `C_*(A;R) ⟶ C_*(X;R)`, so the
induced map is the one obtained from the universal property of the cokernel:
the composite `C_*(A;R) ⟶ C_*(X;R) ⟶ C_*(Y;B)` is zero because it factors
through `C_*(B;R)`, which is killed by the projection `π_B`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Homology

noncomputable section

/-- The square relating the inclusions and the chain maps induced by the two
components of a map of pairs. -/
theorem inclChain_naturality (R : ModuleCat ℤ) {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) :
    inclChain R X A ≫ singChainMap R Φ.hom
      = singChainMap R Φ.sub ≫ inclChain R Y B := by
  rw [inclChain, inclChain, ← singChainMap_comp, ← singChainMap_comp,
    PairHom.sub_comp_incl]

/-- The composite `C_*(A;R) ⟶ C_*(X;R) ⟶ C_*(Y,B;R)` is zero. -/
theorem inclChain_comp_relProj_eq_zero (R : ModuleCat ℤ) {X Y : TopCat} {A : Set X}
    {B : Set Y} (Φ : PairHom X Y A B) :
    inclChain R X A ≫ (singChainMap R Φ.hom ≫ relProj R Y B) = 0 := by
  rw [← Category.assoc, inclChain_naturality R Φ]
  show singChainMap R Φ.sub ≫ (singChainMap R (incl B) ≫ cokernel.π (inclChain R Y B)) = 0
  rw [show singChainMap R (incl B) = inclChain R Y B from rfl,
    cokernel.condition, CategoryTheory.Limits.comp_zero]

theorem RelChainMap (R : ModuleCat ℤ) {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) :
    ∃ φ : relChain R X A ⟶ relChain R Y B,
      CategoryTheory.CategoryStruct.comp (singChainMap R Φ.hom) (relProj R Y B) =
        CategoryTheory.CategoryStruct.comp (relProj R X A) φ := by
  refine ⟨cokernel.desc (inclChain R X A) (singChainMap R Φ.hom ≫ relProj R Y B)
    (inclChain_comp_relProj_eq_zero R Φ), ?_⟩
  exact (cokernel.π_desc (inclChain R X A) (singChainMap R Φ.hom ≫ relProj R Y B)
    (inclChain_comp_relProj_eq_zero R Φ)).symm

end

end Work.Homology
