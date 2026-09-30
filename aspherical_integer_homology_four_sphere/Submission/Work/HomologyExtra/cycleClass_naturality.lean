import Mathlib
import Submission.Work.HomologyExtra.CycleClass

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Naturality of `cycleClass`

The homology class of a cycle is natural in chain maps: if `x : A ⟶ K.X i` is a cycle in `K`
and `φ : K ⟶ L` is a chain map, then the class of `x` in `Hᵢ(K)` maps under `Hᵢ(φ)` to the
class of the cycle `x ≫ φ.f i` in `Hᵢ(L)`.

The proof unwinds `cycleClass` as `K.liftCycles x _ rfl hx ≫ K.homologyπ i`, uses the
naturality of `homologyπ` (so that `homologyMap` becomes `cyclesMap`) and then the fact that
`liftCycles` is natural in the chain map, `liftCycles_comp_cyclesMap`.  The two proofs of
"being a cycle" that appear are propositions, so they are handled by proof irrelevance.
-/

open CategoryTheory

namespace Work.HomologyExtra

theorem cycleClass_naturality {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {A : ModuleCat ℤ} {i : ℕ}
    (x : A ⟶ K.X i) (hx : CategoryTheory.CategoryStruct.comp x (K.d i ((ComplexShape.down ℕ).next i)) = 0) :
    CategoryTheory.CategoryStruct.comp (Work.HomologyExtra.cycleClass x hx) (HomologicalComplex.homologyMap φ i) =
      Work.HomologyExtra.cycleClass (CategoryTheory.CategoryStruct.comp x (φ.f i))
        (by rw [CategoryTheory.Category.assoc, HomologicalComplex.Hom.comm,
          ← CategoryTheory.Category.assoc, hx, CategoryTheory.Limits.zero_comp]) := by
  rw [cycleClass_def, cycleClass_def]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]

end Work.HomologyExtra
