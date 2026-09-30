import Mathlib
import Submission.Work.HomologyMV.Model

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

open CategoryTheory

/-- Two morphisms `ℤ^n ⟶ N` of `ModuleCat ℤ` (i.e. `freeMod n ⟶ N`) are equal as soon as they agree on the standard basis vectors of `ℤ^n`. -/
theorem ext_on_basis {n : ℕ} {N : ModuleCat ℤ} {f g : freeMod n ⟶ N} (h : ∀ i : Fin n, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply ModuleCat.hom_ext
  apply Module.Basis.ext (Pi.basisFun ℤ (Fin n))
  intro i
  rw [Pi.basisFun_apply]
  exact h i

end Work.HomologyMV
