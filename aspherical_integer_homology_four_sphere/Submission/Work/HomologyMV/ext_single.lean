import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

/-- Two `ℤ`-linear maps out of `ℤ^n = (Fin n → ℤ)` are equal as soon as they agree on the standard basis vectors `Pi.single i 1`.  This is the tool that turns a finite check of matrix columns into an equality of maps on homology (compare `Work.HomologyMV.ModuleCat.ext_on_span`). -/
theorem ext_single {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℤ N] {f g : (Fin n → ℤ) →ₗ[ℤ] N} (h : ∀ i : Fin n, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply Module.Basis.ext (Pi.basisFun ℤ (Fin n))
  intro i
  simpa using h i

end Work.HomologyMV
