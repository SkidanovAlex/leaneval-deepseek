import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre

open CategoryTheory Limits

/-- The coproduct (in `ModuleCat ℤ`) of `A` copies of `ℤ` is the free `ℤ`-module on `A`,
i.e. the finitely supported functions `A →₀ ℤ`.  This is `ModuleCat.finsuppCoconeIsColimit`
compared with the canonical colimit cocone defining `∐`. -/
theorem serreC0CoproductFinsupp (A : Type) :
    Nonempty ((∐ fun _ : A => ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℤ (A →₀ ℤ)) := by
  classical
  exact ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ A)⟩

end Work.Serre
