import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
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
