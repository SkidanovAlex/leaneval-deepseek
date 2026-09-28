import Mathlib

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
