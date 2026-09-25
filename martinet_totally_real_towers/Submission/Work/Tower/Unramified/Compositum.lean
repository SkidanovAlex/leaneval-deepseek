import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup

/-!
# The compositum of unramified extensions, for the given predicate

`Work.Tower.isUnramifiedExtensionForallPrimes_sup` shows that the compositum of two everywhere
unramified finite extensions is everywhere unramified (in the strong, ramification-index form).
Here we deduce the corresponding statement for the given predicate `IsUnramifiedExtension` in the
Galois case.

## Main result

* `Work.Tower.isUnramifiedExtension_sup`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

/-- **The compositum of unramified extensions is unramified** (Galois case, given predicate). -/
theorem isUnramifiedExtension_sup {F L : Type*} [Field F] [NumberField F] [Field L] [Algebra F L]
    {E₁ E₂ : IntermediateField F L} [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    [IsGalois F E₁] [IsGalois F E₂]
    (h₁ : IsUnramifiedExtension F E₁) (h₂ : IsUnramifiedExtension F E₂) :
    IsUnramifiedExtension F ↥(E₁ ⊔ E₂) := by
  haveI : NumberField ↥E₁ := NumberField.of_module_finite F ↥E₁
  haveI : NumberField ↥E₂ := NumberField.of_module_finite F ↥E₂
  exact IsUnramifiedExtension.of_forallPrimes
    (Unramified.isUnramifiedExtensionForallPrimes_sup h₁.forallPrimes h₂.forallPrimes)

end Tower
end Work
