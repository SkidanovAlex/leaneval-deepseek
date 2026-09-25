import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Unramified.Discriminant

namespace Work.Tower.CyclotomicBase

open NumberField

theorem isUnramifiedExtension_of_absNorm_differentIdeal_eq_one
    {F M : Type*} [Field F] [Field M] [Algebra F M] [NumberField F] [NumberField M]
    [IsGalois F M]
    (h : (differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers M)).absNorm = 1) :
    Work.Tower.IsUnramifiedExtension F M := by
  have hd : differentIdeal (𝓞 F) (𝓞 M) = ⊤ := Ideal.absNorm_eq_one_iff.mp h
  exact IsUnramifiedExtension.of_forallPrimes
    (isUnramifiedExtensionForallPrimes_iff_differentIdeal_eq_top.mpr hd)

end Work.Tower.CyclotomicBase
