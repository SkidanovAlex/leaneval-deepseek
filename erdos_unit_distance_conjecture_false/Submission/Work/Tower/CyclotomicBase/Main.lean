import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.Ramification
import Submission.Work.Tower.CyclotomicBase.finrank_Mfield
import Submission.Work.Tower.CyclotomicBase.disc_Mfield
import Submission.Work.Tower.CyclotomicBase.finrank_Ffield_eq_three
import Submission.Work.Tower.CyclotomicBase.finrank_Mfield_over_FMfield
import Submission.Work.Tower.CyclotomicBase.isAbelianGalois_FMfield_Mfield
import Submission.Work.Tower.CyclotomicBase.pow_three_gal_FMfield_Mfield
import Submission.Work.Tower.CyclotomicBase.isTotallyReal_FMfield
import Submission.Work.Tower.CyclotomicBase.disc_Ffield

/-!
# The cyclotomic base of the tower (paper Proposition 3.2)

For distinct primes `r₁, …, r_ℓ ≡ 1 (mod 3)` there are a totally real cubic Galois field `F` and a
number field `M` with:

* `M/F` Galois with elementary abelian Galois group of exponent `3` and order `3^{ℓ-1}`,
* `M/F` unramified at every finite prime,
* `|disc F| = (∏ rᵢ)²` (so the root discriminant of `F` is `(∏ rᵢ)^{2/3}`).

This is paper Proposition 3.2 together with its discriminant computation.  The construction is the
one of the paper: `M` is the subfield of `ℚ(ζ_D)`, `D = ∏ rᵢ`, cut out by the product of the `ℓ`
cubic characters of the primes `rᵢ`, and `F` is the cubic field cut out by the product character.

## Main result

* `Work.Tower.exists_cubic_unramified_extension_data`
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower

open Work.Tower.CyclotomicBase

/-- **Paper Proposition 3.2.**  For distinct primes `rᵢ ≡ 1 (mod 3)`, `i = 1, …, ℓ`, with
`ℓ ≥ 1`, there exists a totally real cubic Galois field `F` and a number field `M ⊇ F` such that
`M/F` is Galois with elementary abelian Galois group of exponent `3` and order `3^(ℓ-1)`,
unramified at every finite prime, and `|disc F| = (∏ i, r i)²`.

(For `ℓ = 0` the statement is false: it would demand a cubic field with `|disc| = 1`.) -/
theorem exists_cubic_unramified_extension_data
    (ℓ : ℕ) (hℓ : 0 < ℓ) (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    (hrinj : Function.Injective r) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ℚ M) (_ : IsGalois ℚ M)
      (F : IntermediateField ℚ M),
      Module.finrank ℚ ↥F = 3 ∧ IsGalois ℚ ↥F ∧
      NumberField.IsTotallyReal ↥F ∧
      Module.finrank ↥F M = 3 ^ (ℓ - 1) ∧
      IsGalois ↥F M ∧ IsAbelianGalois ↥F M ∧
      (∀ σ : Gal(M/↥F), σ ^ 3 = 1) ∧
      Work.Tower.IsUnramifiedExtension ↥F M ∧
      |NumberField.discr ↥F| = ((∏ i, r i : ℕ) : ℤ) ^ 2 := by
  haveI hD : NeZero (D r) := neZero_D r hr
  refine ⟨↥(Mfield r hr hr3), inferInstance, inferInstance, inferInstance,
    isGalois_Mfield r hr hr3, FMfield r hr hr3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finrank_FMfield]
    exact finrank_Ffield_eq_three hℓ r hr hr3 hrinj
  · exact isGalois_FMfield r hr hr3
  · exact isTotallyReal_FMfield hℓ r hr hr3 hrinj
  · exact finrank_Mfield_over_FMfield hℓ r hr hr3 hrinj
  · exact isGalois_tower_Ffield_Mfield r hr hr3
  · exact isAbelianGalois_FMfield_Mfield r hr hr3 hrinj
  · exact pow_three_gal_FMfield_Mfield r hr hr3 hrinj
  · exact isUnramifiedExtension_FMfield hℓ r hr hr3 hrinj
  · simp only [FMfield]
    rw [← NumberField.discr_eq_discr_of_algEquiv (↥(Ffield r hr hr3))
      (IntermediateField.restrictAlgEquiv (Ffield_le_Mfield r hr hr3))]
    exact disc_Ffield hℓ r hr hr3 hrinj

end Work.Tower
