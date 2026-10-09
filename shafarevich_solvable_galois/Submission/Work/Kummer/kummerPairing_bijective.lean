import Mathlib
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerPairing_bijective_of_isKummerExtension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

/-- **Bijectivity of the Kummer pairing.**  For `K` a field containing a primitive `n`-th root of
unity `ζ` and `L/K` a finite Galois extension, the Kummer pairing
`kummerPairing hζ : (Kˣ ∩ (Lˣ)^n)/(Kˣ)^n →* (Gal(L/K) →* μ_n)` is bijective.

Injectivity is `Work.Kummer.kummerPairing_injective` (the kernel is the subgroup of `n`-th powers
of `K`), and surjectivity is `Work.Kummer.kummerCharacter_surjective_of_isGalois` (the Lagrange
resolvent).  Neither an exponent condition on `Gal(L/K)` nor the hypothesis that `L/K` is generated
by `n`-th roots of elements of `K` is needed. -/
theorem kummerPairing_bijective {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L]
    [IsGalois K L] : Function.Bijective (kummerPairing (K := K) (L := L) hζ) := by
  refine ⟨kummerPairing_injective (K := K) (L := L) hζ, fun χ => ?_⟩
  obtain ⟨a, ha⟩ := kummerCharacter_surjective_of_isGalois (K := K) (L := L) hζ χ
  exact ⟨QuotientGroup.mk' _ a, by rw [kummerPairing_mk, ha]⟩

end Work.Kummer
