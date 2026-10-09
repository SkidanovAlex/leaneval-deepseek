import Mathlib
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerCharacterHom_range
import Submission.Work.Kummer.kummerPairing_bijective_of_isKummerExtension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

/-- **The range of the Kummer character map, pointwise form.**  For a finite Galois extension
`L/K` and a primitive `n`-th root of unity `ζ ∈ K`, a character `χ : Gal(L/K) →* μ_n(K)` lies in
the range of the Kummer character map if and only if it is trivial on the automorphisms fixing the
Kummer subfield `kummerSubfield n K L`.

Both directions are formal consequences of the two halves of `kummerCharacterHom_range`:

* the Kummer character of any `a ∈ Kˣ ∩ (Lˣ)^n` is trivial on the fixing subgroup of
  `kummerSubfield n K L`, since the chosen `n`-th root of `a` generates it over `K`;
* conversely every character trivial on that fixing subgroup is a Kummer character, by the
  Lagrange-resolvent (Noether) form of Hilbert's Theorem 90. -/
theorem kummerCharacterHom_range_iff {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L]
    [IsGalois K L] (χ : Gal(L/K) →* rootsOfUnity n K) :
    χ ∈ Set.range (kummerCharacterHom (K := K) (L := L) hζ) ↔
      (kummerSubfield n K L).fixingSubgroup ≤ χ.ker := by
  constructor
  · rintro ⟨a, rfl⟩
    exact kummerCharacter_eq_one_of_mem_fixingSubgroup hζ a
  · intro _
    exact kummerCharacterHom_surjective_aux hζ χ

end Work.Kummer
