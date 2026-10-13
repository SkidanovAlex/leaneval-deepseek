import Mathlib
import Submission.Work.DSTRI.Basic

/-!
# Trichotomy of the characteristic regime of a local domain

For a local domain `R` exactly one of the three characteristic regimes holds
(and in particular at least one of them does):

* `EqualCharZero R` : `R` and its residue field both have characteristic `0`,
* `EqualCharPos R`  : `R` has characteristic the prime `p`,
* `MixedChar R`     : `R` has characteristic `0` and its residue field has
  characteristic the prime `p`.

The proof splits according to the characteristic of `R` (`CharP.exists'`, which
for a ring without zero divisors says that the characteristic is either `0` or a
prime), and in the characteristic-zero case splits again according to the
characteristic of the residue field `IsLocalRing.ResidueField R`, which is a
field and therefore again has characteristic `0` or a prime.
-/

namespace Work.DSTRI.Regime

open IsLocalRing

/-- **Trichotomy of the characteristic regime of a local domain.** -/
theorem regime_trichotomy (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] :
    Work.DSTRI.EqualCharZero R ∨ Work.DSTRI.EqualCharPos R ∨ Work.DSTRI.MixedChar R := by
  rcases CharP.exists' R with hR | ⟨p, ⟨hp⟩, hRp⟩
  · -- `R` has characteristic `0`; look at the residue field.
    rcases CharP.exists' (ResidueField R) with hk | ⟨q, ⟨hq⟩, hkq⟩
    · exact Or.inl ⟨hR, hk⟩
    · exact Or.inr (Or.inr ⟨q, hq, hR, hkq⟩)
  · -- `R` has characteristic the prime `p`.
    exact Or.inr (Or.inl ⟨p, hp, hRp⟩)

end Work.DSTRI.Regime
