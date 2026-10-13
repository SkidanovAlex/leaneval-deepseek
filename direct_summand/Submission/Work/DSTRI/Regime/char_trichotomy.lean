import Mathlib
import Submission.Work.DSTRI.Basic
import Submission.Work.DSTRI.Regime.regime_trichotomy

/-!
# DSTRI: the characteristic trichotomy of a local domain, residue-field form

For a local domain `R` with residue field `k = IsLocalRing.ResidueField R`, at least one
of the three characteristic regimes holds (in the form used by the direct-summand
argument; compare the regime predicates of `Work.DSTRI.Basic`):

* `CharZero k` — equal characteristic zero.  Here the characteristic of `k` is the
  characteristic of `R` itself: `CharZero k` already forces `CharZero R`
  (`Work.DSTRI.Regime.charZero_of_residue_charZero`), since the residue map
  `R →+* k` carries the canonical copy of `ℕ` in `R` onto the one in `k`.
* `CharP R p` for a prime `p` — equal characteristic `p`.
* `CharZero R` together with `CharP k p` for a prime `p` — mixed characteristic
  `(0, p)`.

The mathematics is the elementary observation that a ring without zero divisors
(equivalently, by `CharP.exists'`, a ring that is a domain) either is a `ℚ`-algebra or is
an `𝔽_p`-algebra for a unique prime `p`.  We apply it first to `R` and — in the
characteristic-zero case, where the first two alternatives of the goal both fail — to the
residue field `k`, which is a field and hence a domain as well.

This is the same content as `Work.DSTRI.Regime.regime_trichotomy`, read through the
identification `Work.DSTRI.EqualCharZero R = (CharZero R ∧ CharZero k)`: the leading
alternative of the present statement is exactly `EqualCharZero.residue`.
-/

namespace Work.DSTRI.Regime

open IsLocalRing

/-- **Trichotomy of the characteristic regime of a local domain**, with the
characteristic of the residue field as the leading alternative. -/
theorem char_trichotomy (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R] :
    CharZero (IsLocalRing.ResidueField R) ∨ (∃ p : ℕ, p.Prime ∧ CharP R p) ∨
      (∃ p : ℕ, p.Prime ∧ CharZero R ∧ CharP (IsLocalRing.ResidueField R) p) := by
  -- A domain has characteristic `0` or a prime: `CharP.exists'`.
  rcases CharP.exists' R with hR | ⟨p, ⟨hp⟩, hRp⟩
  · -- `R` has characteristic `0`; the residue field, being a domain, has characteristic
    -- `0` (first alternative) or a prime `q` (third alternative, with `CharZero R`).
    rcases CharP.exists' (IsLocalRing.ResidueField R) with hk | ⟨q, ⟨hq⟩, hkq⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inr ⟨q, hq, hR, hkq⟩)
  · -- `R` already has characteristic the prime `p`: second alternative.
    exact Or.inr (Or.inl ⟨p, hp, hRp⟩)

end Work.DSTRI.Regime
