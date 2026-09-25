import Mathlib

open NumberField

namespace Work.CMRealSubfield.RootDiscr

/-- For a tower of number fields `E ⊆ K`, the `[K : E]`-th power of the absolute
discriminant of `E` divides the absolute discriminant of `K`.

This is the divisibility half of the tower formula for discriminants: if `𝓞 K` is a free
`𝓞 E`-module (automatic for number fields, the extension being separable), then

`|disc K| = |N_{E/ℚ}(𝔡_{K/E})| · |disc E| ^ [K : E]`,

so `|disc E| ^ [K : E]` divides `|disc K|`. It is the general form of the quadratic case
`discr_maximalRealSubfield_sq_dvd` for a CM field `K` and its maximal real subfield `K⁺`.

In Lean this is the proof of Mathlib's `NumberField.discr_dvd_discr` (which only exposes the
first-power divisibility `discr E ∣ discr K`) replayed at the full exponent, using the tower
identity `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`. -/
theorem pow_discr_dvd_discr {E K : Type*} [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] :
    (NumberField.discr E) ^ Module.finrank E K ∣ NumberField.discr K := by
  rw [← Int.dvd_natAbs,
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow E (𝓞 E) K (𝓞 K),
    Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow, ← mul_assoc,
    mul_comm _ (NumberField.discr E ^ _), mul_assoc]
  exact Int.dvd_mul_right _ _

end Work.CMRealSubfield.RootDiscr

namespace Work.CMRealSubfield.RootDiscr

namespace Work.CMRealSubfield.RootDiscr

-- Alias: the same statement under the (doubly nested) namespace in which this file's template
-- declared it, so that either fully qualified name resolves.
/-- For a tower `E ⊆ K` of number fields, `disc E ^ [K : E]` divides `disc K` (alias). -/
theorem pow_discr_dvd_discr {E K : Type*} [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] :
    (NumberField.discr E) ^ Module.finrank E K ∣ NumberField.discr K :=
  _root_.Work.CMRealSubfield.RootDiscr.pow_discr_dvd_discr

end Work.CMRealSubfield.RootDiscr

end Work.CMRealSubfield.RootDiscr
