import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_units_quot_pow_maximalIdeal

/-!
# The order of `𝒪[F] / 𝔪[F]^n`

For a nonarchimedean local field `F` with ring of integers `𝒪[F]`, maximal ideal `𝔪[F]` and
residue cardinality `q = residueCard F = #𝓀[F]`, the truncated integer ring `𝒪[F] / 𝔪[F]^n` has
order `q^n`.

This is the classical computation `#(𝒪/𝔪^n) = q^n` (Serre, *Local Fields*, Ch. I §1 and Ch. IV
§1), the additive shadow of the multiplicative statement `#(𝒪/𝔪^n)ˣ = (q-1)q^{n-1}` already
formalised in the sibling module
`Submission.NK.LocalReciprocityLubinTate.Units.natCard_units_quot_pow_maximalIdeal`, where it is
proved for an arbitrary discrete valuation ring `R` with finite residue field
(`NK.LocalReciprocityLubinTate.Units.natCard_quot_maximalIdeal_pow`).  Here we only instantiate
that general theorem at `R = 𝒪[F]`: for a nonarchimedean local field Mathlib supplies both
`IsDiscreteValuationRing 𝒪[F]` and `Finite 𝓀[F]`
(`Mathlib.NumberTheory.LocalField.Basic`), and `𝓀[F]` is by definition
`IsLocalRing.ResidueField ↥𝒪[F]`, so `residueCard F` *is* `Nat.card (IsLocalRing.ResidueField R)`.

The result is used to count the finite quotients of the ring of integers appearing in the
Lubin–Tate picture: `𝒪[F]/𝔪[F]^n` is the truncation whose *units* are the level-`n` quotient of
`𝒪[F]ˣ` by the higher principal units.
-/

namespace NK.LocalReciprocityLubinTate.Audit

universe u

open scoped ValuativeRel

/-- **The order of `𝒪[F] / 𝔪[F]^n` is `q^n`**, `q = residueCard F`.

Both the general theorem (`Units.natCard_quot_maximalIdeal_pow` for a discrete valuation ring with
finite residue field) and the field-local statement are proved, the latter by unfolding
`residueCard` and identifying `Valuation.integer (ValuativeRel.valuation F)` with `𝒪[F]`. -/
theorem natCard_quotient_maximalIdeal_pow (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    Nat.card (↥(ValuativeRel.valuation F).integer ⧸
        (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer) ^ n)
      = NK.LocalReciprocityLubinTate.residueCard F ^ n := by
  simpa [NK.LocalReciprocityLubinTate.residueCard] using
    NK.LocalReciprocityLubinTate.Units.natCard_quot_maximalIdeal_pow
      ↥(ValuativeRel.valuation F).integer n

end NK.LocalReciprocityLubinTate.Audit
