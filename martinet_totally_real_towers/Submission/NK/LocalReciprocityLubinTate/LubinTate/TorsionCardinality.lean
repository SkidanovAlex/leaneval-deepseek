import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.DivisionPoints
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Integers
import Submission.NK.LocalReciprocityLubinTate.Audit.natCard_quotient_maximalIdeal_pow

/-!
# The cardinality of the Lubin–Tate torsion

For a nonarchimedean local field `F` of characteristic zero with uniformiser `π`, the cardinality of
the `π^n`-torsion `Λ_n = F_π[π^n]` of the standard Lubin–Tate group of `π` is

`#Λ_n = q^n`,   `q = residueCard F = #𝓀[F]`   (Milne, *CFT*, Theorem I.3.1),

which is also the cardinality of the ring `𝒪[F]/π^n`:

`Nat.card (𝒪[F]/𝔪[F]^n) = q^n`.

In the classical theory the two are linked by an isomorphism of `𝒪[F]/π^n`-modules
`Λ_n ≅ (𝒪[F]/π^n)^+`, which requires the Lubin–Tate group law evaluated at the torsion points (the
`𝒪[F]`-module structure on the maximal ideal); the *cardinalities*, which are what the numerical
applications use, are proved here unconditionally.

## Main results

* `NK.LocalReciprocityLubinTate.ncard_LTdivisionSet_residueCard`;
* `NK.LocalReciprocityLubinTate.natCard_LTdivisionSet_residueCard`;
* `NK.LocalReciprocityLubinTate.natCard_LTdivisionSet_eq_natCard_quotient`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate

universe u

/-- **`Λ_n` has `q^n` elements**, `q = residueCard F`: the cardinality statement of Milne,
*CFT*, Theorem I.3.1, in terms of the residue cardinality rather than a general `q`. -/
theorem ncard_LTdivisionSet_residueCard (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (n : ℕ) :
    (LTdivisionSet F (π : F) (residueCard F) n).ncard = residueCard F ^ n :=
  ncard_LTdivisionSet F π hπ (residueCard F) n (two_le_residueCard F)

/-- The `Nat.card` form of `#Λ_n = q^n`. -/
theorem natCard_LTdivisionSet_residueCard (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (n : ℕ) :
    Nat.card ↥(LTdivisionSet F (π : F) (residueCard F) n) = residueCard F ^ n := by
  rw [Nat.card_coe_set_eq, ncard_LTdivisionSet_residueCard F π hπ n]

/-- **The Lubin–Tate torsion has the cardinality of `(𝒪[F]/π^n)^+`**: this is the numerical half
of the classical isomorphism `Λ_n ≅ (𝒪[F]/π^n)^+` of `𝒪[F]/π^n`-modules (Milne, *CFT*, Theorem
I.3.1).  The isomorphism itself requires the `𝒪[F]`-module structure on the torsion, which is not
formalised here; its cardinality consequence is. -/
theorem natCard_LTdivisionSet_eq_natCard_quotient (F : Type u) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (n : ℕ) :
    Nat.card ↥(LTdivisionSet F (π : F) (residueCard F) n) =
      Nat.card (↥(ValuativeRel.valuation F).integer ⧸
        (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer) ^ n) := by
  rw [natCard_LTdivisionSet_residueCard F π hπ n,
    ← Audit.natCard_quotient_maximalIdeal_pow F n]

end NK.LocalReciprocityLubinTate
