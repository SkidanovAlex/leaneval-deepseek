import Mathlib.NumberTheory.Cyclotomic.Basic
import Submission.NK.Chebotarev.Density
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Kronecker–Weber over `ℚ`, as an explicit hypothesis

The **Kronecker–Weber theorem** says that every finite abelian extension of `ℚ` is contained in a
cyclotomic field.  It is the one arithmetic input of Čebotarev's density theorem over `ℚ` that is
*not* available in the library, and it is recorded here as an explicit `Prop`,
`NK.Chebotarev.KroneckerWeber`, so that the reduction of Čebotarev to the cyclotomic case can be
stated and proved without it.  The main consumer is
`NK.Chebotarev.abelianChebotarev_of_kroneckerWeber`.
-/

set_option linter.unusedSectionVars false

universe u

namespace NK.Chebotarev

/-- A **model of an abelian extension `L/ℚ` inside a cyclotomic field**: a cyclotomic field
`F = ℚ(ζ_n)`, a Galois intermediate field `E ⊆ F` and a `ℚ`-algebra isomorphism `L ≃ₐ[ℚ] E`. -/
structure CyclotomicModel (L : Type u) [Field L] [NumberField L] (n : ℕ) : Type (u + 1) where
  /-- the cyclotomic field `ℚ(ζ_n)` -/
  F : Type u
  [fieldF : Field F]
  [numberFieldF : NumberField F]
  [cyclotomicF : IsCyclotomicExtension {n} ℚ F]
  /-- the intermediate field isomorphic to `L` -/
  E : IntermediateField ℚ F
  [galoisE : IsGalois ℚ ↥E]
  /-- the isomorphism exhibiting `L` as an intermediate field of `ℚ(ζ_n)` -/
  equiv : L ≃ₐ[ℚ] ↥E

attribute [instance] CyclotomicModel.fieldF CyclotomicModel.numberFieldF
  CyclotomicModel.cyclotomicF CyclotomicModel.galoisE

/-
## Roadmap: how to discharge this hypothesis

The reductions in this chapter are complete, so the *only* missing input for the abelian case of
Čebotarev over `ℚ` is this `Prop`.  The classical routes are:

1. **Global class field theory for `ℚ`.**  For `L/ℚ` abelian, the Artin map identifies
   `Gal(L/ℚ)` with a quotient of a ray class group of `ℚ`, and the ray class group of `ℚ` modulo
   `n` is `(ℤ/n)^×`; comparing with `ℚ(ζ_n)/ℚ` (whose Galois group is `(ℤ/n)^×` and whose
   conductor is `n`) shows `L ⊆ ℚ(ζ_n)` for `n` the conductor of `L`.  The idèle-class-group
   version of Artin reciprocity is being built in the sibling subproject
   `Submission.NK.GlobalCFT` (`NK.GlobalCFT.ArtinReciprocity`); what is still missing on top of
   it is the *conductor* technology (or, equivalently, the conductor–discriminant comparison).

2. **Ramification/discriminant bounds.**  For prime power conductor `p^k`, one shows directly that
   the maximal abelian extension of `ℚ` of conductor dividing `p^k` has degree `φ(p^k)`, using the
   discriminant bound together with the fact that `ℚ` has no non-trivial unramified extension
   (Minkowski's bound, available in Mathlib).  This gives the prime-power case of Kronecker–Weber;
   the general case follows by multiplicativity.

3. **Kummer theory.**  Over `ℚ(ζ_p)` the abelian extensions of exponent `p` are Kummer, and the
   cyclotomic units generate the relevant quotient; this is the classical elementary proof.

The trivial case (`L` itself cyclotomic) is proved in
`NK.Chebotarev.nonempty_cyclotomicModel_of_isCyclotomic`, which shows that this `Prop` is
non-vacuous.
-/

/-- **The Kronecker–Weber theorem over `ℚ`.**  Every finite abelian extension `L/ℚ` is isomorphic
over `ℚ` to an intermediate field of a cyclotomic field `ℚ(ζ_n)`; the intermediate field is Galois
over `ℚ` because `L/ℚ` is abelian. -/
def KroneckerWeber : Prop :=
  ∀ {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ a b : Gal(L/ℚ), a * b = b * a) →
    ∃ (n : ℕ) (_ : 0 < n), Nonempty (CyclotomicModel L n)

end NK.Chebotarev
