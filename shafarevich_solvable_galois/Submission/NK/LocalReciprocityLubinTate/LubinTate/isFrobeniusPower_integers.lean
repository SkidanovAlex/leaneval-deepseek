import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
import Submission.NK.LocalReciprocityLubinTate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius-power condition holds at the integers of a local field

Let `F` be a nonarchimedean local field, `𝒪[F]` its ring of integers and `π ∈ 𝒪[F]` irreducible, i.e.
a uniformiser.  This file proves `NK.LocalReciprocityLubinTate.IsFrobeniusPower π (#𝓀[F])`: the
residue ring `𝒪[F] ⧸ (π)` is a finite field (the residue field `𝓀[F]`), its characteristic `p` is
prime, and its cardinality `#𝓀[F]` is a power of `p`.

This is the second coefficient-ring condition of the Lubin–Tate construction
(`NK.LocalReciprocityLubinTate.LubinTate.Series`), complementary to
`isLubinTateCoeff_integers`.
-/

open scoped ValuativeRel

universe u

set_option linter.style.haveILetI false
namespace NK.LocalReciprocityLubinTate.LubinTate

/-- **The `q`-th power map is additive on the residue ring at the integers of a local field**: with
`q = #𝓀[F]` a power of the residue characteristic `p`, so that `IsFrobeniusPower π (#𝓀[F])` holds.

An irreducible `π ∈ 𝒪[F]` is a uniformiser, so `(π)` is the maximal ideal of the discrete valuation
ring `𝒪[F]`; the quotient `𝒪[F] ⧸ (π)` is therefore the finite residue field `𝓀[F]`.  A finite
field has prime characteristic `p` and cardinality `p ^ n`. -/
theorem isFrobeniusPower_integers (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) :
    NK.LocalReciprocityLubinTate.IsFrobeniusPower π
      (NK.LocalReciprocityLubinTate.residueCard F) := by
  -- `(π)` is the maximal ideal, so `𝒪[F] ⧸ (π)` is the residue field `𝓀[F]`.
  have hI : Ideal.span {π} = IsLocalRing.maximalIdeal ↥((ValuativeRel.valuation F).integer) :=
    hπ.maximalIdeal_eq.symm
  let e : (↥((ValuativeRel.valuation F).integer)) ⧸ Ideal.span {π} ≃+*
      (𝓀[F] : Type u) := Ideal.quotEquivOfEq hI
  letI : Fintype (𝓀[F] : Type u) := Fintype.ofFinite _
  -- The finite residue field has prime characteristic `p` and cardinality `p ^ n`.
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' (𝓀[F] : Type u)
  refine ⟨p, hp, ?_, ⟨n, ?_⟩⟩
  · -- transport `CharP` across `𝒪[F] ⧸ (π) ≃+* 𝓀[F]`.
    exact ((e.symm : (𝓀[F] : Type u) →+*
        (↥(ValuativeRel.valuation F).integer) ⧸ Ideal.span {π}).charP_iff
      e.symm.injective p).mp hchar
  · -- `residueCard F = Nat.card 𝓀[F] = Fintype.card 𝓀[F] = p ^ n`.
    rw [show NK.LocalReciprocityLubinTate.residueCard F = Fintype.card (𝓀[F] : Type u) from
      Nat.card_eq_fintype_card]
    exact hcard

end NK.LocalReciprocityLubinTate.LubinTate
