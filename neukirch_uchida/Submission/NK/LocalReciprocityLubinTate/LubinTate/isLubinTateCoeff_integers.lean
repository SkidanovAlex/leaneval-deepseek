import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
import Submission.NK.LocalReciprocityLubinTate.Basic

/-!
# The Lubin–Tate coefficient-ring conditions hold at the integers of a local field

Let `F` be a nonarchimedean local field, `𝒪[F]` its ring of integers and `π ∈ 𝒪[F]` irreducible,
i.e. a uniformiser.  This file proves that the three coefficient-ring conditions
`NK.LocalReciprocityLubinTate.IsLubinTateCoeff π (#𝓀[F])` of the Lubin–Tate construction
(`NK.LocalReciprocityLubinTate.LubinTate.Series`) hold:

* `1 - π ^ r` is a unit for every `r ≥ 1`.  Indeed `𝒪[F]` is a local ring and `π ^ r` is a
  non-unit because `π` is irreducible, so `1 - π ^ r` is a unit
  (`IsLocalRing.isUnit_or_isUnit_one_sub_self`).
* the `q`-th power map is the identity on `𝒪[F] ⧸ (π)` with `q = #𝓀[F]`.  Since `𝒪[F]` is a
  discrete valuation ring, `π` generates the maximal ideal
  (`Irreducible.maximalIdeal_eq`), so the quotient *is* the residue field `𝓀[F]`, a finite field of
  cardinality `q`, in which `z ^ q = z` for every `z` (`FiniteField.pow_card`).
* `π` is a nonzerodivisor: `𝒪[F]` is a domain and `π ≠ 0` because it is irreducible
  (`Irreducible.ne_zero`).
-/

open scoped ValuativeRel

universe u

namespace NK.LocalReciprocityLubinTate.LubinTate

/-- **Milne, *CFT*, §I.1** (after Serre, *Local Fields*, Ch. XV §3): the ring of integers `𝒪[F]` of
a nonarchimedean local field, together with any uniformiser `π`, satisfies the coefficient-ring
conditions for the Lubin–Tate construction with `q = #𝓀[F]` the residue cardinality.

An irreducible `π ∈ 𝒪[F]` is a uniformiser: `𝒪[F]` is a discrete valuation ring, so `(π)` is the
maximal ideal; consequently `𝒪[F] ⧸ (π)` is the finite residue field `𝓀[F]`, on which the `q`-th
power map is the identity, and `π` is a nonzerodivisor in the domain `𝒪[F]`. -/
theorem isLubinTateCoeff_integers (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) :
    NK.LocalReciprocityLubinTate.IsLubinTateCoeff π
      (NK.LocalReciprocityLubinTate.residueCard F) := by
  refine ⟨fun r hr => ?_, ?_, fun a b hab => ?_⟩
  · -- `1 - π ^ r` is a unit: `π ^ r` is not, and `𝒪[F]` is local.
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self (π ^ r)).resolve_left
      (fun h => hπ.not_isUnit ((isUnit_pow_iff (by omega : r ≠ 0)).mp h))
  · -- `z ^ #𝓀[F] = z` in the residue field, transported along `𝒪[F] ⧸ (π) ≃+* 𝓀[F]`.
    intro z
    have hI : Ideal.span {π} = IsLocalRing.maximalIdeal ↥((ValuativeRel.valuation F).integer) :=
      hπ.maximalIdeal_eq.symm
    let e : (↥((ValuativeRel.valuation F).integer)) ⧸ Ideal.span {π} ≃+*
        (𝓀[F] : Type u) := Ideal.quotEquivOfEq hI
    have key : ∀ w : (𝓀[F] : Type u),
        w ^ (NK.LocalReciprocityLubinTate.residueCard F) = w := by
      intro w
      haveI : Fintype (𝓀[F] : Type u) := Fintype.ofFinite _
      rw [show NK.LocalReciprocityLubinTate.residueCard F = Nat.card (𝓀[F] : Type u) from rfl,
        Nat.card_eq_fintype_card]
      exact FiniteField.pow_card w
    apply e.injective
    rw [map_pow]
    exact key (e z)
  · -- `π` is a nonzerodivisor: `π ≠ 0` and `𝒪[F]` is a domain.
    exact mul_left_cancel₀ hπ.ne_zero hab

end NK.LocalReciprocityLubinTate.LubinTate
