import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.ArchKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The arithmetic core of the `p = 2` node, written down as a standalone statement

`Work.SSGRoute.shafarevich_z_data_two_kummerCore` asks for a `b ∈ Kˣ` whose Kummer cochain has four
properties, stated in the language of profinite cochains.  Every one of those four properties has an
arithmetic form, and the bridge for each is already on disk:

* (A) agreement with the data `y` at the places of `cs(S)`: the quotient `b h⁻¹` is a local `2`-power
  at each prime of `K` under `cs(S)` — bridge
  `Work.SSGRoute.kummerCochar_agree_iff_localPowClass` (the local Kummer dictionary in agreement
  form);
* (B) unramifiedness at the places outside `cs(S)` that are not split in `Λ`: the `A`-valuation of
  `b` is a square in the value group — bridge
  `Work.SSGRoute.kummerCochar_eq_zero_of_isInertia_of_even_valuation` (whose hypothesis is exactly
  this form);
* (C) the vanishing at the involutions of `G_K`: `b` is a square in the fixed field of every
  involution, i.e. `b` is totally positive — bridge
  `Work.SSGRoute.nodeKummerCochar_eq_zero_on_involutions_iff`
  (`ZDataTwo/ArchKummer.lean`);
* (D) the sharpened one-sidedness at the good split places: at every companion `Q` of a place at
  which the cochain is ramified, the class of `b` is a local `2`-power — bridge
  `Work.SSGRoute.kummerCochar_eq_zero_iff_localPowClass` (the same dictionary, at `Q`).

This file writes that arithmetic statement down once, as `ArithCore`, in the exact form in which the
four bridges apply, so that (i) the remaining gap of this node is *visible as number theory* rather
than as cohomology, and (ii) the reduction
`ArithCore ⟹ shafarevich_z_data_two_kummerCore` is pure bookkeeping: for each clause one applies the
bridge named above.  Clause (D)'s *trigger* is kept in the cochain language — it is the same
hypothesis as in the node's clause (6), namely "the cochain is ramified at `A`" — precisely so that
the reduction needs no converse of the inertia criterion (which is a separate, genuinely local
ramification statement: odd valuation implies ramified implies the inertia acts non-trivially).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

/-- **The arithmetic core of the `p = 2` node.**  There is `b ∈ Kˣ` such that

* (A) `b · h⁻¹` is a local `2`-power at every prime of `K` below a place of `cs(S)`;
* (B) for every finite place `A` outside `cs(S)` that is not split in `Λ`, the `A`-valuation of `b`
  is a square in the value group (i.e. `b` is unramified at `A`);
* (C) `b` is a square in the fixed field of every involution of `G_K` (i.e. `b` is totally positive);
* (D) for every finite place `A` outside `cs(S)` that is split in `Λ` and every finite place `Q`
  conjugate to `A` but not `G_K`-conjugate to it, if the Kummer cochain of `b` is ramified at `A`
  then the class of `b` at the prime of `K` below `Q` is a local `2`-power.

This is the classical form of the node's arithmetic core; the four conditions are exactly the
hypotheses of the four dictionary bridges recorded in the module docstring. -/
def ArithCore (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (h : (↥K)ˣ) : Prop :=
  ∃ b : (↥K)ˣ,
    -- (A) agreement with `h` at the places of `cs(S)`
    (∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
        (h𝔭 : A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭),
        (∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A) →
          NK.UchidaKummer.localPowClass ↥K 2 𝔭 (b * h⁻¹) = 1) ∧
    -- (B) unramifiedness at the places outside `cs(S)` that are not split in `Λ`
    (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
        (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ A) → ¬ SSGRoute.IsSplitIn k Λ A →
        ∃ d : (↥K)ˣ,
          A.valuation (algebraMap ↥K Ω (b : ↥K)) =
            A.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2) ∧
    -- (C) total positivity
    (∀ c : Ω ≃ₐ[k] Ω, ∀ hc : c ∈ K.fixingSubgroup, c ^ 2 = 1 →
        ∃ y : Ω, ((IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ : Ω ≃ₐ[↥K] Ω) y = y ∧
          y ^ 2 = algebraMap ↥K Ω (b : ↥K)) ∧
    -- (D) one-sidedness at the good split places, with the cochain trigger
    (∀ (A Q : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (hQ : SSGRoute.IsFinPlace k Q)
        (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
        (h𝔭 : Q.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭),
        (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ A) → SSGRoute.IsSplitIn k Λ A →
        SSGRoute.IsConjPlace k A Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • A = Q) →
        (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ ∧ σ ∈ K.fixingSubgroup ∧
          nodeKummerCochar K ζ hζK hζ b σ ≠ 0) →
        NK.UchidaKummer.localPowClass ↥K 2 𝔭 b = 1)

end Work.SSGRoute.ZDataTwo
