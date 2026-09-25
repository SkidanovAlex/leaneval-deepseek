import Mathlib
import Submission.NK.RamificationDeep.InertiaField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.RamificationDeep

open scoped Pointwise

/-- **The restriction of a discrete valuation ring to a subfield is Noetherian.**

Let `A` be a discrete valuation ring of a field `L` and let `E` be a subfield of `L` (given by an
algebra structure `E → L`, which is automatically injective).  Then `A ∩ E = A.comap (algebraMap E L)`
is a Noetherian ring.

This is the general form of `isNoetherianRing_restrictRing`; it does not use the Galois-theoretic
hypotheses at all.  The proof is the classical dichotomy:

* either the valuation `v` of `A` restricts to a nontrivial valuation of `E`; its value group is then
  a nontrivial subgroup of the value group `(ℤᵐ⁰)ˣ ≅ ℤ` of `v`, hence (being a subgroup of a cyclic
  group) cyclic, so by Serre, *Local Fields*, I §1 Prop. 1 (Mathlib's
  `Valuation.valuationSubring_isDiscreteValuationRing`) `A ∩ E` is a discrete valuation ring, and a
  discrete valuation ring is a principal ideal ring, hence Noetherian;
* or the restricted valuation is trivial, in which case `A ∩ E = ⊤`, i.e. `A ∩ E = E` is a field,
  hence Noetherian.

The two ingredients used in the first bullet are that units of `ℤᵐ⁰` form a cyclic group
(`isCyclic_multiplicative` for `Multiplicative ℤ`, transported through `WithZero`) and that
`Nontrivial (valueGroup w)` follows from `w.IsNontrivial`. -/
theorem isNoetherianRing_comap_algebraMap {E L : Type*} [Field E] [Field L] [Algebra E L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] :
    IsNoetherianRing ↥(A.comap (algebraMap E L)) := by
  -- The `ℤᵐ⁰`-valued valuation attached to the DVR `A`.
  let v : Valuation L (WithZero (Multiplicative ℤ)) :=
    (IsDiscreteValuationRing.maximalIdeal A).valuation L
  -- Its valuation subring is `A` itself.
  have hv : v.valuationSubring = A := by
    ext x
    rw [Valuation.mem_valuationSubring_iff]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := ↥A) (K := L) h
      exact ha ▸ a.2
    · intro hx
      have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
        (K := L) (IsDiscreteValuationRing.maximalIdeal A) ⟨x, hx⟩
      simpa using this
  -- The restriction of `v` to `E`, and its valuation ring `A ∩ E`.
  let w : Valuation E (WithZero (Multiplicative ℤ)) := v.comap (algebraMap E L)
  have hw : w.valuationSubring = A.comap (algebraMap E L) := by
    ext x
    simp only [w, Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      ValuationSubring.mem_comap]
    rw [← hv, Valuation.mem_valuationSubring_iff]
  rw [← hw]
  by_cases h : w.IsNontrivial
  · -- Nontrivial restriction: `w.valuationSubring` is a discrete valuation ring, hence Noetherian.
    haveI := h
    haveI : IsDiscreteValuationRing ↥w.valuationSubring := inferInstance
    infer_instance
  · -- Trivial restriction: `A ∩ E = ⊤` is a field, hence Noetherian.
    have htop : w.valuationSubring = ⊤ := (Valuation.valuationSubring_eq_top_iff w).mpr h
    rw [htop]
    infer_instance

theorem isNoetherianRing_restrictRing {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsGalois K L] [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤) :
    IsNoetherianRing ↥(NK.RamificationDeep.restrictRing A (NK.RamificationDeep.inertiaField (K := K) A)) :=
  isNoetherianRing_comap_algebraMap (E := ↥(inertiaField (K := K) A)) A

end NK.RamificationDeep
