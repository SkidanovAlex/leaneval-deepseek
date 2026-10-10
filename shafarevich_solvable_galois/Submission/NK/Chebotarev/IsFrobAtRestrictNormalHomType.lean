import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.Chebotarev.GalRestrictCompat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Descent of Frobenius elements to a normal subfield, for bare field types

Let `K ⊆ E ⊆ M` be a tower of number fields with `E/K` normal and `M/K` finite Galois, and let
`P` be a prime of `𝓞 M`.  If `ρ ∈ Gal(M/K)` is an arithmetic Frobenius element at `P`, then its
restriction `ρ|_E ∈ Gal(E/K)` is an arithmetic Frobenius element at the prime `P ∩ 𝓞 E` of `𝓞 E`.

This is the same statement as `NK.Chebotarev.IsFrobAtRestrictNormalHom` (where the intermediate
field is given as an `IntermediateField K M`), but here `E` is an arbitrary type equipped with
`Algebra K E`, `Algebra E M` and `IsScalarTower K E M`.  This matters in applications where the
algebra structure `↥E → ↥M` is *not* the canonical instance supplied by the intermediate field
structure (for instance when it is built from `Subsemiring.inclusion`), so that the `𝓞`-level
algebra `𝓞 E → 𝓞 M` is the one induced by the given `Algebra E M` rather than by the inclusion of
subalgebras.

The two ingredients are the same as in the intermediate-field case:

* the compatibility `galRestrict_restrictNormalHom_type` of `galRestrict` with the restriction
  `Gal(M/K) → Gal(E/K)`, which for bare types is proved from
  `algebraMap_galRestrict_apply` and `AlgEquiv.restrictNormal_commutes`;
* the transitivity of contraction of ideals (`Ideal.under_under`), which makes the exponent
  `#(𝓞 K ⧸ P ∩ 𝓞 E ∩ 𝓞 K) = #(𝓞 K ⧸ P ∩ 𝓞 K)` occurring in the definition of a Frobenius element
  the same for `P` and for `P ∩ 𝓞 E`.

In particular no hypothesis on the prime of `K` below `P` is needed.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField

namespace NK.Chebotarev

open IsDedekindDomain

/-- **The `asIdeal` of the contraction of a prime of `𝓞 M` to a bare intermediate type.**  For a
tower `K ⊆ E ⊆ M` given by bare types, the prime `P.under (𝓞 E)` of `𝓞 E` has underlying ideal the
contraction `Ideal.under (𝓞 E) P.asIdeal` of `P.asIdeal` along `algebraMap (𝓞 E) (𝓞 M)` (this is
`rfl`, recorded here so that the contraction lemmas of `Ideal` become applicable). -/
lemma under_asIdeal_type {E M : Type*} [Field E] [NumberField E] [Field M] [NumberField M]
    [Algebra E M] (P : NK.Chebotarev.PrimeIdeal M) :
    (P.under (NumberField.RingOfIntegers E)).asIdeal
      = Ideal.under (NumberField.RingOfIntegers E) P.asIdeal := rfl

/-- **Compatibility of `galRestrict` with restriction to a normal subfield**, for bare field
types.  For a tower `K ⊆ E ⊆ M` of number fields with `E/K` normal, the element of `𝓞 M` obtained
by applying the automorphism induced by `ρ ∈ Gal(M/K)` to an element of `𝓞 E` only depends on the
restriction `ρ|_E` of `ρ` to `E`.  This is the type-level version of
`NK.Chebotarev.galRestrict_restrictNormalHom`. -/
theorem galRestrict_restrictNormalHom_type {K E M : Type*} [Field K] [NumberField K] [Field E]
    [NumberField E] [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
    [IsScalarTower K E M] [FiniteDimensional K M] [IsGalois K M] [Normal K E]
    (ρ : Gal(M/K)) (x : NumberField.RingOfIntegers E) :
    algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers M)
        ((galRestrict (NumberField.RingOfIntegers K) K E (NumberField.RingOfIntegers E))
          (ρ.restrictNormal E) x) =
      (galRestrict (NumberField.RingOfIntegers K) K M (NumberField.RingOfIntegers M)) ρ
        (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers M) x) := by
  apply NumberField.RingOfIntegers.ext
  -- We compare the images in `M`; the scalar towers `𝓞 E → 𝓞 M → M` and `𝓞 E → E → M` identify
  -- the two `algebraMap`s, `algebraMap_galRestrict_apply` describes both sides as the action of
  -- `ρ` respectively `ρ|_E`, and `AlgEquiv.restrictNormal_commutes` says that these agree.
  calc (algebraMap (𝓞 M) M) (algebraMap (𝓞 E) (𝓞 M)
          (galRestrict (𝓞 K) K E (𝓞 E) (ρ.restrictNormal E) x))
      = algebraMap (𝓞 E) M (galRestrict (𝓞 K) K E (𝓞 E) (ρ.restrictNormal E) x) := by
        rw [IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 M) M]
    _ = algebraMap E M (algebraMap (𝓞 E) E
          (galRestrict (𝓞 K) K E (𝓞 E) (ρ.restrictNormal E) x)) := by
        rw [← IsScalarTower.algebraMap_apply (𝓞 E) E M]
    _ = algebraMap E M ((ρ.restrictNormal E) (algebraMap (𝓞 E) E x)) := by
        rw [algebraMap_galRestrict_apply]
    _ = ρ (algebraMap E M (algebraMap (𝓞 E) E x)) := by
        rw [AlgEquiv.restrictNormal_commutes]
    _ = ρ (algebraMap (𝓞 E) M x) := by
        rw [IsScalarTower.algebraMap_apply (𝓞 E) E M]
    _ = ρ (algebraMap (𝓞 M) M (algebraMap (𝓞 E) (𝓞 M) x)) := by
        rw [← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 M) M]
    _ = algebraMap (𝓞 M) M
          ((galRestrict (𝓞 K) K M (𝓞 M)) ρ (algebraMap (𝓞 E) (𝓞 M) x)) := by
        rw [algebraMap_galRestrict_apply]

/-- **Descent of a Frobenius element to a normal subfield, for bare field types.**  Let `K ⊆ E ⊆ M` be a tower of number fields with `E/K` normal and `M/K` finite Galois.  If `ρ ∈ Gal(M/K)` is an arithmetic Frobenius element at the prime `P` of `𝓞 M`, then its restriction to `E` is an arithmetic Frobenius element at the prime `P ∩ 𝓞 E` of `𝓞 E`.  This is the type-level version of `NK.Chebotarev.IsFrobAtRestrictNormalHom` (where the intermediate field is given as an `IntermediateField K M`); here `E` is an arbitrary type with `Algebra K E`, `Algebra E M`, `IsScalarTower K E M`, `Normal K E`, so that the statement applies when the `Algebra ↥E ↥M` instance is not the canonical one (it is supplied by the caller through `Subsemiring.inclusion`). -/
theorem IsFrobAtRestrictNormalHomType {K E M : Type*} [Field K] [NumberField K] [Field E]
    [NumberField E] [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
    [IsScalarTower K E M] [FiniteDimensional K M] [IsGalois K M] [Normal K E]
    (P : NK.Chebotarev.PrimeIdeal M) (ρ : Gal(M/K))
    (h : NK.Chebotarev.IsFrobAt (K := K) (L := M) P ρ) :
    NK.Chebotarev.IsFrobAt (K := K) (L := E) (P.under (NumberField.RingOfIntegers E))
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E ρ) := by
  -- `AlgEquiv.restrictNormalHom E ρ` is `ρ.restrictNormal E`, definitionally; we put the goal in
  -- that form so that the restriction appears literally.
  change NK.Chebotarev.IsFrobAt (K := K) (L := E)
    (P.under (NumberField.RingOfIntegers E)) (ρ.restrictNormal E)
  intro x
  -- The exponent of the congruence is the cardinality of `𝓞 K ⧸ P ∩ 𝓞 E ∩ 𝓞 K`.
  rw [under_asIdeal_type, Ideal.mem_under, map_sub, map_pow]
  -- Rewrite the goal in the shape in which `galRestrict_restrictNormalHom_type` applies.
  change algebraMap (𝓞 E) (𝓞 M) ((galRestrict (𝓞 K) K E (𝓞 E) (ρ.restrictNormal E)) x) -
      (algebraMap (𝓞 E) (𝓞 M) x) ^
        Nat.card (𝓞 K ⧸ Ideal.under (𝓞 K) (Ideal.under (𝓞 E) P.asIdeal)) ∈ P.asIdeal
  -- The congruence for `ρ|_E` is the congruence for `ρ`, transported along `𝓞 E → 𝓞 M`.
  rw [galRestrict_restrictNormalHom_type ρ x]
  -- Contraction of ideals is transitive, so the exponent is the one for `P`.
  rw [show Ideal.under (𝓞 K) (Ideal.under (𝓞 E) P.asIdeal) = Ideal.under (𝓞 K) P.asIdeal from
    Ideal.under_under P.asIdeal]
  exact h (algebraMap (𝓞 E) (𝓞 M) x)

end NK.Chebotarev
