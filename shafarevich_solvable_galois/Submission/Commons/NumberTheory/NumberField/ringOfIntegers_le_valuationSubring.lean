import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField


/-- If a valuation subring `A` of a finite extension `L / K` of number fields contains the
image of the ring of integers of `K`, then it contains the image of the ring of integers of
`L`.  Indeed `𝓞 L` is integral over `𝓞 K`, and `A` is integrally closed in `L`. -/
theorem ringOfIntegers_le_valuationSubring {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (A : ValuationSubring L)
    (hA : ∀ x : NumberField.RingOfIntegers K,
      algebraMap K L (algebraMap (NumberField.RingOfIntegers K) K x) ∈ A) :
    ∀ x : NumberField.RingOfIntegers L,
      algebraMap (NumberField.RingOfIntegers L) L x ∈ A := by
  -- The embedding `𝓞 K →+* A` given by the hypothesis, with values in `L`.
  let φ : NumberField.RingOfIntegers K →+* A :=
    { toFun := fun a => ⟨algebraMap (NumberField.RingOfIntegers K) L a, hA a⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  have hcomp : (algebraMap A L).comp φ
      = (RingHom.id L).comp (algebraMap (NumberField.RingOfIntegers K) L) := by
    ext a; rfl
  intro x
  -- `algebraMap (𝓞 L) L x` is integral over `𝓞 K`.
  have hx : IsIntegral (NumberField.RingOfIntegers K)
      (algebraMap (NumberField.RingOfIntegers L) L x) :=
    (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers L)
      (R := NumberField.RingOfIntegers K) (B := L)).mpr ⟨x, rfl⟩
  -- hence integral over `A`.
  have hxA : IsIntegral A (algebraMap (NumberField.RingOfIntegers L) L x) :=
    IsIntegral.map_of_comp_eq φ (RingHom.id L) hcomp hx
  -- and `A` is integrally closed in `L`.
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := A) (R := A) (B := L)).mp hxA
  rw [← ha]
  exact a.2

end Commons.NumberTheory.NumberField