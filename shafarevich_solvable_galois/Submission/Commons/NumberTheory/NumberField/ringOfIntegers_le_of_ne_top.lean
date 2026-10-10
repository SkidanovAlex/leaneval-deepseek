import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

/-- **Every valuation subring of a number field contains the ring of integers.**

The key point is that the image of `ℤ` in `F` is contained in *every* subring of `F` (it is the
prime subring), and a valuation subring is integrally closed in `F`.  Since `𝓞 F` is integral over
`ℤ`, it is integral over any valuation subring `C`, hence contained in it.

The hypothesis `C ≠ ⊤` of `ringOfIntegers_le_of_ne_top` is therefore not needed; it is kept in the
requested statement because that is how it is used. -/
theorem ringOfIntegers_le_of_valuationSubring {F : Type*} [Field F] [NumberField F]
    (C : ValuationSubring F) : ∀ x : NumberField.RingOfIntegers F,
      algebraMap (NumberField.RingOfIntegers F) F x ∈ C := by
  -- Reduce to the case of the base field `ℚ`: it suffices to know that the image of the ring of
  -- integers of `ℚ` (which is `ℤ`) lies in `C`, since `𝓞 F` is integral over `ℤ`.
  refine ringOfIntegers_le_valuationSubring (K := ℚ) (L := F) C ?_
  intro x
  -- `𝓞 ℚ ≃+* ℤ`, and the image of any integer is in the prime subring of `F`, hence in `C`.
  rw [← Rat.ringOfIntegersEquiv_apply_coe, map_intCast]
  exact intCast_mem C.toSubring _

/-- **Every nontrivial valuation ring of a number field contains the ring of integers.**

Let `F` be a number field and `C : ValuationSubring F` a proper valuation subring.  Then the
image of `𝓞 F` lies in `C`.

Suggested route: `C ∩ ℚ` is a valuation subring of `ℚ`; if it were all of `ℚ` then the
valuation would be trivial on `ℚ`, hence (by `Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top`,
since `F / ℚ` is algebraic) trivial on `F`, contradicting `C ≠ ⊤`.  So `C ∩ ℚ` is a nontrivial
valuation subring of `ℚ`; its maximal ideal `𝔪` meets `ℤ` nontrivially (otherwise every nonzero
integer is a unit of `C ∩ ℚ`, so `ℚ ⊆ C`), hence `𝔪 ∩ ℤ = qℤ` for a prime `q`, and every
integer is a product of a power of `q` (in `C`) with an integer coprime to `q` (a unit of `C`).
Finally `𝓞 F` is integral over `ℤ ⊆ C` and `C` is integrally closed in `F`. -/
theorem ringOfIntegers_le_of_ne_top {F : Type*} [Field F] [NumberField F] (C : ValuationSubring F)
    (hC : C ≠ ⊤) : ∀ x : NumberField.RingOfIntegers F,
      algebraMap (NumberField.RingOfIntegers F) F x ∈ C := by
  -- the hypothesis `hC` is not needed; the result holds for *every* valuation subring
  have _ := hC
  exact ringOfIntegers_le_of_valuationSubring C

end Commons.NumberTheory.NumberField
