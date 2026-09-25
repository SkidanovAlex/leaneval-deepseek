import Submission.Work.Tower.CMAdjoin.Defs

/-!
# Basic structure of `L(i)` for a totally real number field `L`

This file proves that for a totally real number field `L` the field `K = L(i)` of
`Submission.Work.Tower.CMAdjoin.Defs` is a number field that is a quadratic extension of `L`
and in fact a CM-field.

## Main results

* `Work.Tower.CMAdjoin.finrank_cmAdjoin`: `[L(i) : L] = 2`.
* `Work.Tower.CMAdjoin.finrank_cmAdjoin_rat`: `[L(i) : ℚ] = 2 * [L : ℚ]`.
* `Work.Tower.CMAdjoin.numberField`: `L(i)` is a number field.
* `Work.Tower.CMAdjoin.isTotallyComplex`: `L(i)` is totally complex.
* `Work.Tower.CMAdjoin.isCMField`: `L(i)` is a CM-field.

-/

open Polynomial
open NumberField

open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace CMAdjoin

/-! ## Degree -/

/-- `L(i)` is a quadratic extension of `L`. -/
theorem finrank_cmAdjoin (L : Type*) [Field L] : Module.finrank L (cmAdjoin L) = 2 := by
  have h := PowerBasis.finrank (AdjoinRoot.powerBasis (f := sqAddOne L) (sqAddOne_ne_zero L))
  rw [h]
  exact sqAddOne_natDegree L

instance instQuadraticExtension (L : Type*) [Field L] :
    Algebra.IsQuadraticExtension L (cmAdjoin L) :=
  ⟨finrank_cmAdjoin L⟩

instance moduleFinite_cmAdjoin (L : Type*) [Field L] : Module.Finite L (cmAdjoin L) :=
  Module.Finite.of_basis
    (AdjoinRoot.powerBasis (f := sqAddOne L) (sqAddOne_ne_zero L)).basis

instance charZero_cmAdjoin (L : Type*) [Field L] [CharZero L] : CharZero (cmAdjoin L) :=
  charZero_of_injective_algebraMap (algebraMap_injective L)

instance moduleFinite_rat (L : Type*) [Field L] [NumberField L] :
    Module.Finite ℚ (cmAdjoin L) :=
  Module.Finite.trans L (cmAdjoin L)

instance numberField (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    NumberField (cmAdjoin L) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- The `𝓞 L`-algebra structure on `𝓞 (L(i))` is compatible with the inclusions into `L(i)`. -/
instance instIsScalarTowerRingOfIntegers (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] :
    IsScalarTower (𝓞 L) (𝓞 (cmAdjoin L)) (cmAdjoin L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- `[L(i) : ℚ] = 2 * [L : ℚ]`. -/
theorem finrank_cmAdjoin_rat (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] :
    Module.finrank ℚ (cmAdjoin L) = 2 * Module.finrank ℚ L := by
  have h := Module.finrank_mul_finrank ℚ L (cmAdjoin L)
  rw [finrank_cmAdjoin L] at h
  rw [mul_comm] at h
  exact h.symm

/-! ## `L(i)` is totally complex -/

/-- `iota` has no real value under any real embedding: this is what makes `L(i)` totally
complex. -/
theorem not_complexEmbedding_isReal (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] (φ : cmAdjoin L →+* ℂ)
    (hφ : ComplexEmbedding.IsReal φ) : False := by
  have hc : ((ComplexEmbedding.IsReal.embedding hφ (iota L) : ℝ) : ℂ) = φ (iota L) :=
    ComplexEmbedding.IsReal.coe_embedding_apply hφ (iota L)
  have hw : (φ (iota L)) ^ 2 = -1 := by
    rw [← map_pow, iota_sq, map_neg, map_one]
  have h1 : (ComplexEmbedding.IsReal.embedding hφ (iota L)) ^ 2 = -1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow, hc, hw]
    simp
  nlinarith [sq_nonneg (ComplexEmbedding.IsReal.embedding hφ (iota L))]

/-- `L(i)` is totally complex. -/
instance isTotallyComplex (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] : IsTotallyComplex (cmAdjoin L) where
  isComplex w := ⟨w.embedding, not_complexEmbedding_isReal L w.embedding, w.mk_embedding⟩

/-! ## `L(i)` is a CM field -/

/-- `L(i)` is a CM-field, being a totally complex quadratic extension of the totally real
field `L`. -/
instance isCMField (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    IsCMField (cmAdjoin L) :=
  IsCMField.ofCMExtension L (cmAdjoin L)

end CMAdjoin
end Tower
end Work
