import Mathlib
import Submission.Work.Defs.Basic

/-!
# Adjoining `i` to a field (paper Proposition 3.8, Step 4)

This file sets up the vocabulary for the last step of the class-field tower of
*Planar Point Sets with Many Unit Distances* (Erdős's unit-distance conjecture is false):
given a totally real number field `L`, we form `K = L(i) = L[X] / (X ^ 2 + 1)`, the
quadratic extension of `L` obtained by adjoining a square root of `-1`.

## Main definitions

* `Work.Tower.CMAdjoin.sqAddOne L`: the polynomial `X ^ 2 + 1 ∈ L[X]`.
* `Work.Tower.CMAdjoin.cmAdjoin L`: the field `L(i)`, presented as `AdjoinRoot (X ^ 2 + 1)`.
* `Work.Tower.CMAdjoin.iota L`: the class of `X`, i.e. the distinguished square root of `-1`.
* `Work.Tower.CMAdjoin.iotaInt L`: `iota` as an element of the ring of integers `𝓞 (L(i))`.
* `Work.Tower.CMAdjoin.iOrder L`: the order `𝓞 L[i] ⊆ 𝓞 (L(i))`.

## Main results

* `Work.Tower.CMAdjoin.sqAddOne_irreducible`: `X ^ 2 + 1` is irreducible over a totally
  real number field.
* `Work.Tower.CMAdjoin.iota_sq`: `iota ^ 2 = -1`.
* `Work.Tower.CMAdjoin.isIntegral_iota`, `Work.Tower.CMAdjoin.isUnit_iotaInt`.

-/

open Polynomial
open NumberField

open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace CMAdjoin

/-! ## The polynomial `X ^ 2 + 1` -/

/-- The polynomial `X ^ 2 + 1` over a commutative semiring `L`. -/
noncomputable def sqAddOne (L : Type*) [CommSemiring L] : L[X] := Polynomial.X ^ 2 + 1

theorem sqAddOne_eq (L : Type*) [CommSemiring L] : sqAddOne L = Polynomial.X ^ 2 + 1 := rfl

theorem sqAddOne_monic (L : Type*) [CommSemiring L] : (sqAddOne L).Monic := by
  rw [sqAddOne_eq, show (1 : L[X]) = C 1 from rfl]
  exact monic_X_pow_add_C (1 : L) (by norm_num)

theorem sqAddOne_natDegree (L : Type*) [CommSemiring L] [Nontrivial L] :
    (sqAddOne L).natDegree = 2 := by
  rw [sqAddOne_eq, show (1 : L[X]) = C 1 from rfl]
  exact natDegree_X_pow_add_C

theorem sqAddOne_ne_zero (L : Type*) [CommSemiring L] [Nontrivial L] : sqAddOne L ≠ 0 :=
  (sqAddOne_monic L).ne_zero

theorem sqAddOne_degree_ne_zero (L : Type*) [CommSemiring L] [Nontrivial L] :
    (sqAddOne L).degree ≠ 0 := by
  rw [degree_eq_natDegree (sqAddOne_ne_zero L), sqAddOne_natDegree L]
  norm_num

theorem sqAddOne_derivative (L : Type*) [CommSemiring L] : derivative (sqAddOne L) = C 2 * X := by
  rw [sqAddOne_eq, show (1 : L[X]) = C 1 from rfl, derivative_add, derivative_X_pow,
    derivative_C, add_zero]
  norm_num

theorem sqAddOne_eval (L : Type*) [CommSemiring L] (x : L) : (sqAddOne L).eval x = x ^ 2 + 1 := by
  rw [sqAddOne_eq, eval_add, eval_pow, eval_X, eval_one]

/-! ## Irreducibility -/

/-- Over a field admitting a ring homomorphism into `ℝ`, the polynomial `X ^ 2 + 1` has no
root. -/
theorem not_isRoot_sqAddOne (L : Type*) [Field L] (φ : L →+* ℝ) (x : L) :
    ¬ (sqAddOne L).IsRoot x := by
  rw [IsRoot.def, sqAddOne_eval]
  intro h
  have h' : (φ x) ^ 2 + 1 = 0 := by
    simpa using congr_arg φ h
  nlinarith [sq_nonneg (φ x)]

/-- Over a field admitting a ring homomorphism into `ℝ`, the polynomial `X ^ 2 + 1` is
irreducible. -/
theorem sqAddOne_irreducible_of_ringHom (L : Type*) [Field L] (φ : L →+* ℝ) :
    Irreducible (sqAddOne L) := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ (not_isRoot_sqAddOne L φ)
  rw [sqAddOne_natDegree L]
  norm_num

/-- A totally real number field admits a ring homomorphism into `ℝ`: an infinite place is
real, hence given by an embedding into `ℝ`. -/
theorem exists_ringHom_real (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    Nonempty (L →+* ℝ) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  obtain ⟨_φ, hφ, -⟩ := (NumberField.IsTotallyReal.isReal w : InfinitePlace.IsReal w)
  exact ⟨hφ.embedding⟩

/-- `-1` is not a square in a totally real number field. -/
theorem not_isSquare_neg_one (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] : ¬ IsSquare (-1 : L) := by
  obtain ⟨ψ⟩ := exists_ringHom_real L
  rintro ⟨y, hy⟩
  have h : (ψ y) * (ψ y) = -1 := by
    simpa using (congr_arg ψ hy).symm
  have h2 : (ψ y) ^ 2 = -1 := by rw [← h, sq]
  nlinarith [sq_nonneg (ψ y)]

/-- `X ^ 2 + 1` is irreducible over a totally real number field. -/
theorem sqAddOne_irreducible (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] : Irreducible (sqAddOne L) := by
  classical
  exact sqAddOne_irreducible_of_ringHom L (Classical.choice (exists_ringHom_real L))

instance (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    Fact (Irreducible (sqAddOne L)) :=
  ⟨sqAddOne_irreducible L⟩

/-! ## The field `L(i)` -/

/-- The field `L(i)`, obtained by adjoining a square root of `-1` to `L`,
presented as `L[X] / (X ^ 2 + 1)`. -/
abbrev cmAdjoin (L : Type*) [Field L] : Type _ := AdjoinRoot (sqAddOne L)

/-- The distinguished element `i` of `L(i)`: the class of `X`. -/
noncomputable def iota (L : Type*) [Field L] : cmAdjoin L := AdjoinRoot.root (sqAddOne L)

theorem algebraMap_injective (L : Type*) [Field L] :
    Function.Injective (algebraMap L (cmAdjoin L)) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero (sqAddOne_degree_ne_zero L)

theorem iota_sq_add_one (L : Type*) [Field L] : iota L ^ 2 + 1 = 0 := by
  have h : (AdjoinRoot.mk (sqAddOne L)) (Polynomial.X ^ 2 + 1) = 0 := by
    rw [← sqAddOne_eq]
    exact AdjoinRoot.mk_self
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  simpa [iota] using h

theorem iota_sq (L : Type*) [Field L] : iota L ^ 2 = -1 := by
  have h := iota_sq_add_one L
  rw [eq_neg_iff_add_eq_zero]
  exact h

theorem iota_ne_zero (L : Type*) [Field L] : iota L ≠ 0 := by
  haveI : Nontrivial (cmAdjoin L) :=
    AdjoinRoot.nontrivial (f := sqAddOne L) (sqAddOne_degree_ne_zero L)
  intro h
  have h2 : (1 : cmAdjoin L) = 0 := by
    have h3 := iota_sq L
    rw [h] at h3
    simpa using h3
  exact (zero_ne_one (α := cmAdjoin L)) h2.symm

theorem iota_notMem_range (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] : iota L ∉ Set.range (algebraMap L (cmAdjoin L)) := by
  rintro ⟨x, hx⟩
  refine not_isSquare_neg_one L ⟨x, ?_⟩
  have h' : x ^ 2 = -1 := by
    apply algebraMap_injective L
    rw [map_pow, hx, iota_sq, map_neg, map_one]
  rw [← h', sq]

/-- The `L`-algebra generated by `iota` is the whole field, since `K = L(i)`. -/
theorem adjoin_iota_eq_top (L : Type*) [Field L] :
    Algebra.adjoin L ({iota L} : Set (cmAdjoin L)) = ⊤ := by
  simpa [iota] using AdjoinRoot.adjoinRoot_eq_top (f := sqAddOne L)

/-! ## Integrality of `iota` -/

/-- `iota` is integral over `ℤ` (it is a root of the monic polynomial `X ^ 2 + 1`). -/
theorem isIntegral_iota (L : Type*) [Field L] : IsIntegral ℤ (iota L) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [iota_sq]
  exact IsIntegral.neg isIntegral_one

/-- The element `iota` of `L(i)`, as an element of the ring of integers. -/
noncomputable def iotaInt (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] : 𝓞 (cmAdjoin L) := ⟨iota L, isIntegral_iota L⟩

theorem iotaInt_coe (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    ((iotaInt L : 𝓞 (cmAdjoin L)) : cmAdjoin L) = iota L := rfl

theorem iotaInt_sq (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    iotaInt L ^ 2 = -1 := by
  apply Subtype.coe_injective
  change ((iotaInt L : 𝓞 (cmAdjoin L)) : cmAdjoin L) ^ 2 = (-1 : cmAdjoin L)
  rw [iotaInt_coe, iota_sq]

/-- `iota` is a unit of `𝓞 (L(i))`: its inverse is `-iota`. -/
theorem isUnit_iotaInt (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    IsUnit (iotaInt L) := by
  refine ⟨⟨iotaInt L, -iotaInt L, ?_, ?_⟩, rfl⟩
  · rw [mul_neg, ← sq, iotaInt_sq]; simp
  · rw [neg_mul, ← sq, iotaInt_sq]; simp

/-- The `𝓞 L`-order `𝓞 L[i] ⊆ 𝓞 (L(i))`. -/
noncomputable def iOrder (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] : Subalgebra (𝓞 L) (𝓞 (cmAdjoin L)) :=
  Algebra.adjoin (𝓞 L) {iotaInt L}

end CMAdjoin
end Tower
end Work
