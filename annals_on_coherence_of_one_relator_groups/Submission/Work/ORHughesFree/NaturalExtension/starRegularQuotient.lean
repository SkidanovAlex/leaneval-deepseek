import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.matrixQuotientDefs
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.exists_isRelativeInverse
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.StarRegular.isStarRegular_of_ringEquiv
import Submission.Work.ORHughesFree.NaturalExtension.matrixQuotStarEquiv

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ORHughesFree.NaturalExtension

open Work.ORHughesFree

/-! ## Quotients of `∗`-regular rings

The main result of this file is that a two-sided ideal of a positive definite `∗`-regular ring
that is closed under the involution has a positive definite `∗`-regular quotient.  The key
ingredient is the elementary observation that the involution of a `∗`-regular ring descends to
a *proper* involution on every quotient: if `x ∗ x` vanishes in the quotient, then so does
`x`, because in a `∗`-regular ring `x` can be recovered from `x ∗ x` by multiplication with the
relative inverse. -/

/-- The ring isomorphism `Mat₁(R) ≃+* R` sending a `1 × 1` matrix to its only entry. -/
def matrixFinOneRingEquiv (R : Type*) [Ring R] : Matrix (Fin 1) (Fin 1) R ≃+* R where
  toFun A := A 0 0
  invFun r := fun _ _ => r
  left_inv A := by ext i j; fin_cases i; fin_cases j; rfl
  right_inv r := rfl
  map_mul' A B := by simp [Matrix.mul_apply]
  map_add' A B := by simp [Matrix.add_apply]

/-- A positive definite `∗`-regular ring is `∗`-regular: this is the case `n = 1` of the
defining condition, transported along `Mat₁(R) ≃+* R`. -/
theorem isStarRegular_of_isPositiveDefiniteStarRegular {R : Type*} [Ring R] [StarRing R]
    (hpos : IsPositiveDefiniteStarRegular R) : IsStarRegular R :=
  StarRegular.isStarRegular_of_ringEquiv (matrixFinOneRingEquiv R)
    (fun A => by
      show (star A) 0 0 = star (A 0 0)
      rw [Matrix.star_apply])
    (hpos 1)

/-- A quotient of a `∗`-regular ring by a `∗`-closed two-sided ideal is `∗`-regular.

Regularity is immediate from regularity of the ring.  For properness, suppose that
`star x * x = 0` in `S ⧸ J` and lift `x` to `a ∈ S`.  Then `star a * a ∈ J`, and if
`b` is a relative inverse of `a` (which exists by Berberian's theorem, `exists_isRelativeInverse`)
then `star a = (star a * a) * b` because `a = (a * b) * a` and `star (a * b) = a * b`.  Hence
`star a ∈ J`, and then `a = star (star a) ∈ J`, so `x = 0`. -/
theorem isStarRegular_quotient {S : Type*} [Ring S] [StarRing S] (hS : IsStarRegular S)
    (J : Ideal S) [J.IsTwoSided] (hJ : ∀ x ∈ J, star x ∈ J) :
    @IsStarRegular (S ⧸ J) _ (starRingQuotient J hJ) := by
  letI := starRingQuotient J hJ
  refine ⟨⟨fun y => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, hb⟩ := hS.vonNeumannRegular.exists_mul_inverse a
    exact ⟨Ideal.Quotient.mk J b, by rw [← map_mul, ← map_mul, hb]⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy' : starQuot J (Ideal.Quotient.mk J a) * Ideal.Quotient.mk J a = 0 := hy
    rw [starQuot_mk J hJ a, ← map_mul] at hy'
    have hpa : star a * a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hy'
    obtain ⟨b, hb⟩ := StarRegular.exists_isRelativeInverse a
    have hstar : star a = (star a * a) * b := by
      calc star a = star ((a * b) * a) := by rw [hb.left]
        _ = star a * star (a * b) := by rw [star_mul]
        _ = star a * (a * b) := by rw [hb.star_left]
        _ = (star a * a) * b := by rw [mul_assoc]
    have hsa : star a ∈ J := by
      rw [hstar]
      exact Ideal.IsTwoSided.mul_mem_of_left b hpa
    have ha : a ∈ J := by
      have h := hJ (star a) hsa
      rwa [star_star] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-! ## The involution on matrices modulo an entrywise ideal -/

/-- The entrywise quotient map on matrices commutes with the conjugate-transpose involutions,
where on the target the entries are pushed forward by `starQuot`. -/
theorem mapMatrix_quotient_star {R : Type*} [Ring R] [StarRing R] (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ x ∈ I, star x ∈ I) (n : ℕ) (M : Matrix (Fin n) (Fin n) R) :
    matrixQuotMap I n (star M) =
      Matrix.of (fun i j => starQuot I (matrixQuotMap I n M j i)) := by
  ext i j
  simp only [matrixQuotMap, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply,
    Matrix.of_apply]
  exact (starQuot_mk I hI (M j i)).symm

/-- The element `0` of `R ⧸ I` is fixed by the descended involution. -/
theorem starQuot_zero {R : Type*} [Ring R] [StarRing R] (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ x ∈ I, star x ∈ I) : starQuot I (0 : R ⧸ I) = 0 := by
  letI := starRingQuotient I hI
  rw [show starQuot I (0 : R ⧸ I) = star (0 : R ⧸ I) from rfl, star_zero]

/-- The kernel of the entrywise quotient map on matrices is closed under the involution. -/
theorem ker_mapMatrix_star {R : Type*} [Ring R] [StarRing R] (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ x ∈ I, star x ∈ I) (n : ℕ)
    {x : Matrix (Fin n) (Fin n) R} (hx : x ∈ RingHom.ker (matrixQuotMap I n)) :
    star x ∈ RingHom.ker (matrixQuotMap I n) := by
  rw [RingHom.mem_ker] at hx ⊢
  rw [mapMatrix_quotient_star I hI n x, hx]
  ext i j
  simp only [Matrix.zero_apply]
  exact starQuot_zero I hI

/-- A quotient of a positive definite `∗`-regular ring by a `∗`-closed two-sided ideal is again
positive definite `∗`-regular.

The first conjunct is `isStarRegular_quotient`.  For the second, `Matₙ(R ⧸ I)` is the quotient
of the `∗`-regular ring `Matₙ(R)` by the kernel of the entrywise quotient map, which is a
`∗`-closed two-sided ideal; the general quotient lemma applies to `Matₙ(R)`, and the result is
transported across the star-compatible isomorphism `matrixQuotStarEquiv`. -/
theorem starRegularQuotient {R : Type} [Ring R] [StarRing R] (hpos : IsPositiveDefiniteStarRegular R)
    (I : Ideal R) [I.IsTwoSided] (hI : ∀ x ∈ I, star x ∈ I) :
    @IsStarRegular (R ⧸ I) _ (starRingQuotient I hI) ∧
    @IsPositiveDefiniteStarRegular (R ⧸ I) _ (starRingQuotient I hI) := by
  have hSR : IsStarRegular R := isStarRegular_of_isPositiveDefiniteStarRegular hpos
  refine ⟨isStarRegular_quotient hSR I hI, ?_⟩
  intro n
  letI : StarRing (R ⧸ I) := starRingQuotient I hI
  have hJ : ∀ x ∈ RingHom.ker (matrixQuotMap I n), star x ∈ RingHom.ker (matrixQuotMap I n) :=
    fun x hx => ker_mapMatrix_star I hI n hx
  letI : StarRing (Matrix (Fin n) (Fin n) R ⧸ RingHom.ker (matrixQuotMap I n)) :=
    starRingQuotient (RingHom.ker (matrixQuotMap I n)) hJ
  obtain ⟨e, _he_mk, he_star⟩ := matrixQuotStarEquiv I hI n
  have hsrc : @IsStarRegular (Matrix (Fin n) (Fin n) R ⧸ RingHom.ker (matrixQuotMap I n)) _
      (starRingQuotient (RingHom.ker (matrixQuotMap I n)) hJ) :=
    isStarRegular_quotient (hpos n) (RingHom.ker (matrixQuotMap I n)) hJ
  exact StarRegular.isStarRegular_of_ringEquiv e (fun x => by
    change e (starQuot (RingHom.ker (matrixQuotMap I n)) x) =
      Matrix.of (fun i j => starQuot I (e x j i))
    exact he_star x) hsrc

end Work.ORHughesFree.NaturalExtension
