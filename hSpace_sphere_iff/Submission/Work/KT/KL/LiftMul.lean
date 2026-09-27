import Mathlib
import Submission.Work.KT.Fund.kappa_const

namespace Work.KT.KL

/-! ## Elementary matrix identities over a commutative semiring

The product `(A + c • B) * (A + d • B)` of two "lifts" of orthogonal idempotents `A`, `B` with
`A + B = 1` is `A + (c * d) • B`: the cross terms vanish because `A * B = B * A = 0`, and the
scalars are central.  These are the algebraic core of the computation. -/

/-- Scalar multiplication in a matrix algebra over a commutative semiring: the scalars commute
with the product and can be collected. -/
lemma smul_mul_smul_mat {R : Type*} [CommSemiring R] {n : ℕ} (c d : R)
    (M N : Matrix (Fin n) (Fin n) R) :
    (c • M) * (d • N) = (c * d) • (M * N) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-- The product of the two lifts `A + c • B` and `A + d • B` of orthogonal idempotents
`A`, `B` summing to `1` is `A + (c * d) • B`. -/
lemma lift_mul_generic {R : Type*} [CommSemiring R] {n : ℕ} (c d : R)
    (A B : Matrix (Fin n) (Fin n) R) (hA : A * A = A) (hB : B * B = B)
    (_hsum : A + B = 1) (hAB : A * B = 0) (hBA : B * A = 0) :
    (A + c • B) * (A + d • B) = A + (c * d) • B := by
  have h1 : (c • B) * A = 0 := by rw [Algebra.smul_mul_assoc, hBA, smul_zero]
  have h2 : A * (d • B) = 0 := by rw [Algebra.mul_smul_comm, hAB, smul_zero]
  have h3 : (c • B) * (d • B) = (c * d) • B := by rw [smul_mul_smul_mat, hB]
  calc (A + c • B) * (A + d • B)
      = (A * A + (c • B) * A) + (A * (d • B) + (c • B) * (d • B)) := by
        rw [mul_add, add_mul, add_mul]
    _ = A + (c * d) • B := by rw [h1, h2, h3, hA]; simp

/-- If moreover `c * d = 1`, the two lifts are inverse to each other. -/
lemma lift_mul_generic_one {R : Type*} [CommSemiring R] {n : ℕ} (c d : R)
    (A B : Matrix (Fin n) (Fin n) R) (hA : A * A = A) (hB : B * B = B)
    (hsum : A + B = 1) (hAB : A * B = 0) (hBA : B * A = 0) (hcd : c * d = 1) :
    (A + c • B) * (A + d • B) = 1 := by
  rw [lift_mul_generic c d A B hA hB hsum hAB hBA, hcd, one_smul, hsum]

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## `pullMat` as a ring homomorphism on square matrices -/

/-- `Fund.pullMat` is entrywise application of the ring homomorphism `KC.sphHom X`, hence a ring
homomorphism on matrices. -/
lemma pullMat_eq_mapMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X,ℂ)) :
    Work.KT.Fund.pullMat X M = (Work.KT.Fund.KC.sphHom X).mapMatrix M := by
  rw [RingHom.mapMatrix_apply, Work.KT.Fund.KC.pullMat_eq_map]

lemma pullMat_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) C(X,ℂ)) :
    Work.KT.Fund.pullMat X (M * N) = Work.KT.Fund.pullMat X M * Work.KT.Fund.pullMat X N := by
  rw [pullMat_eq_mapMatrix X, pullMat_eq_mapMatrix X M, pullMat_eq_mapMatrix X N, map_mul]

lemma pullMat_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) C(X,ℂ)) :
    Work.KT.Fund.pullMat X (M + N) = Work.KT.Fund.pullMat X M + Work.KT.Fund.pullMat X N := by
  rw [pullMat_eq_mapMatrix X, pullMat_eq_mapMatrix X M, pullMat_eq_mapMatrix X N, map_add]

lemma pullMat_one {n : ℕ} :
    Work.KT.Fund.pullMat X (1 : Matrix (Fin n) (Fin n) C(X,ℂ)) = 1 := by
  rw [pullMat_eq_mapMatrix X, map_one]

lemma pullMat_zero {n : ℕ} :
    Work.KT.Fund.pullMat X (0 : Matrix (Fin n) (Fin n) C(X,ℂ)) = 0 := by
  rw [pullMat_eq_mapMatrix X, map_zero]

/-- **The lift of `(A + zB)⁻¹` is the inverse unit.**

For orthogonal idempotents `A`, `B` with `A + B = 1` over `C(X, ℂ)`, the boundary value of the
lower lift `A + ζ̄B` (i.e. `pullMat A + z⁻¹ • pullMat B`) is the inverse of the boundary value
`pullMat A + z • pullMat B` of the upper lift `A + ζB`.

Route: `pullMat` is multiplicative (`Work.KT.Fund.KC.pullMat_eq_map` and `Matrix.map_mul`);
expand the product; the scalar factors `z`, `z⁻¹` are central and `z * z⁻¹ = 1`
(`Units.mul_inv`); then use `A*A = A`, `A*B = B*A = 0`, `B*B = B`, `A + B = 1` and
`pullMat 1 = 1`.  (`hBA` is implied by `hsum`, `hB`, `hAB` but is convenient to keep.) -/
theorem LiftMul (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ))
    (hA : A * A = A) (hB : B * B = B) (hsum : A + B = 1) (hAB : A * B = 0)
    (hBA : B * A = 0) :
    (Work.KT.Fund.pullMat X A + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X B)
      * (Work.KT.Fund.pullMat X A
          + (↑((Work.KT.zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X B) = 1 := by
  have hA' : Work.KT.Fund.pullMat X A * Work.KT.Fund.pullMat X A
      = Work.KT.Fund.pullMat X A := by
    rw [← pullMat_mul X, hA]
  have hB' : Work.KT.Fund.pullMat X B * Work.KT.Fund.pullMat X B
      = Work.KT.Fund.pullMat X B := by
    rw [← pullMat_mul X, hB]
  have hsum' : Work.KT.Fund.pullMat X A + Work.KT.Fund.pullMat X B = 1 := by
    rw [← pullMat_add X, hsum, pullMat_one X]
  have hAB' : Work.KT.Fund.pullMat X A * Work.KT.Fund.pullMat X B = 0 := by
    rw [← pullMat_mul X, hAB, pullMat_zero X]
  have hBA' : Work.KT.Fund.pullMat X B * Work.KT.Fund.pullMat X A = 0 := by
    rw [← pullMat_mul X, hBA, pullMat_zero X]
  have hcd : (↑(Work.KT.zUnit X) : C(X × Sph ℂ, ℂ)) * ↑((Work.KT.zUnit X)⁻¹) = 1 :=
    Units.mul_inv (Work.KT.zUnit X)
  exact lift_mul_generic_one (R := C(X × Sph ℂ, ℂ)) (n := n)
    (↑(Work.KT.zUnit X)) (↑((Work.KT.zUnit X)⁻¹))
    (Work.KT.Fund.pullMat X A) (Work.KT.Fund.pullMat X B)
    hA' hB' hsum' hAB' hBA' hcd

end Work.KT.KL
