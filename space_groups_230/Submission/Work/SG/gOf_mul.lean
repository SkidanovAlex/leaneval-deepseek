import Mathlib
import Submission.Work.SG.realize_defs

/-!
# Multiplicativity of the realisation `gOf`

`gOf M A hO w` is the Euclidean motion `x ↦ M A M⁻¹ x + M w` attached to an integer matrix
`A` and a real vector `w` (see `Submission.Work.SG.realize_defs`).  Writing `oConj M A = M A M⁻¹`
for the real conjugate, the composite of two such motions is again of this shape, because

* `(M A M⁻¹)(M B M⁻¹) = M (A B) M⁻¹`  (`M⁻¹ M = 1` cancels the two inner factors), and
* `(M A M⁻¹)(M y) = M (A y)`           (the two factors cancel on a vector of the form `M y`).

On the cocycle level (`τ (A B) = τ A + A τ B + k`, `k ∈ ℤ³`) the resulting translation vector is
`M (τ A + A τ B + k + A m + n − k) = M (τ (A B) + A m + n − k)`, which is exactly the index
suggested by the multiplication of the affine maps.  This is the bookkeeping lemma needed to see
that `(A, n) ↦ gOf M A hO (τ A + n)` is a group homomorphism, hence that the `idxFun` table
used in `exists_realization` is closed under multiplication.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open Matrix

namespace GOfMulAux

/-- Associativity of conjugation: `(M A M⁻¹)(M B M⁻¹) = M (A B) M⁻¹` when `M⁻¹ M = 1`. -/
lemma mul_conj_mul (M A B : RMat) (h : M⁻¹ * M = 1) :
    M * A * M⁻¹ * (M * B * M⁻¹) = M * (A * B) * M⁻¹ := by
  have h1 : M * A * M⁻¹ * (M * B * M⁻¹) = ((M * A) * (M⁻¹ * M)) * (B * M⁻¹) := by
    simp only [Matrix.mul_assoc]
  rw [h1, h, Matrix.mul_one]
  noncomm_ring

/-- Conjugation is multiplicative: `oConj M A * oConj M B = oConj M (A * B)`. -/
lemma oConj_mul (M : RMat) (hM : M.det ≠ 0) (A B : IMat) :
    oConj M A * oConj M B = oConj M (A * B) := by
  have h := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM)
  simp only [oConj, realMat_mul]
  exact mul_conj_mul M (realMat A) (realMat B) h

/-- The two factors of the conjugate cancel against `M`: `oConj M A * M = M * realMat A`. -/
lemma oConj_mul_self (M : RMat) (hM : M.det ≠ 0) (A : IMat) :
    oConj M A * M = M * realMat A := by
  have h := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM)
  have h1 : oConj M A * M = (M * realMat A) * (M⁻¹ * M) := by
    simp only [oConj, Matrix.mul_assoc]
  rw [h1, h, Matrix.mul_one]

/-- The conjugate acts on the image of `M` as `M` acts on the image of `realMat A`:
`(M A M⁻¹)(M y) = M (A y)`. -/
lemma oConj_mulVec_self (M : RMat) (hM : M.det ≠ 0) (A : IMat) (y : Fin 3 → ℝ) :
    oConj M A *ᵥ (M *ᵥ y) = M *ᵥ (realMat A *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, oConj_mul_self M hM A, ← Matrix.mulVec_mulVec]

/-- Integer vectors are additive. -/
lemma intVec_add_aux (a b : Fin 3 → ℤ) : intVec (a + b) = intVec a + intVec b := by
  funext i; simp [intVec]

/-- An integer matrix acts on integer vectors through `realMat`. -/
lemma realMat_mulVec_intVec_aux (A : IMat) (n : Fin 3 → ℤ) :
    realMat A *ᵥ intVec n = intVec (A *ᵥ n) := by
  ext i
  simp only [realMat, intVec, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  rfl

/-- The product of two realised motions:
`gOf M A hOa wA * gOf M B hOb wB = gOf M (A * B) hOab (realMat A *ᵥ wB + wA)`.

Only the *values* of the motions enter, so the orthogonality proofs `hOa`, `hOb`, `hOab` are
irrelevant. -/
lemma gOf_mul_aux (M : RMat) (hM : M.det ≠ 0) (A B : IMat)
    {hOab : Matrix.transpose (oConj M (A * B)) * oConj M (A * B) = 1}
    {hOa : Matrix.transpose (oConj M A) * oConj M A = 1}
    {hOb : Matrix.transpose (oConj M B) * oConj M B = 1} (wA wB : Fin 3 → ℝ) :
    gOf M A hOa wA * gOf M B hOb wB = gOf M (A * B) hOab (realMat A *ᵥ wB + wA) := by
  refine AffineIsometryEquiv.ext fun x => ?_
  simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply, gOf_apply]
  apply WithLp.ofLp_injective
  simp only [WithLp.ofLp_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    oConj_mul M hM A B, oConj_mul_self M hM A]
  abel

end GOfMulAux

open GOfMulAux

theorem gOf_mul (M : Work.SG.RMat) (hM : M.det ≠ 0) {A B : Work.SG.IMat}
    {τ : Work.SG.IMat → Fin 3 → ℝ} {k : Fin 3 → ℤ}
    (hk : τ (A * B) = τ A + Matrix.mulVec (Work.SG.realMat A) (τ B) + Work.SG.intVec k)
    (n m : Fin 3 → ℤ)
    (hOab : Matrix.transpose (Work.SG.oConj M (A * B)) * (Work.SG.oConj M (A * B)) = 1)
    (hOa : Matrix.transpose (Work.SG.oConj M A) * (Work.SG.oConj M A) = 1)
    (hOb : Matrix.transpose (Work.SG.oConj M B) * (Work.SG.oConj M B) = 1) :
    Work.SG.gOf M A hOa (τ A + Work.SG.intVec n) * Work.SG.gOf M B hOb (τ B + Work.SG.intVec m)
      = Work.SG.gOf M (A * B) hOab (τ (A * B) + Work.SG.intVec (A.mulVec m + n - k)) := by
  -- the integer correction `k` cancels against `A m + n - k + k`
  have hk' : Work.SG.intVec k + Work.SG.intVec (A.mulVec m + n - k)
      = Work.SG.intVec (A.mulVec m) + Work.SG.intVec n := by
    rw [← intVec_add_aux, ← intVec_add_aux,
      show k + (A.mulVec m + n - k) = A.mulVec m + n by abel]
  -- the translation vectors of the two sides agree
  have hw : Work.SG.realMat A *ᵥ (τ B + Work.SG.intVec m) + (τ A + Work.SG.intVec n)
      = τ (A * B) + Work.SG.intVec (A.mulVec m + n - k) := by
    calc Work.SG.realMat A *ᵥ (τ B + Work.SG.intVec m) + (τ A + Work.SG.intVec n)
        = Work.SG.realMat A *ᵥ τ B
            + (Work.SG.intVec (A.mulVec m) + (τ A + Work.SG.intVec n)) := by
          rw [Matrix.mulVec_add, realMat_mulVec_intVec_aux]; abel
      _ = Work.SG.realMat A *ᵥ τ B
            + (τ A + (Work.SG.intVec k + Work.SG.intVec (A.mulVec m + n - k))) := by
          rw [hk']; abel
      _ = τ (A * B) + Work.SG.intVec (A.mulVec m + n - k) := by
          rw [hk]; abel
  rw [gOf_mul_aux M hM A B (hOab := hOab) (τ A + Work.SG.intVec n)
    (τ B + Work.SG.intVec m), hw]

end Work.SG
