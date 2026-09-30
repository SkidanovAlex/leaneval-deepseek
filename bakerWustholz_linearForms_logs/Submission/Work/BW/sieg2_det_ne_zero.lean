import Mathlib
import Submission.Work.BW.sieg2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Nonvanishing of the mixed-coordinate Gram determinant

The mixed coordinate space `SiegCoord F N = ℝ^{d N}` (`d = [F : ℚ]`) carries the Euclidean
inner product obtained by reading off the coordinates of the orthonormal basis
`mixedEmbedding.stdBasis F`.  The explicit sum `siegInner` defined in `sieg2Defs` is precisely
that Euclidean dot product: the index set `mixedEmbedding.index F` splits as one coordinate per
*real* infinite place and two coordinates (real and imaginary part) per *complex* infinite place.

Consequently the "Gram matrix" `fun i j => siegInner (x i) (x j)` of a family of vectors is a
genuine Gram matrix, and it is non-singular as soon as the family is linearly independent over
`ℝ`.  We prove this through the matrix identity `G = M * Mᵀ`, where `M` is the matrix whose rows
are the vectors: if `G` were singular there would be a nonzero `c` with `G *ᵥ c = 0`, whence
`(Mᵀ *ᵥ c) ⬝ᵥ (Mᵀ *ᵥ c) = c ⬝ᵥ (G *ᵥ c) = 0`, so `Mᵀ *ᵥ c = 0`, i.e. `∑ i, c i • x i = 0`,
contradicting linear independence.
-/

open NumberField
open scoped Classical
open Matrix

namespace Work.BW

/-- In mixed coordinates, `siegInner` is the ordinary Euclidean dot product over the full index
set `Fin N × mixedEmbedding.index F` (one coordinate per real place, two per complex place). -/
theorem siegInner_eq_sum {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (x y : SiegCoord F N) :
    siegInner x y = ∑ p : Fin N × NumberField.mixedEmbedding.index F, x p.1 p.2 * y p.1 p.2 := by
  simp only [siegInner, Fintype.sum_prod_type, Fintype.sum_sum_type,
    NumberField.InfinitePlace.sum_eq_sum_add_sum]
  apply Finset.sum_congr rfl; intro j _
  congr 1
  · apply Finset.sum_congr rfl; intro a _
    rw [dite_eq_left a.2]
  · apply Finset.sum_congr rfl; intro c _
    rw [dite_eq_right (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr c.2), Fin.sum_univ_two]

/-- A Gram-type determinant built from the Euclidean dot product of a family of real vectors is
nonzero whenever the family is linearly independent. -/
theorem gram_det_ne_zero {ι : Type*} [Fintype ι] {N K : ℕ}
    (x : Fin K → (Fin N → ι → ℝ)) (hli : LinearIndependent ℝ x) :
    (Matrix.of (fun i j : Fin K => ∑ p : Fin N × ι, x i p.1 p.2 * x j p.1 p.2)).det ≠ 0 := by
  classical
  set M : Matrix (Fin K) (Fin N × ι) ℝ := fun i p => x i p.1 p.2
  have hGM : (Matrix.of (fun i j : Fin K => ∑ p : Fin N × ι, x i p.1 p.2 * x j p.1 p.2))
      = M * Mᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun p _ => by simp [M])
  rw [hGM]
  intro hdet
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : c ⬝ᵥ ((M * Mᵀ).mulVec c) = 0 := by rw [hc]; simp
  have hvec : Matrix.vecMul c M = Mᵀ.mulVec c := by
    funext p
    simp only [Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have h2 : c ⬝ᵥ ((M * Mᵀ).mulVec c) = (Mᵀ.mulVec c) ⬝ᵥ (Mᵀ.mulVec c) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hvec]
  have h3 : Mᵀ.mulVec c = 0 := dotProduct_self_eq_zero.mp (h2 ▸ h1)
  have hcomp : ∀ (j : Fin N) (q : ι), (Mᵀ.mulVec c) (j, q) = ∑ i, c i * x i j q := by
    intro j q
    simp only [Matrix.mulVec, M]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hz : ∑ i, c i • x i = 0 := by
    funext j q
    have hL : (∑ i, c i • x i) j q = ∑ i, c i * x i j q := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hL, ← hcomp j q]
    simp [h3]
  exact hcne (funext (Fintype.linearIndependent_iff.mp hli c hz))

theorem sieg2_det_ne_zero {F : Type*} [Field F] [NumberField F] {N K : ℕ}
    (v : Fin K → (Fin N → NumberField.RingOfIntegers F))
    (hli : LinearIndependent ℝ (fun i => Work.BW.siegCoord (v i))) :
    Matrix.det (Matrix.of (fun i j : Fin K =>
      Work.BW.siegInner (Work.BW.siegCoord (v i)) (Work.BW.siegCoord (v j)))) ≠ 0 := by
  classical
  have heq : Matrix.of (fun i j : Fin K =>
        Work.BW.siegInner (Work.BW.siegCoord (v i)) (Work.BW.siegCoord (v j)))
      = Matrix.of (fun i j : Fin K =>
          ∑ p : Fin N × NumberField.mixedEmbedding.index F,
            Work.BW.siegCoord (v i) p.1 p.2 * Work.BW.siegCoord (v j) p.1 p.2) := by
    ext i j
    exact siegInner_eq_sum _ _
  rw [heq]
  exact gram_det_ne_zero (fun i => Work.BW.siegCoord (v i)) hli

end Work.BW
