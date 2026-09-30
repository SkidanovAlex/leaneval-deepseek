import Mathlib
import Submission.Work.BW.sieg2_intLatE_basis
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The determinant of the Gram matrix of `intLatEBasis`

`Submission.Work.BW.sieg2_intLatE_basis` provides, for every number field `F` and every `N`,
an `ℝ`-basis `intLatEBasis F N` of `EuclideanSpace ℝ (Fin N × index F)` whose `ℤ`-span is
the lattice `intLatE F N`.  It is the `N`-fold product of the one-factor basis `intLatBasis F`
of `EuclideanSpace ℝ (index F)`, mapped through the currying identification.

Here we compute the determinant of the corresponding Gram matrix:

  `det (gram (intLatEBasis F N)) = (det (gram (intLatBasis F))) ^ N`.

The point is that in the product basis the Gram matrix is *block diagonal* with `N` identical
blocks `gram (intLatBasis F)`: two product basis vectors whose `Fin N`-coordinates differ are
orthogonal, and when those coordinates agree they contribute the corresponding entry of
`gram (intLatBasis F)`.  We prove this entrywise and then invoke the block-diagonal determinant
formula.
-/

open NumberField
open scoped Classical

namespace Work.BW

noncomputable section

/-- The mixed coordinates of the image of the `i`-th element of the integral basis of `F`. -/
def sieg2IntLatCoord (F : Type*) [Field F] [NumberField F]
    (i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) :
    NumberField.mixedEmbedding.index F → ℝ :=
  fun p => (NumberField.mixedEmbedding.stdBasis F).repr
    (NumberField.mixedEmbedding F (NumberField.integralBasis F i)) p

/-- The inner product of two vectors of `EuclideanSpace ℝ ι` given by coordinate functions. -/
theorem sieg2_inner_toLp {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]

/-- The combinatorial core: a sum, over the product `Fin N × J`, of the pointwise product of two
"coordinate slices".  Only the terms whose `Fin N`-coordinate agrees survive. -/
theorem sieg2_sum_prod_ite_mul {ι J : Type*} [Fintype ι] [Fintype J] (N : ℕ) (c : ι → J → ℝ)
    (q q' : Fin N × ι) :
    (∑ p : Fin N × J,
        (if p.1 = q.1 then c q.2 p.2 else 0) * (if p.1 = q'.1 then c q'.2 p.2 else 0))
      = if q.1 = q'.1 then ∑ j, c q.2 j * c q'.2 j else 0 := by
  rw [Fintype.sum_prod_type]
  dsimp only
  by_cases h : q.1 = q'.1
  · rw [ite_eq_left h, Finset.sum_eq_single q.1]
    · simp [h]
    · intro n _ hn
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [ite_eq_right hn, zero_mul]
    · intro hn; simp at hn
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero (fun n _ => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hn : n = q.1
    · rw [ite_eq_left hn, ite_eq_right (by intro hc; exact h (hn.symm.trans hc))]
      simp
    · rw [ite_eq_right hn, zero_mul]

/-- Block-diagonal determinant: the matrix whose `Fin N`-blocks on the diagonal are `G` and whose
off-diagonal blocks vanish has determinant `G.det ^ N`. -/
theorem sieg2_det_of_ite_mul_block {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (N : ℕ) (G : Matrix ι ι R) :
    (Matrix.of (fun (q q' : Fin N × ι) => if q.1 = q'.1 then G q.2 q'.2 else 0)).det
      = G.det ^ N := by
  have key : (Matrix.of (fun (q q' : Fin N × ι) => if q.1 = q'.1 then G q.2 q'.2 else 0))
      = (Matrix.blockDiagonal (fun _ : Fin N => G)).submatrix
          (Equiv.prodComm (Fin N) ι) (Equiv.prodComm (Fin N) ι) := by
    ext q q'
    simp [Matrix.blockDiagonal, Equiv.prodComm, Matrix.submatrix_apply]
  rw [key, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  simp [Fintype.card_fin]

/-- The inner product of two vectors of the one-factor basis `intLatBasis F`, in coordinates. -/
theorem sieg2_gram_intLatBasis_inner {F : Type*} [Field F] [NumberField F]
    (i i' : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) :
    inner ℝ (intLatBasis F i) (intLatBasis F i')
      = ∑ j, sieg2IntLatCoord F i j * sieg2IntLatCoord F i' j := by
  rw [intLatBasis_apply, intLatBasis_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  rfl

theorem sieg2_gram_det_intLatEBasis {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    (Matrix.gram ℝ (⇑(Work.BW.intLatEBasis F N))).det
      = (Matrix.gram ℝ (⇑(Work.BW.intLatBasis F))).det ^ N := by
  have hM : Matrix.gram ℝ (⇑(intLatEBasis F N))
      = Matrix.of (fun q q' : Fin N ×
            Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F) =>
          if q.1 = q'.1 then (Matrix.gram ℝ (⇑(intLatBasis F))) q.2 q'.2 else 0) := by
    ext q q'
    rw [Matrix.gram_apply, Matrix.of_apply, Matrix.gram_apply]
    rw [sieg2_gram_intLatBasis_inner]
    simp only [intLatEBasis_apply]
    rw [sieg2_inner_toLp]
    exact sieg2_sum_prod_ite_mul N (fun i j =>
      (NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F (NumberField.integralBasis F i)) j) q q'
  rw [hM, sieg2_det_of_ite_mul_block]

end

end Work.BW
