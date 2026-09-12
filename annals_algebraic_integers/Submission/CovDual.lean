import Mathlib
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Submission.LatticeDefs

noncomputable section

open scoped BigOperators RealInnerProductSpace NNReal ENNReal
open Module Submodule MeasureTheory MeasureTheory.Measure Metric Filter
open Submission.LatticeDefs

/-!
# Determinant/covolume duality for the dual basis in an inner product space

In a finite-dimensional real inner product space `E` (canonical volume: the Haar
measure with unit-volume parallelepipeds on orthonormal bases, as provided by
`MeasureTheory.measureSpaceOfInnerProductSpace`), let `b : Basis ι ℝ E`.  Let

    db := (euclForm E).dualBasis (euclform_nondegenerate E) b

be the dual basis w.r.t. the inner product.  Then the volumes of the fundamental
domains multiply to `1`.
-/

namespace Submission.CovDual

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inner product of `x` and `y` computed from their coordinates in an orthonormal basis. -/
lemma sum_repr_inner {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ E) (x y : E) :
    (∑ i, (o.toBasis.repr x) i * (o.toBasis.repr y) i) = ⟪x, y⟫ := by
  have hsum := OrthonormalBasis.sum_inner_mul_inner o x y
  calc
    (∑ i, (o.toBasis.repr x) i * (o.toBasis.repr y) i)
        = ∑ i, ⟪x, o i⟫ * ⟪o i, y⟫ := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
            rw [real_inner_comm]
    _ = ⟪x, y⟫ := hsum

/-- The coordinate matrix (in the orthonormal basis `o`) of the inner-product-dual basis
is the inverse transpose of the coordinate matrix of the original basis. -/
lemma dualBasis_toMatrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (o : OrthonormalBasis ι ℝ E) :
    let db := (euclForm E).dualBasis (euclForm_nondegenerate E) b
    ((o.toBasis.toMatrix db).transpose * (o.toBasis.toMatrix b)) = 1 := by
  intro db
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
  rw [sum_repr_inner o (db j) (b k)]
  rw [← euclForm_apply (db j) (b k)]
  rw [LinearMap.BilinForm.apply_dualBasis_left]
  rw [Matrix.one_apply]
  by_cases h : j = k
  · simp [h]
  · simp [h, eq_comm]

/-- The absolute determinants of a basis and of its dual basis multiply to `1`. -/
lemma det_mul_det_dual {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (o : OrthonormalBasis ι ℝ E) :
    |o.toBasis.det b| * |o.toBasis.det ((euclForm E).dualBasis (euclForm_nondegenerate E) b)| = 1 := by
  let db := (euclForm E).dualBasis (euclForm_nondegenerate E) b
  have hNM : ((o.toBasis.toMatrix db).transpose * (o.toBasis.toMatrix b)) = 1 :=
    dualBasis_toMatrix_mul b o
  have hdet := congrArg Matrix.det hNM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hb : (o.toBasis.toMatrix b).det = o.toBasis.det b := by
    rw [Module.Basis.det_apply]
  have hdb : (o.toBasis.toMatrix db).det = o.toBasis.det db := by
    rw [Module.Basis.det_apply]
  rw [hdb, hb, mul_comm] at hdet
  rw [← abs_mul, hdet, abs_one]

end InnerProduct

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The fundamental domain of an orthonormal basis has volume `1`. -/
lemma fundamentalDomain_measureReal_onb {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ E) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  have hae : ZSpan.fundamentalDomain o.toBasis =ᵐ[volume] parallelepiped (⇑o) := by
    simpa [OrthonormalBasis.coe_toBasis] using ZSpan.fundamentalDomain_ae_parallelepiped (μ := volume) o.toBasis
  have hv1 : volume (parallelepiped (⇑o)) = 1 := OrthonormalBasis.volume_parallelepiped o
  simp [MeasureTheory.measureReal_def, measure_congr hae, hv1]

/-- The volume of the fundamental domain of a basis is the absolute value of its determinant
with respect to any orthonormal basis. -/
lemma fundamentalDomain_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (o : OrthonormalBasis ι ℝ E) :
    volume.real (ZSpan.fundamentalDomain b) = |o.toBasis.det b| := by
  rw [ZSpan.measureReal_fundamentalDomain b volume o.toBasis, fundamentalDomain_measureReal_onb o,
    mul_one]

end Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Volume of the fundamental domain of a real basis times that of its dual basis equals 1. -/
lemma covolume_dual_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    (volume.real (ZSpan.fundamentalDomain b)) *
      (volume.real (ZSpan.fundamentalDomain
        ((euclForm E).dualBasis (euclForm_nondegenerate E) b))) = 1 := by
  classical
  let e : ι ≃ Fin (finrank ℝ E) := Fintype.equivFinOfCardEq (by simp [Module.finrank_eq_card_basis b])
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex e.symm
  set db : Basis ι ℝ E := (euclForm E).dualBasis (euclForm_nondegenerate E) b
  calc
    volume.real (ZSpan.fundamentalDomain b) * volume.real (ZSpan.fundamentalDomain db)
        = |o.toBasis.det b| * |o.toBasis.det db| := by
            rw [fundamentalDomain_measureReal b o, fundamentalDomain_measureReal db o]
    _ = 1 := by
            simpa [db] using det_mul_det_dual (o := o) b

end Submission.CovDual
