import Mathlib
import Submission.Work.ThomBordism._gtd.P1
import Submission.Work.ThomBordism.Grassmann.Oriented

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThomBordism.Signs

open Work.ThomBordism.Grassmann

/-!
# The invariance of the chart evaluation under the orientation flip

`Work.ThomBordism.Grassmann.flipMat k = diag(-1,1,…,1)` is an orthogonal, orientation-**reversing**
matrix (its determinant is `-1`), so it is *not* an element of `SOk k` and the existing
`Work.ThomBordism.Grassmann.coordVec_soActFun`/`coordEval_soActFun` do not apply to it.  But the
coordinate vectors of the plane of a frame are in fact invariant under *any* change of frame by an
invertible matrix: `coordVec S f i` is the vector of the plane of `f` whose `S`-coordinates are
`e_i`, and this description does not depend on the basis of the plane used to compute it.  The
helper below records exactly this for a matrix with `Aᵀ A = 1` (which is the hypothesis needed for
the acted frame to remain orthonormal), by replaying the proof of `coordVec_soActFun` with
`A.det` a unit instead of `A ∈ SO(k)`.

Consequently the chart evaluation `coordEval S (flipMat k · f) v` agrees with `coordEval S f v`:
the orientation flip of the Grassmannian acts on the frames but not on the chart coordinates of the
tautological bundle.  This is the frame-level input of the `Signs/flipMap` construction.
-/

/-- **Invariance of the coordinate vectors under an orthogonal change of frame.**  If `Aᵀ A = 1`
(so that acting on an orthonormal frame produces an orthonormal frame), then the `S`-coordinate
vectors of the plane of `A · f` are those of the plane of `f`: the coordinate vectors do not
depend on which orthonormal basis of the plane is used. -/
theorem coordVec_soActFun_of_orth {k m : ℕ} (S : ChartIdx k m) (f : Stiefel k m) (i : Fin k)
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.transpose * A = 1) :
    coordVec S ⟨soActFun A f.1, orthonormal_soActFun hA f.2⟩ i = coordVec S f i := by
  by_cases hunit : IsUnit (frameMatrix S f.1).det
  · rw [coordVec, coordVec, show (⟨soActFun A f.1, orthonormal_soActFun hA f.2⟩ : Stiefel k m).1
        = soActFun A f.1 from rfl, frameMatrix_soActFun, Matrix.mul_inv_rev]
    simp only [soActFun, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hcoef : (∑ j, ((A⁻¹ * (frameMatrix S f.1)⁻¹) j i * A l j))
        = (frameMatrix S f.1)⁻¹ l i := by
      rw [show (∑ j, ((A⁻¹ * (frameMatrix S f.1)⁻¹) j i * A l j))
          = ∑ j, (A l j * ((A⁻¹ * (frameMatrix S f.1)⁻¹) j i)) from
        Finset.sum_congr rfl fun j _ => mul_comm _ _]
      rw [← Matrix.mul_apply]
      rw [show (A * (A⁻¹ * (frameMatrix S f.1)⁻¹)) = (frameMatrix S f.1)⁻¹ from by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hA),
          Matrix.one_mul]]
    simp only [← mul_smul]
    rw [← Finset.sum_smul, hcoef]
  · have hdet : (frameMatrix S f.1).det = 0 := by
      by_contra h
      exact hunit (isUnit_iff_ne_zero.mpr h)
    have hdet2 : (frameMatrix S
        (⟨soActFun A f.1, orthonormal_soActFun hA f.2⟩ : Stiefel k m).1).det = 0 := by
      rw [show (⟨soActFun A f.1, orthonormal_soActFun hA f.2⟩ : Stiefel k m).1
            = soActFun A f.1 from rfl,
        frameMatrix_soActFun, Matrix.det_mul, hdet, zero_mul]
    rw [coordVec, coordVec, Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hdet2]; simp),
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hdet]; simp)]
    simp

/-- **The evaluation of the tautological fibre does not see the orientation flip**:
right-multiplying a frame of the chart `S` by `flipMat k = diag(-1,1,…,1)` leaves the chart
coordinates of every vector of the plane unchanged. -/
theorem coordEval_flipMat {k m : ℕ} (S : Work.ThomBordism.Grassmann.ChartIdx k m) (f : Work.ThomBordism.Grassmann.Stiefel k m) (hf : f ∈ Work.ThomBordism.Grassmann.chartSet S)
    (v : Work.ThomBordism.Grassmann.Amb k) :
    Work.ThomBordism.Grassmann.coordEval S ⟨Work.ThomBordism.Grassmann.soActFun (Work.ThomBordism.Grassmann.flipMat k) f.1, Work.ThomBordism.Grassmann.orthonormal_soActFun (Work.ThomBordism.Grassmann.flipMat_transpose_mul k) f.2⟩ v
      = Work.ThomBordism.Grassmann.coordEval S f v := by
  rw [coordEval, coordEval]
  exact Finset.sum_congr rfl fun i _ => by
    rw [coordVec_soActFun_of_orth S f i (flipMat_transpose_mul k)]

end Work.ThomBordism.Signs
