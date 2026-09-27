import Mathlib
import Submission.Work.Drive.analyticDensity
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.linCommonPoint
import Submission.Work.Drive.linShearIncidence
import Submission.Work.Drive.linPlaneChartNormals
import Submission.Work.Drive.hVNormalForm

/-!
# The vocabulary of the general-position clause of the transported linear family

`Work.Drive.rowCD_linTrans_generalPosition_openDense` asks for an open set of design parameters
`t`, dense at every point of the closed unit ball, on which the transported linear family

> `Ψ k (t) = (linBase A k).trans (classEquiv (blk k t))`

is in *general position*: the three planes `linSub (Ψ k (t))` meet in a line (`hrank`) and the
boundary circle of the disk model of the `k`-th chart never hits the common point of the three planes
(`hgen`).

The general-position set is the complement of the zero set of *three* explicit functions of `t`
(`Work.Drive.gpDet A k`), which are analytic; the density engine `Work.Drive.isOpen_denseAtBall_ne_zero`
then gives openness and density at the ball.  This module fixes the vocabulary:

* `gpStdVec j` — the standard basis vector `e_j` of `Eucl 3 = ℝ⁴`;
* `gpPsi A k t` — the transported linear chart `Ψ k (t)`;
* `gpCoordPull j φ` — the functional `v ↦ (φ⁻¹ v) _ j`;
* `gpFun A k t` — the four functionals `(linFun (Ψ 0), linFun (Ψ 1), linFun (Ψ 2), coord 2 of (Ψ k)⁻¹)`
  of the `k`-th quadruple;
* `gpMat A k t`, `gpDet A k t` — their matrix in the standard basis and its determinant;
* `gpLambda A k t` — the endomorphism of `Eucl 3` whose components are the four functionals (so that
  the determinant of `gpMat` is the determinant of `gpLambda`, and `gpDet A k t ≠ 0` is exactly the
  linear independence of the four functionals);
* `gpInvCoord A n j v t = ((Ψ n t)⁻¹ v) _ j` and its explicit form (the class inverse formula), which
  is what makes `gpDet` a rational function of `t` with a positive denominator.

The mathematical content (the identification with `hrank`/`hgen`, and the analyticity of `gpDet`) is in
the modules that import this one. -/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

/-- The standard basis vector `e_j` of `Eucl 3 = ℝ⁴`. -/
def gpStdVec (j : Fin 4) : Eucl 3 := (EuclideanSpace.single j (1 : ℝ) : Eucl 3)

/-- The `j`-th coordinate functional of `Eucl 3`, pulled back by the inverse of a linear equivalence:
`v ↦ (φ⁻¹ v) _ j`. -/
def gpCoordPull (j : Fin 4) (φ : Eucl 3 ≃L[ℝ] Eucl 3) : Eucl 3 →ₗ[ℝ] ℝ :=
  (coordFun j).comp φ.symm.toLinearMap

/-- **The transported linear chart**: `Ψ k (t) = (linBase A k).trans (classEquiv (blk k t))`. -/
def gpPsi (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    Eucl 3 ≃L[ℝ] Eucl 3 :=
  (linBase A k).trans (classEquiv ((blk k) t))

/-- **The four functionals** of the `k`-th quadruple: the three normals `linFun (Ψ k)` of the three
planes, and the functional `v ↦ ((Ψ k t)⁻¹ v) _ 2` whose kernel cuts the boundary line out of the
`k`-th plane. -/
def gpFun (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    Fin 4 → (Eucl 3 →ₗ[ℝ] ℝ) :=
  Fin.cases (linFun (gpPsi A 0 t))
    (Fin.cases (linFun (gpPsi A 1 t))
      (Fin.cases (linFun (gpPsi A 2 t))
        (fun _ => gpCoordPull 2 (gpPsi A k t))))

@[simp] lemma gpFun_zero (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) : gpFun A k t 0 = linFun (gpPsi A 0 t) := rfl

@[simp] lemma gpFun_one (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) : gpFun A k t 1 = linFun (gpPsi A 1 t) := rfl

@[simp] lemma gpFun_two (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) : gpFun A k t 2 = linFun (gpPsi A 2 t) := rfl

@[simp] lemma gpFun_three (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) : gpFun A k t 3 = gpCoordPull 2 (gpPsi A k t) := rfl

/-- The matrix of the four functionals in the standard basis `e_0, …, e_3`. -/
def gpMat (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => gpFun A k t i (gpStdVec j)

lemma gpMat_apply (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12))
    (i j : Fin 4) : gpMat A k t i j = gpFun A k t i (gpStdVec j) := rfl

/-- **The general-position determinant** of the `k`-th quadruple. -/
def gpDet (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) : ℝ :=
  (gpMat A k t).det

/-- The endomorphism of `Eucl 3` whose components are the four functionals of `gpFun`. -/
def gpLambda (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) :
    Eucl 3 →ₗ[ℝ] Eucl 3 :=
  toLp4.toLinearMap.comp (LinearMap.pi (gpFun A k t))

/-- The `j`-th coordinate of `(Ψ n t)⁻¹ v`. -/
def gpInvCoord (A : Eucl 3 ≃L[ℝ] Eucl 3) (n : Fin 3) (j : Fin 4) (v : Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) : ℝ :=
  ((gpPsi A n t)⁻¹ v) j

/-- The `j`-th coordinate of the `k`-th block of the parameter, as a continuous linear map. -/
def gpLinCoord (k : Fin 3) (j : Fin 4) : EuclideanSpace ℝ (Fin 12) →L[ℝ] ℝ :=
  (cproj j).comp (blk k)

@[simp] lemma gpLinCoord_apply (k : Fin 3) (j : Fin 4) (t : EuclideanSpace ℝ (Fin 12)) :
    gpLinCoord k j t = (blk k t) j := rfl

/-- `t ↦ ((linBase A k)⁻¹ (classGen (blk k t) v)) _ j`, as a continuous linear map of `t`. -/
def gpClassGenCoord (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (v : Eucl 3) (j : Fin 4) :
    EuclideanSpace ℝ (Fin 12) →L[ℝ] ℝ :=
  (cproj j).comp (((linBase A k).symm : Eucl 3 →L[ℝ] Eucl 3).comp
    ((classEval v).toContinuousLinearMap.comp (blk k)))

@[simp] lemma gpClassGenCoord_apply (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (v : Eucl 3)
    (j : Fin 4) (t : EuclideanSpace ℝ (Fin 12)) :
    gpClassGenCoord A k v j t = ((linBase A k)⁻¹ (classGen ((blk k) t) v)) j := by
  rw [gpClassGenCoord]
  show (cproj j) ((linBase A k).symm (classEval v ((blk k) t))) =
    ((linBase A k).symm (classGen ((blk k) t) v)) j
  rw [classEval_apply]
  rfl

/-! ## The explicit inverse of the class equivalence -/

/-- **The inverse of the class equivalence**, applied to a vector:
`(1 + L τ)⁻¹ w = (1 + ‖τ‖²)⁻¹ • (w - L τ w)`. -/
lemma classEquiv_inv_apply (t w : Eucl 3) :
    (classEquiv t).symm w = (1 + classNormSq t)⁻¹ • ((1 - classGen t) w) := by
  have hpos : (0 : ℝ) < 1 + classNormSq t := by
    have := classNormSq_nonneg t; linarith
  apply (classEquiv t).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  show w = classEquiv t ((1 + classNormSq t)⁻¹ • ((1 - classGen t) w))
  have hcoe : ⇑(classEquiv t) = ⇑(1 + classGen t : Eucl 3 →L[ℝ] Eucl 3) := by
    funext v; rw [classEquiv_apply]; rfl
  rw [hcoe, map_smul, classGen_mul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul,
    eq_comm]

/-- **The explicit form of `gpInvCoord`**: the `j`-th coordinate of `(Ψ n t)⁻¹ v` is the `j`-th
coordinate of `(linBase A n)⁻¹ v` corrected by the class generator, divided by `1 + ‖blk n t‖²`. -/
lemma gpInvCoord_formula (A : Eucl 3 ≃L[ℝ] Eucl 3) (n : Fin 3) (j : Fin 4) (v : Eucl 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    gpInvCoord A n j v t = (1 + classNormSq ((blk n) t))⁻¹ *
      (((linBase A n)⁻¹ v) j - ((linBase A n)⁻¹ (classGen ((blk n) t) v)) j) := by
  rw [gpInvCoord]
  show (((linBase A n).trans (classEquiv ((blk n) t)))⁻¹ v).ofLp j = _
  rw [
    show ((linBase A n).trans (classEquiv ((blk n) t)))⁻¹ v
        = (linBase A n)⁻¹ ((classEquiv ((blk n) t))⁻¹ v) from rfl,
    show ((classEquiv ((blk n) t))⁻¹ v)
        = (1 + classNormSq ((blk n) t))⁻¹ • ((1 - classGen ((blk n) t)) v)
        from classEquiv_inv_apply _ _]
  simp

end

end Work.Drive
