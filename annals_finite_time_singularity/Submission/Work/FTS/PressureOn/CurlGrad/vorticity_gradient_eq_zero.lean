import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.Coords

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Gradient

namespace Work.FTS.PressureOn.CurlGrad

/-!
# The curl of a gradient vanishes

Auxiliary facts for `vorticity_gradient_eq_zero`: the coordinates of Mathlib's gradient in the
standard basis, the differentiability of the gradient of a `C²` function, the coordinate formula
for the derivative of a gradient field (the `(i,j)` entry of `D(∇φ)(x)` is the mixed second
partial `∂ᵢ∂ⱼφ`), and the symmetry of the second derivative.
-/

/-- **Coordinates of a gradient.**  In the standard basis `e j` of `ℝ³`, the `j`-th coordinate of
the gradient `∇φ` is the partial derivative `∂ⱼφ`. -/
theorem gradient_apply_coord {φ : Work.FTS.PressureOn.R3 → ℝ} (y : Work.FTS.PressureOn.R3)
    (j : Fin 3) :
    (gradient φ y) j = fderiv ℝ φ y (FiniteTimeSingularity.e j) := by
  rw [← EuclideanSpace.basisFun_inner,
    show (EuclideanSpace.basisFun (Fin 3) ℝ) j = FiniteTimeSingularity.e j from
      (Work.Cyl.basisVec_eq_basisFun j).symm,
    inner_gradient_right]
  simp

/-- **The gradient of a `C²` function is differentiable.**  Its derivative at `x` is the second
derivative `fderiv ℝ (fderiv ℝ φ) x` of `φ`, transported to a map `ℝ³ → ℝ³` across the Riesz
identification `R3 ≃ₗᵢ⋆[ℝ] StrongDual ℝ R3`. -/
theorem hasFDerivAt_gradient {φ : Work.FTS.PressureOn.R3 → ℝ} {x : Work.FTS.PressureOn.R3}
    (hφ : ContDiffAt ℝ 2 φ x) :
    HasFDerivAt (gradient φ)
      (((InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm.toContinuousLinearEquiv.toContinuousLinearMap :
          StrongDual ℝ Work.FTS.PressureOn.R3 →L[ℝ] Work.FTS.PressureOn.R3).comp
        (fderiv ℝ (fderiv ℝ φ) x)) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x := hφ.fderiv_right (m := 1) (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  exact (LinearIsometryEquiv.hasFDerivAt
    (InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm (x := (fderiv ℝ φ) x)).comp x hfd

/-- **The derivative of a gradient in coordinates.**  For `φ` of class `C²` at `x`, the `(i,j)`
entry of the Jacobian of `∇φ` at `x` is the mixed second partial derivative `∂ᵢ∂ⱼφ`. -/
theorem fderiv_gradient_apply_coord {φ : Work.FTS.PressureOn.R3 → ℝ}
    {x : Work.FTS.PressureOn.R3} (hφ : ContDiffAt ℝ 2 φ x) (i j : Fin 3) :
    (fderiv ℝ (gradient φ) x (FiniteTimeSingularity.e i)) j
      = (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e j) := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x := hφ.fderiv_right (m := 1) (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  have hd : DifferentiableAt ℝ (gradient φ) x := (hasFDerivAt_gradient hφ).differentiableAt
  have hcc : (fderiv ℝ (gradient φ) x (FiniteTimeSingularity.e i)) j
      = fderiv ℝ (fun y => (gradient φ y) j) x (FiniteTimeSingularity.e i) := by
    rw [Work.Cyl.fderiv_coord (gradient φ) x hd j, ContinuousLinearMap.comp_apply,
      PiLp.proj_apply]
  have hcongr : (fun y => (gradient φ y) j)
      = (fun y => fderiv ℝ φ y (FiniteTimeSingularity.e j)) :=
    funext fun y => gradient_apply_coord y j
  rw [hcc, hcongr]
  have hclm : HasFDerivAt (fun y => fderiv ℝ φ y (FiniteTimeSingularity.e j))
      ((fderiv ℝ (fderiv ℝ φ) x).flip (FiniteTimeSingularity.e j)) x := by
    have h := hfd.clm_apply (hasFDerivAt_const (FiniteTimeSingularity.e j) x)
    simpa using h
  rw [hclm.fderiv]
  simp

/-- **The second derivative of a `C²` function is symmetric.** -/
theorem sndFDeriv_symm {φ : Work.FTS.PressureOn.R3 → ℝ} {x : Work.FTS.PressureOn.R3}
    (hφ : ContDiffAt ℝ 2 φ x) (i j : Fin 3) :
    (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e j)
      = (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e j)) (FiniteTimeSingularity.e i) :=
  (hφ.isSymmSndFDerivAt (by norm_num)).eq (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e j)

/-- **The curl of a gradient vanishes.**  For `φ : ℝ³ → ℝ` of class `C²` at `x` (in the sense of
`ContDiffAt`), `vorticity (gradient φ) x = 0`, where `vorticity` is the curl
(`FiniteTimeSingularity.vorticity`, defined in `ChallengeDeps.lean` as `∑ i, e i ⨯₃ ∂ᵢu`) and
`gradient` is Mathlib's gradient.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.vorticity_gradient_eq_zero`.

Proof hints (all available in this workspace):
* the coordinate form of the curl `Work.Cyl.vorticity_eq_coordinates` and
  `Work.Cyl.fderiv_apply_coord` (`((fderiv ℝ u x) (basisVec i)).ofLp j =
  Cyl.pd i (fun y => (u y).ofLp j) x`), in `Submission/Work/Cyl/Basic.lean` and
  `Submission/Work/Cyl/Coords.lean`;
* `inner_gradient_left : ⟪∇ f x, y⟫ = fderiv ℝ f x y` (Mathlib,
  `Mathlib/Analysis/Calculus/Gradient/Basic.lean`) identifies `(gradient φ y) j =
  fderiv ℝ φ y (basisVec j)`;
* the mixed second derivatives of `φ` commute at `x`: `ContDiffAt.isSymmSndFDerivAt`
  (`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`), i.e.
  `fderiv ℝ (fderiv ℝ φ) x v w = fderiv ℝ (fderiv ℝ φ) x w v` for `φ ∈ C²` at `x`; the relocation
  `fderiv ℝ (fun y => fderiv ℝ φ y (e j)) x (e i) = (fderiv ℝ (fderiv ℝ φ) x (e i)) (e j)` comes
  from `HasFDerivAt.clm_apply` / `fderiv_clm_apply`
  (`Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`), applied to `c := fun y => fderiv ℝ φ y` and
  the constant `u := fun _ => e j`.

With these, each of the three coordinates of `vorticity (gradient φ) x` is a difference
`∂ᵢ∂ⱼφ - ∂ⱼ∂ᵢφ = 0`. -/
theorem vorticity_gradient_eq_zero {φ : Work.FTS.PressureOn.R3 → ℝ}
    {x : Work.FTS.PressureOn.R3} (hφ : ContDiffAt ℝ 2 φ x) :
    FiniteTimeSingularity.vorticity (gradient φ) x = 0 := by
  have hsymm : ∀ i j : Fin 3,
      (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e j)
        = (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e j))
            (FiniteTimeSingularity.e i) :=
    fun i j => sndFDeriv_symm hφ i j
  rw [Work.Cyl.vorticity_eq_coordinates]
  apply PiLp.ext
  intro j
  fin_cases j
  · show ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 1)).ofLp 2
        - ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 2)).ofLp 1 = 0
    rw [fderiv_gradient_apply_coord hφ 1 2, hsymm 1 2, fderiv_gradient_apply_coord hφ 2 1]
    simp
  · show ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 2)).ofLp 0
        - ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 0)).ofLp 2 = 0
    rw [fderiv_gradient_apply_coord hφ 2 0, hsymm 2 0, fderiv_gradient_apply_coord hφ 0 2]
    simp
  · show ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 0)).ofLp 1
        - ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 1)).ofLp 0 = 0
    rw [fderiv_gradient_apply_coord hφ 0 1, hsymm 0 1, fderiv_gradient_apply_coord hφ 1 0]
    simp

end Work.FTS.PressureOn.CurlGrad
