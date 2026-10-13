import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.Cyl.Frame
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Calculus glue for the cylindrical layer

General-purpose lemmas: the bridge between `fderiv` and one-dimensional derivatives along coordinate
lines, the coordinate form of the trace and of the curl, and the basic API of the partial derivative
`pd`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The standard basis -/

lemma basisVec_eq_basisFun (i : Fin 3) :
    basisVec i = EuclideanSpace.basisFun (Fin 3) ℝ i := by
  fin_cases i <;>
    simp [basisVec, e0, e1, eZ, FiniteTimeSingularity.e, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single]

/-! ## `fderiv` along coordinate lines -/

/-- `fderiv` applied to a vector is the derivative of the restriction of `f` to the corresponding
line. -/
theorem fderiv_apply_eq_deriv_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x v : E)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
  have h3 : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 :=
    h2.comp_hasDerivAt 0 h1
  exact h3.deriv.symm

/-- Partial derivative of a scalar field on `ℝ³` along the coordinate direction `i`, as a `deriv` of
a line. -/
theorem pd_eq_deriv_line (g : R3 → ℝ) (i : Fin 3) (x : R3) :
    pd i g x = deriv (fun t : ℝ => g (x + t • basisVec i)) 0 := rfl

/-! ## Coordinates of derivatives -/

lemma differentiableAt_coord (u : R3 → R3) (x : R3) (hd : DifferentiableAt ℝ u x) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => (u y) j) x :=
  ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (u x) j).comp x hd.hasFDerivAt).differentiableAt

lemma hasFDerivAt_coord (u : R3 → R3) (x : R3) (hd : DifferentiableAt ℝ u x) (j : Fin 3) :
    HasFDerivAt (fun y => (u y) j)
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).comp (fderiv ℝ u x)) x :=
  (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (u x) j).comp x hd.hasFDerivAt

lemma fderiv_coord (u : R3 → R3) (x : R3) (hd : DifferentiableAt ℝ u x) (j : Fin 3) :
    fderiv ℝ (fun y => (u y) j) x =
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).comp (fderiv ℝ u x) :=
  (hasFDerivAt_coord u x hd j).fderiv

/-- Coordinates of `fderiv` are the partial derivatives in the corresponding directions. -/
theorem fderiv_apply_coord (u : R3 → R3) (x : R3) (i j : Fin 3)
    (hd : DifferentiableAt ℝ u x) :
    (fderiv ℝ u x (basisVec i)) j = pd i (fun y => (u y) j) x := by
  have h1 : (fderiv ℝ u x (basisVec i)) j = fderiv ℝ (fun y => (u y) j) x (basisVec i) := by
    rw [fderiv_coord u x hd j, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  rw [h1, pd, fderiv_apply_eq_deriv_line _ _ _ (differentiableAt_coord u x hd j)]

/-! ## Trace and divergence in coordinates -/

/-- The trace of the derivative of a field is the sum of the diagonal entries of its Jacobian in the
standard basis. -/
theorem trace_fderiv_eq_sum (u : R3 → R3) (x : R3) :
    (fderiv ℝ u x).trace ℝ R3 = ∑ i, (fderiv ℝ u x (basisVec i)) i := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_inner, ← basisVec_eq_basisFun]
  rfl

/-- The divergence as a sum of one-dimensional derivatives. -/
theorem div_eq_sum_partials (u : R3 → R3) (x : R3) (hd : DifferentiableAt ℝ u x) :
    FiniteTimeSingularity.div u x = ∑ i, deriv (fun t : ℝ => (u (x + t • basisVec i)) i) 0 := by
  rw [FiniteTimeSingularity.div, trace_fderiv_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_apply_coord u x i i hd, pd_eq_deriv_line]

/-! ## The curl in coordinates -/

/-- The sum `e₀ × a + e₁ × b + e₂ × c` in coordinates. -/
lemma cross_basis_sum (a b c : R3) :
    crossProduct (basisVec 0) a + crossProduct (basisVec 1) b + crossProduct (basisVec 2) c =
      ![b 2 - c 1, c 0 - a 2, a 1 - b 0] := by
  funext j
  fin_cases j <;> simp [basisVec, FiniteTimeSingularity.e, cross_apply] <;> ring

/-- The curl of a vector field in coordinates. -/
theorem vorticity_eq_coordinates (u : R3 → R3) (x : R3) :
    FiniteTimeSingularity.vorticity u x =
      !₂[(fderiv ℝ u x (basisVec 1)) 2 - (fderiv ℝ u x (basisVec 2)) 1,
          (fderiv ℝ u x (basisVec 2)) 0 - (fderiv ℝ u x (basisVec 0)) 2,
          (fderiv ℝ u x (basisVec 0)) 1 - (fderiv ℝ u x (basisVec 1)) 0] := by
  rw [FiniteTimeSingularity.vorticity, Fin.sum_univ_three]
  apply PiLp.ext
  intro j
  fin_cases j <;> simp [basisVec, FiniteTimeSingularity.e, cross_apply] <;> ring

end Work.Cyl
