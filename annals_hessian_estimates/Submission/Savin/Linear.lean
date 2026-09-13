/-
# The Hessian under a linear substitution

`hessOp (fun y => w (B y)) x = B† ∘ (hessOp w (B x)) ∘ B`

This is the input of the *linear theory* of the limiting equation
`tr (C ∘ D²w) = 0` of Savin's Proposition 4.1: with `B` chosen so that `B C B = 1`
(e.g. `B = C^{-1/2}`, or on an eigenbasis) the substituted function is harmonic, so the
harmonic Harnack/mean value/`C^3` approximation theory applies to it.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.HolderScale
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_add_linear_of_contDiffAt

open Metric MeasureTheory Filter
open Commons.Analysis.Calculus.FDeriv
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- Conjugating a symmetric operator by `B† · B` preserves symmetry. -/
theorem isSymm_adjoint_comp_comp {S : ℝ⁴ →L[ℝ] ℝ⁴} (hS : S.IsSymmetric)
    (B : ℝ⁴ →L[ℝ] ℝ⁴) : (B.adjoint.comp (S.comp B)).IsSymmetric := by
  have hS' : ∀ v w : ℝ⁴, ⟪S v, w⟫ = ⟪v, S w⟫ := fun v w => hS v w
  intro v w
  show ⟪(B.adjoint.comp (S.comp B)) v, w⟫ = ⟪v, (B.adjoint.comp (S.comp B)) w⟫
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left, hS' (B v) (B w),
    ContinuousLinearMap.adjoint_inner_right]

/-- **The Hessian under a linear substitution.** -/
theorem hessOp_comp_linear {B : ℝ⁴ →L[ℝ] ℝ⁴} {w : ℝ⁴ → ℝ} {x : ℝ⁴}
    (hw : ContDiffAt ℝ 2 w (B x)) :
    hessOp (fun y => w (B y)) x = B.adjoint.comp ((hessOp w (B x)).comp B) := by
  have hcont : ContDiffAt ℝ 2 (fun y : ℝ⁴ => w (B y)) x := hw.comp x B.contDiff.contDiffAt
  refine clm_eq_of_inner_self_eq (hessOp_symm_of_contDiffAt hcont)
    (isSymm_adjoint_comp_comp (hessOp_symm_of_contDiffAt hw) B) fun v => ?_
  have hchain : (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => w (B y))) x) v v
      = (fderiv ℝ (fderiv ℝ w) (B x)) (B v) (B v) := by
    have h := fderiv_fderiv_comp_add_linear_of_contDiffAt B (0 : ℝ⁴) w x v v
      (by simpa using hw)
    simpa using h
  have hleft : ⟪hessOp (fun y : ℝ⁴ => w (B y)) x v, v⟫
      = (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => w (B y))) x) v v :=
    InnerProductSpace.continuousLinearMapOfBilin_apply _ v v
  have hright : ⟪(B.adjoint.comp ((hessOp w (B x)).comp B)) v, v⟫
      = ⟪hessOp w (B x) (B v), B v⟫ := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_left]
  have hmiddle : (fderiv ℝ (fderiv ℝ w) (B x)) (B v) (B v)
      = ⟪hessOp w (B x) (B v), B v⟫ :=
    (InnerProductSpace.continuousLinearMapOfBilin_apply _ (B v) (B v)).symm
  rw [hleft, hchain, hmiddle, hright]

end

end Submission
