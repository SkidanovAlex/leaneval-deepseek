import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Submission.Commons.Analysis.Calculus.laplacian_comp_add_smul

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Real
open scoped Real

/-- Chain rule for the derivative of the reflection of the argument of a differentiable
function: `∇(x ↦ u (-x)) = - ∇u(-x)`. -/
lemma fderiv_comp_neg_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} (x : E) :
    fderiv ℝ (fun y => u (-y)) x = - fderiv ℝ u (-x) := by
  have h := fderiv_comp_smul (-1 : ℝ) (f := u) (x := x)
  simpa using h

/-- The derivative of an even function is odd. -/
lemma fderiv_neg_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (heven : ∀ x, f (-x) = f x) (x : E) :
    fderiv ℝ f (-x) = - fderiv ℝ f x := by
  have h1 : fderiv ℝ (fun y => f (-y)) x = - fderiv ℝ f (-x) := fderiv_comp_neg_apply x
  have h2 : (fun y => f (-y)) = f := funext heven
  rw [h2] at h1
  have h3 : - fderiv ℝ f x = fderiv ℝ f (-x) := by
    have h := congrArg Neg.neg h1
    simpa using h
  exact h3.symm

/-- The Laplacian is invariant under the reflection `x ↦ -x` of the argument. -/
lemma laplacian_comp_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x : E) :
    Laplacian.laplacian (fun y => u (-y)) x = Laplacian.laplacian u (-x) := by
  let v := stdOrthonormalBasis ℝ E
  have h1 : Laplacian.laplacian (fun y => u (-y)) x
      = ∑ i, (iteratedFDeriv ℝ 2 (fun y => u (-y)) x) ![v i, v i] :=
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun y => u (-y)) v) x
  have h2 : Laplacian.laplacian u (-x)
      = ∑ i, (iteratedFDeriv ℝ 2 u (-x)) ![v i, v i] :=
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v) (-x)
  rw [h1, h2]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hfun : (fun y => u (-y)) = u ∘ ⇑(-1 : E →L[ℝ] E) := by
    funext y; simp
  rw [hfun]
  have hcomp := Commons.Analysis.Calculus.iteratedFDeriv_two_comp_clm
      (-1 : E →L[ℝ] E) x (v i) (by simpa using hu.contDiffAt)
  simp only [neg_apply, one_apply_eq_self] at hcomp
  rw [hcomp]
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp

/-- The weighted Laplacian `M u = -Δu + ⟪∇f, ∇u⟫` commutes with the reflection `x ↦ -x` when the
potential `f` is even. -/
theorem laplacian_weighted_comp_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f u : E → ℝ} (hf : ContDiff ℝ 2 f) (heven : ∀ x, f (-x) = f x)
    (hu : ContDiff ℝ 2 u) (x : E) :
    - Laplacian.laplacian (fun y => u (-y)) x
      + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => u (-y)) x))
    = - Laplacian.laplacian u (-x)
      + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f (-x)))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u (-x))) := by
  have hA : Laplacian.laplacian (fun y => u (-y)) x = Laplacian.laplacian u (-x) :=
    laplacian_comp_neg hu x
  have hB : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => u (-y)) x)
      = - (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u (-x)) := by
    rw [fderiv_comp_neg_apply (u := u) x, map_neg]
  have hC : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f (-x))
      = - (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) := by
    rw [fderiv_neg_of_even heven x, map_neg]
  rw [hA, hB, hC]
  simp only [inner_neg_left, inner_neg_right]

end Commons.Analysis.GaussianMeasure