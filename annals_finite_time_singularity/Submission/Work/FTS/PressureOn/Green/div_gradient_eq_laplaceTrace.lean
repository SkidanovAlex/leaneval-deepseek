import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `div (∇u) = laplaceTrace u`

`Work.FTS.PressureOn.Green.div_gradient_eq_laplaceTrace`: for a `C²` function `u : ℝ³ → ℝ` the
divergence of the gradient field equals the trace of the Hessian,
`div (fun z => ∇u z) = laplaceTrace u`.

Both sides are traces computed from `fderiv`:

* `div G x = ∑ᵢ (fderiv ℝ G x (eᵢ))ᵢ` — the trace in the standard orthonormal basis
  (`Work.FTS.PressureOn.trace_eq_sum_single`, a colleague's lemma);
* `laplaceTrace u x = ∑ᵢ fderiv ℝ (fun w => fderiv ℝ u w (eᵢ)) x (eᵢ)` (the definition).

## Route

The whole proof is the Fréchet–Riesz bookkeeping that turns the first of these sums into the
second.  Write `Φ := fderiv ℝ u : ℝ³ → (ℝ³ →L[ℝ] ℝ)` (the derivative of `u` as a functional),
so that the gradient field is

  `G := fun z => ∇u z = L ∘ Φ`,  `L := (toDual ℝ ℝ³).symm : (ℝ³ →L[ℝ] ℝ) →L[ℝ] ℝ³`

(the inverse Fréchet–Riesz representation, packaged as a continuous linear equivalence; for `ℝ`
it is genuinely linear).

* `u ∈ C²` gives `Φ ∈ C¹` (`contDiff_succ_iff_fderiv`), hence `Φ` is differentiable and
  `fderiv ℝ G x = L.comp (fderiv ℝ Φ x)` by the chain rule.  This is the only regularity input.
* For a functional `T : ℝ³ →L[ℝ] ℝ`, `(L T) i = ⟪L T, eᵢ⟫ = T (eᵢ)`
  (`InnerProductSpace.toDual_symm_apply`), so

    `(fderiv ℝ G x (eᵢ)) i = (fderiv ℝ Φ x (eᵢ)) (eᵢ)`.
* On the other side, `w ↦ fderiv ℝ u w (eᵢ)` is the composition of `Φ` with the evaluation
  `T ↦ T (eᵢ)` (a continuous linear map), so by the chain rule again

    `fderiv ℝ (fun w => fderiv ℝ u w (eᵢ)) x (eᵢ) = (fderiv ℝ Φ x (eᵢ)) (eᵢ)`.

The two sums therefore agree termwise.  No symmetry (Clairaut) of the second derivative is
needed — both sides are evaluated in the same two slots `(eᵢ, eᵢ)`.
-/

noncomputable section

namespace Work.FTS.PressureOn.Green

open Work.FTS.PressureOn

/-- The `i`-th coordinate of a vector of `ℝ³` is the inner product with the `i`-th basis vector
`FiniteTimeSingularity.e i`. -/
theorem coord_eq_inner_R3 (y : R3) (i : Fin 3) : y i = inner ℝ y (FiniteTimeSingularity.e i) := by
  simp [FiniteTimeSingularity.e, PiLp.inner_apply]

/-- The inverse Fréchet–Riesz representation, packaged as a continuous linear map, is the
underlying function of `(InnerProductSpace.toDual ℝ ℝ³).symm`. -/
theorem toDual_symm_eq_CLM (v : R3 →L[ℝ] ℝ) :
    ((InnerProductSpace.toDual ℝ R3).symm.toContinuousLinearEquiv.toContinuousLinearMap) v
      = (InnerProductSpace.toDual ℝ R3).symm v := rfl

theorem div_gradient_eq_laplaceTrace (u : Work.FTS.PressureOn.R3 → ℝ) (hu : ContDiff ℝ 2 u) :
    FiniteTimeSingularity.div (fun z => gradient u z) = Work.FTS.PressureOn.laplaceTrace u := by
  -- `fderiv ℝ u` is `C¹` because `u` is `C²`
  have hΦ : ContDiff ℝ 1 (fderiv ℝ u) :=
    ((contDiff_succ_iff_fderiv (f := u) (n := (1 : WithTop ℕ∞))).mp hu).2.2
  have hLdiff : ∀ y : R3, DifferentiableAt ℝ (fderiv ℝ u) y :=
    fun y => (hΦ.differentiable (by norm_num)).differentiableAt
  funext x
  -- the inverse Fréchet–Riesz map, as a continuous linear map
  set L : (R3 →L[ℝ] ℝ) →L[ℝ] R3 :=
    (InnerProductSpace.toDual ℝ R3).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLapply : ∀ v : R3 →L[ℝ] ℝ, L v = (InnerProductSpace.toDual ℝ R3).symm v :=
    fun v => toDual_symm_eq_CLM v
  -- the gradient field is `L ∘ fderiv ℝ u`, hence differentiable with the chain-rule derivative
  have hGderiv : HasFDerivAt (fun z => gradient u z)
      (L.comp (fderiv ℝ (fderiv ℝ u) x)) x := by
    have h1 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x :=
      (hLdiff x).hasFDerivAt
    have h2 : HasFDerivAt (fun T : R3 →L[ℝ] ℝ => L T) L (fderiv ℝ u x) :=
      ContinuousLinearMap.hasFDerivAt L
    have h3 := h2.comp x h1
    have hfeq : (fun z => gradient u z) = (fun T : R3 →L[ℝ] ℝ => L T) ∘ (fderiv ℝ u) := by
      funext z
      simp only [Function.comp_apply]
      show gradient u z = L (fderiv ℝ u z)
      rw [hLapply]
      rfl
    rw [← hfeq] at h3
    exact h3
  have hfG : fderiv ℝ (fun z => gradient u z) x = L.comp (fderiv ℝ (fderiv ℝ u) x) :=
    hGderiv.fderiv
  -- the trace of the Jacobian of the gradient, as a sum of diagonal entries
  rw [Work.FTS.PressureOn.div_eq_sum_single (fun z => gradient u z) x]
  rw [Work.FTS.PressureOn.laplaceTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- the chain rule for the `i`-th coordinate of the gradient
  have hRHS : fderiv ℝ (fun w => fderiv ℝ u w (FiniteTimeSingularity.e i)) x
        (FiniteTimeSingularity.e i)
      = (fderiv ℝ (fderiv ℝ u) x (FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) := by
    have hfun : (fun w => fderiv ℝ u w (FiniteTimeSingularity.e i))
        = (ContinuousLinearMap.apply ℝ ℝ (FiniteTimeSingularity.e i)) ∘ (fderiv ℝ u) := by
      funext w
      simp [ContinuousLinearMap.apply_apply]
    have hcomp := (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.apply ℝ ℝ (FiniteTimeSingularity.e i))).comp x (hLdiff x).hasFDerivAt
    rw [hfun, hcomp.fderiv]
    simp [ContinuousLinearMap.apply_apply]
  calc (fderiv ℝ (fun z => gradient u z) x (FiniteTimeSingularity.e i)) i
      = (L (fderiv ℝ (fderiv ℝ u) x (FiniteTimeSingularity.e i))) i := by
        rw [hfG]
        rfl
    _ = ((InnerProductSpace.toDual ℝ R3).symm
          (fderiv ℝ (fderiv ℝ u) x (FiniteTimeSingularity.e i))) i := by rw [hLapply]
    _ = inner ℝ ((InnerProductSpace.toDual ℝ R3).symm
          (fderiv ℝ (fderiv ℝ u) x (FiniteTimeSingularity.e i))) (FiniteTimeSingularity.e i) :=
        coord_eq_inner_R3 _ _
    _ = (fderiv ℝ (fderiv ℝ u) x (FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) :=
        InnerProductSpace.toDual_symm_apply
    _ = fderiv ℝ (fun w => fderiv ℝ u w (FiniteTimeSingularity.e i)) x
          (FiniteTimeSingularity.e i) := hRHS.symm

end Work.FTS.PressureOn.Green
