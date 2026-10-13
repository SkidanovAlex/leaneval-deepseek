import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.BSSwirl.CrossAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl.VortVV

open FiniteTimeSingularity

/-- **The derivative of the vorticity (curl) operator.**

Mathematics: the curl `∇ × Ψ` of a field `Ψ : ℝ³ → ℝ³` is the *linear* differential operator
`∑ i, eᵢ × ∂ᵢΨ`.  Its Fréchet derivative at `x` in the direction `v` is obtained by
differentiating under the sum and commuting `∂ᵢ` with the derivative, giving
`v ↦ ∑ i, eᵢ × (D²Ψ(x)[v, eᵢ])`.

Formalisation: `vorticity Ψ x = ∑ i, crossR3 (e i) (fderiv ℝ Ψ x (e i))`
(`vorticity_eq_sum_crossR3`).  Each summand is the continuous linear map `crossBilin (e i)`
applied to the evaluation `y ↦ fderiv ℝ Ψ y (e i)`, whose derivative is
`(fderiv ℝ (fderiv ℝ Ψ) x).flip (e i)` by `HasFDerivAt.clm_apply` (the second factor being the
constant `e i`); `flip` is then eliminated with `ContinuousLinearMap.flip_apply`.  Smoothness of
`fderiv ℝ Ψ` (so that its Fréchet derivative exists) comes from `ContDiff.fderiv_right` applied
to `hΨ 2`. -/
theorem fderiv_vorticity_apply (Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3)
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (x v : Work.FTS.BSSwirl.R3) :
    fderiv ℝ (FiniteTimeSingularity.vorticity Ψ) x v
      = ∑ i : Fin 3, Work.FTS.BSSwirl.crossR3 (FiniteTimeSingularity.e i)
          (fderiv ℝ (fderiv ℝ Ψ) x v (FiniteTimeSingularity.e i)) := by
  -- `Ψ` is `C^∞`, hence `fderiv ℝ Ψ` is `C^1`, hence differentiable everywhere.
  have hdiff : DifferentiableAt ℝ (fderiv ℝ Ψ) x :=
    have h1 : ContDiff ℝ (1 : WithTop ℕ∞) (fderiv ℝ Ψ) :=
      ContDiff.fderiv_right (hΨ 2) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    (h1.differentiable (by norm_num)).differentiableAt
  -- The derivative of each summand of the coordinate expression of the curl.
  have key : ∀ i : Fin 3,
      HasFDerivAt (fun y => crossR3 (e i) (fderiv ℝ Ψ y (e i)))
        ((crossBilin (e i)).comp ((fderiv ℝ (fderiv ℝ Ψ) x).flip (e i))) x := by
    intro i
    have hc : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) x) x := hdiff.hasFDerivAt
    have hu : HasFDerivAt (fun _ : R3 => e i) (0 : R3 →L[ℝ] R3) x := hasFDerivAt_const _ _
    have h2 : HasFDerivAt (fun y => (fderiv ℝ Ψ y) (e i))
        ((fderiv ℝ (fderiv ℝ Ψ) x).flip (e i)) x := by
      simpa using hc.clm_apply hu
    exact (crossBilin (e i)).hasFDerivAt.comp x h2
  -- Differentiate the finite sum.
  have hsum : HasFDerivAt (fun y => ∑ i : Fin 3, crossR3 (e i) (fderiv ℝ Ψ y (e i)))
      (∑ i : Fin 3, (crossBilin (e i)).comp ((fderiv ℝ (fderiv ℝ Ψ) x).flip (e i))) x :=
    HasFDerivAt.fun_sum fun i _ => key i
  -- The curl is that sum, pointwise.
  have hvort : vorticity Ψ = fun y => ∑ i : Fin 3, crossR3 (e i) (fderiv ℝ Ψ y (e i)) := by
    funext y; exact vorticity_eq_sum_crossR3 Ψ y
  rw [hvort, hsum.fderiv, sum_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, crossBilin_apply]

end Work.FTS.BSSwirl.VortVV
