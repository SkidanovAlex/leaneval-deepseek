import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

open Work.FTS.PressureOn

/-! ## Symmetry of second derivatives, in evaluation form

The library lemma `IsSymmSndFDerivAt.eq` states the symmetry of second derivatives for a `C²`
function `g` in the form
`fderiv ℝ (fderiv ℝ g) x v w = fderiv ℝ (fderiv ℝ g) x w v`,
i.e. through the bundled derivative `fderiv ℝ (fderiv ℝ g) x`.  For the computation below it is
more convenient to have the same statement in *evaluation* form, with the two directions appearing
as the directions of the outer `fderiv` and of the inner evaluation.  The two forms are related by
`fderiv_clm_apply` applied to the family `y ↦ fderiv ℝ g y` of continuous linear maps and the
constant map `y ↦ v`. -/

/-- **Symmetry of the second derivative in evaluation form.**  For a function `g` that is `C²` at
`x` and vectors `v`, `w`, the two mixed second directional derivatives agree:
`∂_w (y ↦ ∂_v g y) x = ∂_v (y ↦ ∂_w g y) x`. -/
private lemma sndFDeriv_eval_swap {g : R3 → ℝ} {x : R3}
    (hg : ContDiffAt ℝ 2 g x) (v w : R3) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun y => fderiv ℝ g y v) x = (fderiv ℝ (fderiv ℝ g) x).flip v := by
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  have h2 : fderiv ℝ (fun y => fderiv ℝ g y w) x = (fderiv ℝ (fderiv ℝ g) x).flip w := by
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  rw [h1, h2, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact ((hg.isSymmSndFDerivAt (by norm_num)).eq v w).symm

/-- The Laplacian `laplaceTrace u x = ∑ᵢ ∂ᵢ∂ᵢ u x` (trace of the Hessian in the standard basis
`FiniteTimeSingularity.e`, defined in `Submission/Work/FTS/PressureOn/Defs.lean`) commutes with a
first partial derivative: for a `C³` function `Ψ : ℝ³ → ℝ` and every coordinate `i`,
`Δ (∂ᵢ Ψ) = ∂ᵢ (Δ Ψ)` as functions.  This is a pure Clairaut/symmetry-of-second-derivatives fact. -/
theorem laplaceTrace_fderiv_comm {Ψ : Work.FTS.PressureOn.R3 → ℝ} (hΨ : ContDiff ℝ 3 Ψ)
    (i : Fin 3) :
    Work.FTS.PressureOn.laplaceTrace (fun z : Work.FTS.PressureOn.R3 => fderiv ℝ Ψ z
        (FiniteTimeSingularity.e i))
      = fun z : Work.FTS.PressureOn.R3 => fderiv ℝ (Work.FTS.PressureOn.laplaceTrace Ψ) z
          (FiniteTimeSingularity.e i) := by
  -- Both sides are sums over `j : Fin 3` of third-order partial derivatives of `Ψ`; the `j`-th
  -- summand of the left side is `∂_j ∂_j ∂_i Ψ x` and that of the right side is `∂_i ∂_j ∂_j Ψ x`.
  funext x
  -- `fun z => fderiv ℝ Ψ z v` is `C²` for every direction `v` (it is `∂_v Ψ`, and `Ψ` is `C³`).
  have hC2 : ∀ v : R3, ContDiff ℝ 2 (fun z : R3 => fderiv ℝ Ψ z v) := fun v =>
    (hΨ.contDiff_fderiv_apply (m := 2) (by norm_num)).comp
      (contDiff_id.prodMk (contDiff_const (c := v)))
  -- Likewise `y ↦ ∂_v (∂_v Ψ) y` is `C¹`, hence differentiable.
  have hC1 : ∀ v : R3, ContDiff ℝ 1 (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z v) y v) :=
    fun v => ((hC2 v).contDiff_fderiv_apply (m := 1) (by norm_num)).comp
      (contDiff_id.prodMk (contDiff_const (c := v)))
  -- The `j`-th summands agree: exchange `∂_i` and `∂_j` (second derivatives of `Ψ`), then
  -- `∂_j` and `∂_i` (second derivatives of `∂_j Ψ`).
  have key : ∀ j : Fin 3,
      fderiv ℝ (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i))
          y (FiniteTimeSingularity.e j)) x (FiniteTimeSingularity.e j)
        = fderiv ℝ (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j))
          y (FiniteTimeSingularity.e j)) x (FiniteTimeSingularity.e i) := by
    intro j
    have hfun : (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i))
          y (FiniteTimeSingularity.e j))
        = (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j))
          y (FiniteTimeSingularity.e i)) := by
      funext y
      exact sndFDeriv_eval_swap (hΨ.contDiffAt.of_le (by norm_num)) (FiniteTimeSingularity.e i)
        (FiniteTimeSingularity.e j)
    rw [hfun]
    exact sndFDeriv_eval_swap ((hC2 (FiniteTimeSingularity.e j)).contDiffAt)
      (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e j)
  have hlt : laplaceTrace (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i)) x
      = ∑ j : Fin 3, fderiv ℝ (fun y : R3 =>
          fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i)) y
            (FiniteTimeSingularity.e j)) x (FiniteTimeSingularity.e j) := rfl
  have hrt : fderiv ℝ (laplaceTrace Ψ) x (FiniteTimeSingularity.e i)
      = ∑ j : Fin 3, fderiv ℝ (fun y : R3 =>
          fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j)) y
            (FiniteTimeSingularity.e j)) x (FiniteTimeSingularity.e i) := by
    have hfun : laplaceTrace Ψ
        = fun y : R3 => ∑ j : Fin 3, fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j))
            y (FiniteTimeSingularity.e j) := rfl
    rw [hfun]
    have hd : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
        DifferentiableAt ℝ (fun y : R3 =>
          fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j)) y
            (FiniteTimeSingularity.e j)) x :=
      fun j _ => ((hC1 (FiniteTimeSingularity.e j)).differentiable (by norm_num)).differentiableAt
    rw [fderiv_fun_sum hd]
    simp
  rw [hlt, hrt]
  exact Finset.sum_congr rfl (fun j _ => key j)

end Work.FTS.PressureOn.PoissonAux
