import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.vorticity_cross_eq
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.PressureOn.CurlGrad

/-! ## Regularity of `gradient φ` for a `C²` function `φ`

`gradient φ = (toDual ℝ ℝ³).symm ∘ fderiv ℝ φ` is the composite of the continuous linear
equivalence `toDual` with `fderiv ℝ φ`, which is `C¹` as soon as `φ` is `C²`
(`ContDiff.fderiv_right`).  Hence `gradient φ` is `C¹`, differentiable everywhere with
derivative `fderiv ℝ (gradient φ)`, and compactly supported when `φ` is. -/

/-- `gradient φ` is `C¹` when `φ` is `C²`. -/
lemma contDiff_one_gradient {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (gradient φ) :=
  (LinearIsometryEquiv.contDiff (InnerProductSpace.toDual ℝ R3).symm).comp
    (hφ.fderiv_right (m := 1) (by norm_num))

/-- `gradient φ` is differentiable everywhere, with derivative `fderiv ℝ (gradient φ)`, when `φ`
is `C²`. -/
lemma gradient_hasFDerivAt {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) :
    ∀ x, HasFDerivAt (gradient φ) (fderiv ℝ (gradient φ) x) x := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hdiff : Differentiable ℝ (fun x => (InnerProductSpace.toDual ℝ R3).symm
      (fderiv ℝ φ x)) :=
    (LinearIsometryEquiv.differentiable (InnerProductSpace.toDual ℝ R3).symm).comp
      (hdf.differentiable (by norm_num))
  intro x
  exact hdiff.differentiableAt.hasFDerivAt

/-- `gradient φ` has compact support when `φ` does: its support is contained in the support of
`fderiv ℝ φ`, which is contained in `tsupport φ`. -/
lemma gradient_hasCompactSupport {φ : R3 → ℝ} (hcs : HasCompactSupport φ) :
    HasCompactSupport (gradient φ) := by
  refine (hcs.fderiv ℝ).mono ?_
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h
  exact hx (by simp [gradient, h])

/-- **Regularity of the field `x ↦ u x × ∇φ x`.**  For `u : ℝ³ → ℝ³` of class `C¹` and
`φ : ℝ³ → ℝ` of class `C²` with compact support, the vector field
`X := fun x => crossVec (u x) (gradient φ x)` is continuous, differentiable everywhere with
derivative `fderiv ℝ X x`, has compact support, and its divergence is integrable; moreover
`gradient φ` itself is differentiable everywhere with derivative `fderiv ℝ (gradient φ) x`:

this is exactly the list of hypotheses required by
`Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt X hcs hcont hdiff hint`.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.gradient_crossVec_bundle`.

Proof hints: `gradient φ = (toDual ℝ ℝ³).symm ∘ fderiv ℝ φ`, `ContDiffAt.fderiv_right` gives
differentiability of `fderiv ℝ φ` from `hφ` (`ContDiff ℝ 2`), and composing with the continuous
linear isometry `(toDual ℝ ℝ³).symm` gives `HasFDerivAt (gradient φ) (fderiv ℝ (gradient φ) x) x`
(`ContinuousLinearMap.hasFDerivAt` + `HasFDerivAt.comp`, then `.fderiv`).  For `X`: use
`Work.FTS.PressureOn.vorticityCross_isBoundedBilinearMap` (`IsBoundedBilinearMap.continuous`,
`IsBoundedBilinearMap.differentiableAt` and `DifferentiableAt.hasFDerivAt`) composed with the pair
`x ↦ (u x, gradient φ x)` (`Continuous.prodMk`, `DifferentiableAt.prod`/`DifferentiableAt.prod_mk`);
`HasCompactSupport` follows from `HasCompactSupport.mono'` with the compactly supported
`gradient φ` (its support is contained in `tsupport φ` via `support_fderiv_subset` and
`HasCompactSupport.fderiv`), since `crossVec a 0 = 0`.  Finally `Integrable (div X)`: `X` is locally
zero off its (compact) support, hence so is `fderiv ℝ X` and hence `div X`, which is also
continuous; use `Work.FTS.PressureOn.exists_norm_supp_bound` (in
`Submission/Work/FTS/PressureOn/integral_div_eq_zero_of_hasFDerivAt.lean`) to get a radius `R` with
`div X = 0` outside `Metric.closedBall 0 R`, then
`ContinuousOn.integrableOn_compact` plus `MeasureTheory.integrable_indicator_iff`. -/
theorem gradient_crossVec_bundle {u : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {φ : Work.FTS.PressureOn.R3 → ℝ} (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 2 φ)
    (hcs : HasCompactSupport φ) :
    (∀ x, HasFDerivAt (gradient φ) (fderiv ℝ (gradient φ) x) x)
      ∧ Continuous (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x))
      ∧ (∀ x, HasFDerivAt (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x))
          (fderiv ℝ (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x)) x) x)
      ∧ HasCompactSupport (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x))
      ∧ MeasureTheory.Integrable
          (FiniteTimeSingularity.div (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x))) := by
  -- `gradient φ` is `C¹`, hence continuous and differentiable everywhere
  have hgrad_cd : ContDiff ℝ 1 (gradient φ) := contDiff_one_gradient hφ
  have hgrad_cont : Continuous (gradient φ) := hgrad_cd.continuous
  have hgrad_fd : ∀ x, HasFDerivAt (gradient φ) (fderiv ℝ (gradient φ) x) x :=
    gradient_hasFDerivAt hφ
  -- the pointwise cross product as a bounded bilinear map
  have hB := vorticityCross_isBoundedBilinearMap
  -- `X := x ↦ u x × ∇φ x` is `C¹`, hence continuous and differentiable everywhere
  have hX_cd : ContDiff ℝ 1 (fun x => crossVec (u x) (gradient φ x)) :=
    (hB.contDiff (n := 1)).comp (hu.prodMk hgrad_cd)
  have hX_cont : Continuous (fun x => crossVec (u x) (gradient φ x)) :=
    hB.continuous.comp (hu.continuous.prodMk hgrad_cont)
  have hX_diff : ∀ x, HasFDerivAt (fun x => crossVec (u x) (gradient φ x))
      (fderiv ℝ (fun x => crossVec (u x) (gradient φ x)) x) x := by
    intro x
    have hp : HasFDerivAt (fun y => (u y, gradient φ y))
        ((fderiv ℝ u x).prod (fderiv ℝ (gradient φ) x)) x :=
      ((hu.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).prodMk (hgrad_fd x)
    exact ((hB.hasFDerivAt (u x, gradient φ x)).comp x hp).differentiableAt.hasFDerivAt
  -- compact support: the support of `X` is contained in that of `∇φ`, which is compact
  have hcsX : HasCompactSupport (fun x => crossVec (u x) (gradient φ x)) :=
    (gradient_hasCompactSupport hcs).mono (fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro h
      exact hx (by simp [h]))
  -- `div X` vanishes off a closed ball, so it has compact support, and it is continuous
  have hdivcs : HasCompactSupport (div (fun x => crossVec (u x) (gradient φ x))) := by
    obtain ⟨R, hRpos, hR⟩ :=
      exists_norm_supp_bound (fun x => crossVec (u x) (gradient φ x)) hcsX
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) ?_
    intro y hy
    rw [Function.mem_support] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (hR y (le_of_lt (not_le.mp h))).2
  have hdivcont : Continuous (div (fun x => crossVec (u x) (gradient φ x))) := by
    have hfdc : Continuous (fderiv ℝ (fun x => crossVec (u x) (gradient φ x))) :=
      hX_cd.continuous_fderiv (by norm_num)
    rw [show div (fun x => crossVec (u x) (gradient φ x))
        = fun y => ∑ i : Fin 3, (fderiv ℝ (fun x => crossVec (u x) (gradient φ x)) y
            (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) i from
      funext (div_eq_sum_single (fun x => crossVec (u x) (gradient φ x)))]
    refine continuous_finsetSum _ (fun i _ => ?_)
    have h1 : Continuous (fun y : R3 => fderiv ℝ (fun x => crossVec (u x) (gradient φ x)) y
        (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) := hfdc.clm_apply continuous_const
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) i).comp h1
  exact ⟨hgrad_fd, hX_cont, hX_diff, hcsX,
    hdivcont.integrable_of_hasCompactSupport hdivcs⟩

end Work.FTS.PressureOn.CurlGrad
