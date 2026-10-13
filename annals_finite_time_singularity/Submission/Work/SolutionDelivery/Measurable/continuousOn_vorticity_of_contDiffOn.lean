import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Measurable

open scoped Matrix

/-- The curl (vorticity) of a continuous linear map `ℝ³ →L[ℝ] ℝ³`, in exactly the form in
which the curl of a differentiable field appears in `FiniteTimeSingularity.vorticity`:
`∇×L = ∑ᵢ eᵢ ×₃ (L eᵢ)`. -/
noncomputable def curlOf (L : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i)))

/-- `curlOf` is continuous (it is a finite sum of compositions of the continuous linear maps
`L ↦ L (e i)` and the bilinear cross product with the fixed vector `e i`). -/
theorem continuous_curlOf : Continuous curlOf := by
  unfold curlOf
  fun_prop

/-- The spatial derivative of the time slice `y ↦ u y t` at `x` is the restriction of the
joint derivative `fderiv ℝ u.uncurry (x,t)` to the first factor `ℝ³ → ℝ³ × ℝ`. -/
theorem fderiv_slice_eq {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    fderiv ℝ (fun y => u y t) x
      = (fderiv ℝ u.uncurry (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  rw [show (fun y : R3 => u y t) = u.uncurry ∘ (fun y => (y, t)) from rfl]
  rw [fderiv_comp x h (hasFDerivAt_prodMk_left x t).differentiableAt]
  rw [(hasFDerivAt_prodMk_left x t).fderiv]

/-- The vorticity of a slice through the derivative of the joint field. -/
theorem vorticity_eq_curlOf {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    FiniteTimeSingularity.vorticity (fun y => u y t) x
      = curlOf ((fderiv ℝ u.uncurry (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) := by
  simp only [FiniteTimeSingularity.vorticity, curlOf, fderiv_slice_eq h]

theorem continuousOn_vorticity_of_contDiffOn {u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {T R : ℝ}
    (hsmooth : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Work.SolutionDelivery.extWindow T)) :
    ContinuousOn (fun p : Work.SolutionDelivery.R3 × ℝ =>
        FiniteTimeSingularity.vorticity (fun y => u y p.2) p.1)
      (Metric.closedBall 0 R ×ˢ Set.Icc (-1) (T + 1)) := by
  let K : Set (R3 × ℝ) := Metric.closedBall 0 R ×ˢ Set.Icc (-1) (T + 1)
  -- `K` sits in the open set on which `u.uncurry` is `C¹`
  have hKsub : K ⊆ Set.univ ×ˢ extWindow T := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    exact ⟨trivial, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hopen : IsOpen (Set.univ ×ˢ extWindow T : Set (R3 × ℝ)) :=
    isOpen_univ.prod (isOpen_extWindow T)
  -- the joint derivative is continuous on `K`
  have hderiv : ContinuousOn (fderiv ℝ u.uncurry) K :=
    (hsmooth.continuousOn_fderiv_of_isOpen hopen le_rfl).mono hKsub
  have hcomp : ContinuousOn
      (fun p : R3 × ℝ => (fderiv ℝ u.uncurry p) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) K :=
    hderiv.clm_comp continuousOn_const
  refine (continuous_curlOf.comp_continuousOn hcomp).congr ?_
  intro p hp
  have hdiff : DifferentiableAt ℝ u.uncurry p :=
    (hsmooth.differentiableOn one_ne_zero).differentiableAt
      (hopen.mem_nhds (hKsub hp))
  exact vorticity_eq_curlOf hdiff

end Work.SolutionDelivery.Measurable
