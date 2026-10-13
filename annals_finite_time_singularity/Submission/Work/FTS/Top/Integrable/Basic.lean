/-
# `Work.FTS.Top.Integrable.Basic` — the vorticity of the slices `u · s`

This is the supporting vocabulary of `Work.FTS.Top.intervalIntegrable_vortLInf` (the
Beale–Kato–Majda integrand of a `Work.FTS.Top.BlowupAt` is interval-integrable).

The point of the module is that the vorticity of a *time slice* `y ↦ u y s` can be read off the
*joint* derivative `fderiv ℝ u.uncurry (x,s)`:

* `curlOf L` is the curl `∑ᵢ eᵢ ×₃ (L eᵢ)` of a continuous linear map `L : ℝ³ →L[ℝ] ℝ³`, exactly
  the shape in which the curl of a differentiable field appears in
  `FiniteTimeSingularity.vorticity`;
* `continuous_curlOf` : `L ↦ curlOf L` is continuous;
* `fderiv_slice_eq` : at a point where `u.uncurry` is differentiable, the derivative of the slice
  is the spatial block `L ∘SL inl` of the joint derivative (chain rule along `y ↦ (y,t)`);
* `vorticity_eq_curlOf` : hence `vorticity (u · t) x = curlOf (fderiv u.uncurry (x,t) ∘SL inl)`;
* `continuousOn_vorticity_joint` : if `u.uncurry` is `C¹` on the closed strip `ℝ³ × [0,S]`, then
  the map `(x,s) ↦ ‖vorticity (u · s) x‖` is continuous on the *open* strip `ℝ³ × (0,S)` — there
  every point is an interior point of the closed strip, so `ContDiffOn` gives an honest `ContDiffAt`
  and `ContDiffAt.continuousAt_fderiv` applies.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.Top.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal Matrix ENNReal

namespace Work.FTS.Top.Integrable

/-- The curl (vorticity) of a continuous linear map `ℝ³ →L[ℝ] ℝ³`, in exactly the form in which
the curl of a differentiable field appears in `FiniteTimeSingularity.vorticity`:
`∇×L = ∑ᵢ eᵢ ×₃ (L eᵢ)`. -/
noncomputable def curlOf (L : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i)))

/-- `curlOf` is continuous (it is a finite sum of compositions of the continuous linear maps
`L ↦ L (e i)` and the bilinear cross product with the fixed vector `e i`). -/
theorem continuous_curlOf : Continuous curlOf := by
  unfold curlOf
  fun_prop

/-- The spatial derivative of the time slice `y ↦ u y t` at `x` is the restriction of the joint
derivative `fderiv ℝ u.uncurry (x,t)` to the first factor `ℝ³ → ℝ³ × ℝ`. -/
theorem fderiv_slice_eq {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    fderiv ℝ (fun y => u y t) x
      = (fderiv ℝ u.uncurry (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  rw [show (fun y : R3 => u y t) = u.uncurry ∘ (fun y => (y, t)) from rfl]
  rw [fderiv_comp x h (hasFDerivAt_prodMk_left x t).differentiableAt]
  rw [(hasFDerivAt_prodMk_left x t).fderiv]

/-- The vorticity of a slice, through the derivative of the joint field. -/
theorem vorticity_eq_curlOf {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    vorticity (fun y => u y t) x
      = curlOf ((fderiv ℝ u.uncurry (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) := by
  simp only [FiniteTimeSingularity.vorticity, curlOf, fderiv_slice_eq h]

/-- **Joint continuity of the vorticity.**  If `u.uncurry` is `C¹` on the closed strip
`ℝ³ × [0,S]` then `(x,s) ↦ ‖vorticity (u · s) x‖` is continuous on the open strip `ℝ³ × (0,S)`:
each point of the latter is an interior point of the closed strip, so `ContDiffOn` upgrades to
`ContDiffAt` and `fderiv ℝ u.uncurry` is continuous there. -/
theorem continuousOn_vorticity_joint {u : R3 → ℝ → R3} {S : ℝ}
    (hcd : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    ContinuousOn (fun p : R3 × ℝ => ‖vorticity (u · p.2) p.1‖) (Set.univ ×ˢ Set.Ioo 0 S) := by
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo 0 S : Set (R3 × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hcd' : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo 0 S) :=
    hcd.mono (Set.prod_mono_right Set.Ioo_subset_Icc_self)
  have hderiv : ContinuousOn (fderiv ℝ u.uncurry) (Set.univ ×ˢ Set.Ioo 0 S) :=
    hcd'.continuousOn_fderiv_of_isOpen hopen le_rfl
  have hcomp : ContinuousOn
      (fun p : R3 × ℝ => (fderiv ℝ u.uncurry p) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ))
      (Set.univ ×ˢ Set.Ioo 0 S) :=
    hderiv.clm_comp continuousOn_const
  have hcurl : ContinuousOn
      (fun p : R3 × ℝ => curlOf ((fderiv ℝ u.uncurry p) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)))
      (Set.univ ×ˢ Set.Ioo 0 S) :=
    continuous_curlOf.comp_continuousOn hcomp
  refine (hcurl.norm).congr (fun p hp => ?_)
  have hdiff : DifferentiableAt ℝ u.uncurry p :=
    (hcd'.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hp)
  rw [vorticity_eq_curlOf hdiff]

end Work.FTS.Top.Integrable
