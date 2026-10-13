/-
# Continuity in time of the physical vorticity, from the joint `C^{1,α}` strips

Node: the physical bridge (`Submission/Work/FTS/PressureOn`).  This module proves

  `Work.FTS.PressureOn.continuousOn_time_omega_of_strips`

the *time*-continuity of the physical vorticity `ω` on a strip `[0,S]`, `S < T`, which is the
input of `Work.FTS.PressureOn.tendsto_timeDeriv_physVel`.

## The mathematics

The velocity `u := physVel ω` is jointly of class `C^{1,α}` on `ℝ³ × [0,S']` for every `S' < T`,
and the vorticity of each time slice `u(·,s)` is `ω(·,s)` (`hcurl`).  Hence `ω(·,s)` is the curl of
a family of fields whose *spatial* derivative depends continuously on `s`, and the curl is a
continuous function of that derivative.  The only point that needs care is `s = 0`, which is a
*boundary* point of the strip `ℝ³ × [0,S']`: there `ContDiffOn` on the closed strip only controls
the derivative *within* the strip, but (i) the derivative within the strip at `(x,0)` restricted
to the spatial directions *is* the honest derivative of the slice `u(·,0)` at `x` (the points
`(x + v, 0)` lie in the strip), and (ii) the within-derivative is continuous on the strip.  Two
elementary lemmas (`hasFDerivAt_slice_of_hasFDerivWithinAt`,
`fderiv_slice_eq_fderivWithin_prod`) package exactly this.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter
open scoped Topology NNReal Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## The curl of a spatial derivative -/

/-- The curl (vorticity) of a continuous linear map `ℝ³ →L[ℝ] ℝ³`, in exactly the form in which
it appears in `FiniteTimeSingularity.vorticity`: `∇×L = ∑ᵢ eᵢ ×₃ (L eᵢ)`. -/
noncomputable def curlOf (L : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i)))

/-- `curlOf` is continuous: it is a finite sum of compositions of the evaluation `L ↦ L eᵢ`
(with `eᵢ` fixed) and of the cross product with the fixed vector `eᵢ`. -/
theorem continuous_curlOf : Continuous curlOf := by
  unfold curlOf
  fun_prop

/-- `FiniteTimeSingularity.vorticity` is `curlOf` applied to the derivative; definitional. -/
theorem vorticity_eq_curlOf (u : R3 → R3) (x : R3) :
    FiniteTimeSingularity.vorticity u x = curlOf (fderiv ℝ u x) := rfl

/-! ## The derivative of a time slice, from a derivative within a set -/

/-- **The derivative of a time slice, from the derivative of the uncurried field within a set.**

If `u.uncurry` has derivative `f'` within `s` at `(x, s₀)`, and the points `(y, s₀)` for `y` near
`x` all lie in `s`, then the slice `y ↦ u y s₀` is differentiable at `x` with derivative the
spatial block `f' ∘SL inl` of `f'`.

This is what makes `ContDiffOn` on a *closed* strip (whose time-boundary `s₀ = 0` is not an
interior point) usable for the spatial derivatives of the boundary slice. -/
theorem hasFDerivAt_slice_of_hasFDerivWithinAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → ℝ → F} {s : Set (E × ℝ)} {x : E} {s₀ : ℝ}
    (hs : ∀ᶠ y in 𝓝 x, (y, s₀) ∈ s) {f' : (E × ℝ) →L[ℝ] F}
    (h : HasFDerivWithinAt (Function.uncurry u) f' s (x, s₀)) :
    HasFDerivAt (fun y => u y s₀) (f' ∘SL ContinuousLinearMap.inl ℝ E ℝ) x := by
  rw [hasFDerivWithinAt_iff_tendsto] at h
  rw [hasFDerivAt_iff_tendsto]
  have hmk0 : Tendsto (fun y : E => (y, s₀)) (𝓝 x) (𝓝 (x, s₀)) := by
    rw [nhds_prod_eq]
    exact tendsto_id.prodMk tendsto_const_nhds
  have hmk : Tendsto (fun y : E => (y, s₀)) (𝓝 x) (𝓝[s] (x, s₀)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hmk0 (by simpa using hs)
  refine (h.comp hmk).congr fun y => ?_
  have hsub : ((y, s₀) : E × ℝ) - (x, s₀) = ((y - x, (0 : ℝ)) : E × ℝ) := by simp
  have hnorm : ‖((y - x, (0 : ℝ)) : E × ℝ)‖ = ‖y - x‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  simp only [Function.comp_apply, Function.uncurry_apply_pair, hsub, hnorm]
  rfl

/-- The product-set form of `hasFDerivAt_slice_of_hasFDerivWithinAt`, for the strips
`univ ×ˢ I` that occur in the workspace. -/
theorem hasFDerivAt_slice_of_hasFDerivWithinAt_prod
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → ℝ → F} {I : Set ℝ} {s₀ : ℝ} (hs₀ : s₀ ∈ I) {x : E}
    {f' : (E × ℝ) →L[ℝ] F}
    (h : HasFDerivWithinAt (Function.uncurry u) f' (Set.univ ×ˢ I) (x, s₀)) :
    HasFDerivAt (fun y => u y s₀) (f' ∘SL ContinuousLinearMap.inl ℝ E ℝ) x :=
  hasFDerivAt_slice_of_hasFDerivWithinAt (s := Set.univ ×ˢ I)
    (Filter.Eventually.of_forall fun _ => Set.mem_prod.mpr ⟨Set.mem_univ _, hs₀⟩) h

/-- **The spatial derivative of a slice, through the derivative within a product set.**  If
`u.uncurry` is `C¹` within `univ ×ˢ I` at `(x, s₀)` and `s₀ ∈ I`, then the spatial derivative of
the slice `y ↦ u y s₀` at `x` is the composition of the derivative within `univ ×ˢ I` with the
inclusion `ℝ³ ↪ ℝ³ × ℝ`. -/
theorem fderiv_slice_eq_fderivWithin_prod {u : R3 → ℝ → R3} {I : Set ℝ} {s₀ : ℝ}
    (hs₀ : s₀ ∈ I) {x : R3}
    (h : ContDiffWithinAt ℝ 1 (Function.uncurry u) (Set.univ ×ˢ I) (x, s₀)) :
    fderiv ℝ (fun y => u y s₀) x
      = fderivWithin ℝ (Function.uncurry u) (Set.univ ×ˢ I) (x, s₀)
          ∘SL ContinuousLinearMap.inl ℝ R3 ℝ := by
  have hd : DifferentiableWithinAt ℝ (Function.uncurry u) (Set.univ ×ˢ I) (x, s₀) :=
    h.differentiableWithinAt one_ne_zero
  exact (hasFDerivAt_slice_of_hasFDerivWithinAt_prod hs₀ hd.hasFDerivWithinAt).fderiv

/-! ## The main statement -/

/-- **Continuity in time of the physical vorticity on the strips.**

If `u = physVel ω` is jointly `C^{1,α}` on `ℝ³ × [0,S']` for every `S' ∈ (0,T)` and the vorticity
of each time slice of `u` is `ω(·,s)`, then for every `x` the function `s ↦ ω x s` is continuous
on `[0,S]` for every `S ∈ (0,T)`. -/
theorem continuousOn_time_omega_of_strips {α : NNReal} {ω : R3 → ℝ → R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S) := by
  intro x
  obtain ⟨hcd, -, -⟩ := hstrips S hS
  -- the strip is a set with nonempty interior in the time direction
  have hU : UniqueDiffOn ℝ ((Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ))) :=
    UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS.1)
  -- the derivative within the strip is continuous on the strip
  have hcont : ContinuousOn
      (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S)) (Set.univ ×ˢ Set.Icc (0 : ℝ) S) :=
    hcd.continuousOn_fderivWithin hU le_rfl
  -- hence so is its spatial block at the fixed point `x`
  have hslice : ContinuousOn (fun s : ℝ =>
      fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s)) (Set.Icc 0 S) :=
    hcont.comp' (by fun_prop : ContinuousOn (fun s : ℝ => (x, s)) (Set.Icc 0 S))
      (fun s hs => ⟨trivial, hs⟩)
  have hclm : ContinuousOn (fun s : ℝ =>
      fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ)
      (Set.Icc 0 S) :=
    hslice.clm_comp continuousOn_const
  -- and the curl of the spatial block is `ω`
  refine (continuous_curlOf.comp_continuousOn hclm).congr fun s hs => ?_
  show ω x s = curlOf (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ)
  have hsT : s ∈ Set.Ico 0 T := ⟨hs.1, lt_of_le_of_lt hs.2 hS.2⟩
  have hwit : ContDiffWithinAt ℝ 1 (Function.uncurry (Work.FTS.Physical.physVel ω))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s) :=
    hcd.contDiffWithinAt ⟨trivial, hs⟩
  rw [← hcurl s hsT x, vorticity_eq_curlOf,
    fderiv_slice_eq_fderivWithin_prod (u := Work.FTS.Physical.physVel ω)
      (I := Set.Icc (0 : ℝ) S) hs hwit]

end Work.FTS.PressureOn
