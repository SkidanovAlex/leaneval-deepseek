/-
# `Work.ConstructionInstance.vorticity_bound_of_strip`

A spacetime `C^{1,α}` bound on `u.uncurry` on the strip `ℝ³ × [0,S]` bounds the *vorticity of
each time slice* `u · s` uniformly for `s` in the strictly shorter strip `[0,T)`, `T < S`.

The reason for the strict inequality `T < S` is that every `s ∈ Ico 0 T` lies in the interior of
`Icc 0 S` as far as the *time* variable is concerned (in fact `s < T < S`), so the whole slice
`ℝ³ × {s}` sits inside the closed strip `ℝ³ × [0,S]` on which the regularity is assumed.  The
point that needs care is `s = 0` (and, more generally, points on the spatial boundary of the
strip, of which there are none since `univ` has empty boundary): there the joint derivative is
only available *within* the strip, so we use `fderivWithin ℝ u.uncurry (univ ×ˢ Icc 0 S)` and the
chain rule along the slice embedding `y ↦ (y, s)` rather than the honest `fderiv`.

Concretely: the `IsBoundedFunOn` clause of `IsContDiffHolderOn` gives a uniform bound `B` on
`‖fderivWithin ℝ u.uncurry (univ ×ˢ Icc 0 S) (y,σ)‖` over the strip; along a slice the derivative
of `u · s` is the spatial block `L ∘SL inl` of that within-derivative `L`, whose norm is at most
`‖L‖ ≤ B`; and `norm_vorticity_le` turns the spatial derivative bound into the curl bound
`‖ω‖ ≤ 3 ‖D(u·s)‖`.  The resulting constant is `3 * max B 0 ≥ 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.ConstructionInstance.norm_vorticity_le
import Submission.Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem vorticity_bound_of_strip {α : NNReal}
    {u : Work.ConstructionInstance.R3 → ℝ → Work.ConstructionInstance.R3} {S T : ℝ}
    (hST : T < S)
    (h : IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Ico 0 T, ∀ x : Work.ConstructionInstance.R3,
      ‖FiniteTimeSingularity.vorticity (fun y => u y s) x‖ ≤ K := by
  obtain ⟨hcd, hbdd, _⟩ := h
  -- A uniform bound on the joint (within-)derivative over the whole strip.
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ p ∈ Set.univ ×ˢ Set.Icc 0 S,
      ‖fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) p‖ ≤ B := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall
      (0 : (Work.ConstructionInstance.R3 × ℝ) →L[ℝ] Work.ConstructionInstance.R3)).1 hbdd
    refine ⟨max r 0, fun p hp => ?_⟩
    have hp' : fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) p ∈
        fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) '' (Set.univ ×ˢ Set.Icc 0 S) :=
      ⟨p, hp, rfl⟩
    have hh := hr hp'
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hh
    exact le_trans hh (le_max_left _ _)
  refine ⟨3 * max B 0, by positivity, fun s hs x => ?_⟩
  -- `s` lies in the closed time interval, so the whole slice `ℝ³ × {s}` is in the strip.
  have hsIcc : s ∈ Set.Icc 0 S := ⟨hs.1, le_of_lt (lt_trans hs.2 hST)⟩
  have hmem : (x, s) ∈ Set.univ ×ˢ Set.Icc 0 S := ⟨trivial, hsIcc⟩
  set L : (Work.ConstructionInstance.R3 × ℝ) →L[ℝ] Work.ConstructionInstance.R3 :=
    fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, s) with hLdef
  have hLbound : ‖L‖ ≤ B := hB (x, s) hmem
  -- The within-derivative of `u.uncurry` at `(x,s)`.
  have hdiff : DifferentiableWithinAt ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, s) :=
    (hcd.differentiableOn (by norm_num)) (x, s) hmem
  have hg : HasFDerivWithinAt u.uncurry L (Set.univ ×ˢ Set.Icc 0 S) (x, s) :=
    hdiff.hasFDerivWithinAt
  -- Chain rule along the slice embedding `y ↦ (y, s)`, whose derivative is `inl`.
  have hf : HasFDerivWithinAt (fun y : Work.ConstructionInstance.R3 => (y, s))
      (ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ) Set.univ x :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x s).hasFDerivWithinAt
  have hcomp := hg.comp x hf (fun y _ => hmem)
  have hslice : HasFDerivAt (fun y : Work.ConstructionInstance.R3 => u y s)
      (L ∘SL ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ) x :=
    hcomp.hasFDerivAt Filter.univ_mem
  have hfderiv : fderiv ℝ (fun y : Work.ConstructionInstance.R3 => u y s) x
      = L ∘SL ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ := hslice.fderiv
  -- The spatial block `L ∘SL inl` has norm at most `‖L‖`, since `inl` is an isometry.
  have hnormcomp : ‖L ∘SL ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ‖ ≤ ‖L‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
    calc ‖(L ∘SL ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ) v‖
        = ‖L (v, (0:ℝ))‖ := rfl
      _ ≤ ‖L‖ * ‖(v, (0:ℝ))‖ := ContinuousLinearMap.le_opNorm L (v, (0:ℝ))
      _ = ‖L‖ * ‖v‖ := by simp
  have hfd : ‖fderiv ℝ (fun y : Work.ConstructionInstance.R3 => u y s) x‖ ≤ B := by
    rw [hfderiv]
    exact le_trans hnormcomp hLbound
  calc ‖FiniteTimeSingularity.vorticity (fun y => u y s) x‖
      ≤ 3 * ‖fderiv ℝ (fun y : Work.ConstructionInstance.R3 => u y s) x‖ :=
        Work.ConstructionInstance.norm_vorticity_le _ _
    _ ≤ 3 * max B 0 := by
        have h2 : ‖fderiv ℝ (fun y : Work.ConstructionInstance.R3 => u y s) x‖ ≤ max B 0 :=
          le_trans hfd (le_max_left _ _)
        linarith

end Work.ConstructionInstance
