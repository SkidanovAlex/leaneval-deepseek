import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.Physical.Defs
import Submission.Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The time derivative of the physical velocity, from joint `C^{1,α}` regularity

If `u = physVel ω` is jointly `C^{1,α}` on the strip `ℝ³ × [0,S]`, then at every time
`t ∈ (0,S)` the time slice `s ↦ u x s` is differentiable at `t`, with derivative the time
derivative `∂ₜ u x t = timeDeriv (physVel ω) x t`.

The point `(x,t)` lies in the *interior* of the strip `univ ×ˢ Icc 0 S` as soon as `0 < t < S`,
so `ContDiffOn ℝ 1` upgrades to `ContDiffAt`, hence to differentiability of the uncurried field;
the time slice is the composition of `u.uncurry` with the curve `s ↦ (x,s)` (whose derivative is
`(0,1)`), and the `t`-block of the joint derivative is `timeDeriv`
(`Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply`).
-/

namespace Work.FTS.PressureOn.Connect

open Set Filter

theorem hasDerivAt_physVel_time {α : NNReal} {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {S t : ℝ} {x : Work.FTS.PressureOn.R3} (ht : t ∈ Set.Ioo 0 S)
    (hstrip : IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 S)) :
    HasDerivAt (fun s => Work.FTS.Physical.physVel ω x s)
      (FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t) t := by
  obtain ⟨ht0, htS⟩ := ht
  -- `(x,t)` is an interior point of the strip `univ ×ˢ Icc 0 S` because `0 < t < S`.
  have hnhds : (Set.univ ×ˢ Set.Icc (0 : ℝ) S) ∈ nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Icc_mem_nhds ht0 htS)
  have hcd : ContDiffAt ℝ 1 (Work.FTS.Physical.physVel ω).uncurry (x, t) :=
    hstrip.1.contDiffAt hnhds
  have hf : HasFDerivAt (Work.FTS.Physical.physVel ω).uncurry
      (fderiv ℝ (Work.FTS.Physical.physVel ω).uncurry (x, t)) (x, t) :=
    (hcd.differentiableAt (by simp)).hasFDerivAt
  -- the time slice is `u.uncurry` composed with the curve `s ↦ (x,s)`, of derivative `(0,1)`.
  have hcurve : HasDerivAt (fun s : ℝ => ((x, s) : Work.FTS.PressureOn.R3 × ℝ))
      ((0 : Work.FTS.PressureOn.R3), (1 : ℝ)) t := by
    simpa using (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t).hasDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => Work.FTS.Physical.physVel ω x s)
      ((fderiv ℝ (Work.FTS.Physical.physVel ω).uncurry (x, t))
        ((0 : Work.FTS.PressureOn.R3), (1 : ℝ))) t :=
    hf.comp_hasDerivAt t hcurve
  -- the `t`-block of the joint derivative is the time derivative.
  have hL : (fderiv ℝ (Work.FTS.Physical.physVel ω).uncurry (x, t))
      ((0 : Work.FTS.PressureOn.R3), (1 : ℝ))
      = FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t := by
    rw [Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply hf (0 : Work.FTS.PressureOn.R3) (1 : ℝ)]
    simp
  rw [hL] at hcomp
  exact hcomp

end Work.FTS.PressureOn.Connect
