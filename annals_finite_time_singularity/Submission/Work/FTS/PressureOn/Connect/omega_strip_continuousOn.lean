/-
# Joint continuity of the physical vorticity on a strip

This module lives in the `Connect` area of `Work.FTS.PressureOn` and proves

  `Work.FTS.PressureOn.Connect.omega_strip_continuousOn`

the *joint* (space-time) continuity of the physical vorticity `ω` on a strip `ℝ³ × [0,S]`,
`S < T`.  It is the joint analogue of
`Work.FTS.PressureOn.continuousOn_time_omega_of_strips` (imported here), which gives only the
*time* continuity at a fixed `x`.

## The mathematics

The velocity `u := physVel ω` is jointly of class `C^{1,α}` on `ℝ³ × [0,S']` for every `S' < T`,
and the vorticity of each time slice `u(·,s)` is `ω(·,s)` (`hcurl`).  The derivative of a slice
`u(·,s)` is the *spatial block* of the derivative `fderivWithin` of the uncurried field within the
strip `ℝ³ × [0,S]` (at the boundary `s = 0` this is exactly the point of the lemma
`fderiv_slice_eq_fderivWithin_prod` of `continuousOn_time_omega_of_strips`: the within-derivative
restricted to the spatial directions *is* the honest derivative of the slice).  Since
`fderivWithin` is continuous on the strip (`ContDiffOn.continuousOn_fderivWithin`, the strip being
a `UniqueDiffOn` set), and the curl `curlOf` is a continuous operation on continuous linear maps,
the map `(x,s) ↦ ω x s = curlOf (D_x u(·,s))(x)` is a composition of continuous-on-the-strip maps.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter
open scoped Topology NNReal Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

-- required full name (path convention): Work.FTS.PressureOn.Connect.omega_strip_continuousOn
theorem omega_strip_continuousOn {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    ContinuousOn (Function.uncurry ω) (Set.univ ×ˢ Set.Icc 0 S) := by
  obtain ⟨hcd, -, -⟩ := hstrips S hS
  -- the strip has nonempty interior in the time direction, so it is a `UniqueDiffOn` set
  have hU : UniqueDiffOn ℝ
      ((Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (Work.FTS.PressureOn.R3 × ℝ))) :=
    UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS.1)
  -- the derivative within the strip is continuous on the strip
  have hcont : ContinuousOn
      (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S)) (Set.univ ×ˢ Set.Icc (0 : ℝ) S) :=
    hcd.continuousOn_fderivWithin hU le_rfl
  -- hence so is its spatial block
  have hclm : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) p ∘SL ContinuousLinearMap.inl ℝ Work.FTS.PressureOn.R3 ℝ)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) S) :=
    hcont.clm_comp continuousOn_const
  -- and the curl of the spatial block is `ω`
  refine (continuous_curlOf.comp_continuousOn hclm).congr fun p hp => ?_
  obtain ⟨-, hs⟩ := Set.mem_prod.mp hp
  show ω p.1 p.2 = curlOf (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) p ∘SL ContinuousLinearMap.inl ℝ Work.FTS.PressureOn.R3 ℝ)
  have hsT : p.2 ∈ Set.Ico 0 T := ⟨hs.1, lt_of_le_of_lt hs.2 hS.2⟩
  have hwit : ContDiffWithinAt ℝ 1 (Function.uncurry (Work.FTS.Physical.physVel ω))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) S) p :=
    hcd.contDiffWithinAt ⟨trivial, hs⟩
  rw [← hcurl p.2 hsT p.1, vorticity_eq_curlOf,
    fderiv_slice_eq_fderivWithin_prod (u := Work.FTS.Physical.physVel ω)
      (I := Set.Icc (0 : ℝ) S) hs hwit]

end Work.FTS.PressureOn.Connect
