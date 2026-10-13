import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_slice_of_hasFDerivAt_uncurry

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

-- required full name (path convention): Work.FTS.PressureOn.Connect.timeDeriv_physVel_continuousOn_strip

/-! On the open time-strip `0 < t < S`, the time derivative `∂ₜ (physVel ω)` of the physical
velocity is continuous, as soon as the *joint* map `(x,t) ↦ physVel ω x t` is `C^{1,α}` on the
closed strip `ℝ³ × [0,S]`.

The point is that the open strip lies in the *interior* of the closed strip: there the joint
`C¹` hypothesis gives an honest Fréchet derivative, and `∂ₜ` of a slice is that Fréchet
derivative evaluated at `(0,1)`; continuity of the Fréchet derivative on the open strip (a
consequence of `ContDiffOn ℝ 1` on an open set) then transfers to `∂ₜ`. -/

-- `hS` is not needed for the argument (the open strip is empty when `S ≤ 0`).
set_option linter.unusedVariables false in
theorem timeDeriv_physVel_continuousOn_strip {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {S : ℝ}
    (hS : 0 < S)
    (hstrip : IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 S) := by
  -- The strip is open, and contained in the (closed) strip on which the joint `C^1`
  -- regularity of `physVel ω` is assumed.
  have hUopen : IsOpen ((Set.univ : Set Work.FTS.PressureOn.R3) ×ˢ Set.Ioo (0 : ℝ) S) :=
    (isOpen_univ : IsOpen (Set.univ : Set Work.FTS.PressureOn.R3)).prod
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) S))
  have hUsub : ((Set.univ : Set Work.FTS.PressureOn.R3) ×ˢ Set.Ioo (0 : ℝ) S) ⊆
      ((Set.univ : Set Work.FTS.PressureOn.R3) ×ˢ Set.Icc (0 : ℝ) S) :=
    Set.prod_mono subset_rfl Set.Ioo_subset_Icc_self
  have hcd : ContDiffOn ℝ 1 (Work.FTS.Physical.physVel ω).uncurry
      ((Set.univ : Set Work.FTS.PressureOn.R3) ×ˢ Set.Ioo (0 : ℝ) S) := hstrip.1.mono hUsub
  -- On the open strip, the Fréchet derivative of the joint velocity is continuous.
  have hcont : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      fderiv ℝ (Work.FTS.Physical.physVel ω).uncurry p (0, 1))
      ((Set.univ : Set Work.FTS.PressureOn.R3) ×ˢ Set.Ioo (0 : ℝ) S) :=
    (hcd.continuousOn_fderiv_of_isOpen hUopen le_rfl).clm_apply continuousOn_const
  -- It agrees there with the time derivative of the velocity slices.
  refine hcont.congr ?_
  intro p hp
  obtain ⟨x, t⟩ := p
  have hdiff : DifferentiableAt ℝ (Work.FTS.Physical.physVel ω).uncurry (x, t) :=
    (hcd.contDiffWithinAt hp).contDiffAt (hUopen.mem_nhds hp) |>.differentiableAt one_ne_zero
  have hd := Work.FTS.PressureOn.Connect.hasDerivAt_slice_of_hasFDerivAt_uncurry
    (v := Work.FTS.Physical.physVel ω) (x := x) (t := t) hdiff.hasFDerivAt
  simpa [FiniteTimeSingularity.timeDeriv] using hd.deriv

end Work.FTS.PressureOn.Connect
