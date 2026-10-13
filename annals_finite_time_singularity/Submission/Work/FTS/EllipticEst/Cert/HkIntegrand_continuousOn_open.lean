import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst.Cert

/-- **Joint continuity of the `H^k`-integrand on the open quadrant.**  For `f` smooth on a
neighbourhood of the closed quadrant, `HkIntegrand α k f` is a finite sum of products of
continuous functions on `(0,∞) × (0,π/2)`: the iterated derivatives `D_z^i f`, `D_z^jD_θ^if` (via
`SmoothNbhd.DzIter`, `SmoothNbhd.DthIter`) and the weights `w(z)/sin(2θ)^{η/2}`,
`Wt α z θ = w(z)/sin(2θ)^{γ/2}` (all with `sin(2θ) > 0` there).  The `(0,∞)`-smoothness in `z`
comes from `ContDiffOn.fderiv_of_isOpen` on the open set `nbhU` on which `SmoothNbhd` is stated.
This is the `contOn_uncurry_HkIntegrand` helper that is *private* in
`Submission/Work/Spaces/HkMem_mixed_le.lean` (and likewise in `HkSq_mixed_le.lean`,
`LocData/HkMem_of_majorant.lean`); copy that short chain of private lemmas, or those lemmas must
be made public.  It is needed publicly here. -/
theorem HkIntegrand_continuousOn_open (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  -- `SmoothNbhd` smoothness on `nbhU = (-1,∞) × (-1,π/2+1)` restricts to the open
  -- quadrant `quadU = (-1,∞) × (0,π/2)`, on which the public continuity result applies.
  have hq : ContDiffOn ℝ ⊤ (Function.uncurry f) Work.Spaces.quadU :=
    h.mono (Set.prod_mono (le_refl _)
      (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])))
  exact Work.Spaces.continuousOn_HkIntegrand_Qd α k f hq

end Work.FTS.EllipticEst.Cert
