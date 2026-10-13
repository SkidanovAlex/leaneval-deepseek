import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R2

theorem hasDerivAt_slice_pz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry f)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s : ℝ => f s θ) (Work.Spaces.pz f z θ) z := by
  -- `pz f z θ` is by definition the derivative of the `z`-slice, so it suffices to
  -- know that the slice is differentiable at `z`.
  rw [Work.Spaces.pz, hasDerivAt_deriv_iff]
  -- the domain `(0,∞) × (0,π/2)` is open, so `ContDiffOn` upgrades to `ContDiffAt`
  have hs : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hp : (z, θ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2)) := ⟨hz, hθ⟩
  have hca : ContDiffAt ℝ 1 (Function.uncurry f) (z, θ) := h.contDiffAt (hs.mem_nhds hp)
  have hd : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    hca.differentiableAt (by norm_num)
  -- compose with the differentiable curve `s ↦ (s, θ)`
  have hcurve : DifferentiableAt ℝ (fun s : ℝ => (s, θ)) z := by fun_prop
  exact hd.comp z hcurve

end Work.FTS.RegPkgGal.R2
