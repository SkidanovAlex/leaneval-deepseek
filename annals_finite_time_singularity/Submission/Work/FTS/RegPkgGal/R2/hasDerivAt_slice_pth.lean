import Mathlib.Analysis.Calculus.ContDiff.Comp
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

theorem hasDerivAt_slice_pth {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry f)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s : ℝ => f z s) (Work.Spaces.pth f z θ) θ := by
  -- The angular slice `s ↦ (z, s)` is `C¹` and maps the angular interval into the
  -- product on which `uncurry f` is `C¹`, so the composite `s ↦ f z s` is `C¹`.
  have hslice : ContDiffOn ℝ 1 (fun s : ℝ => (z, s)) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    fun_prop
  have hmap : Set.MapsTo (fun s : ℝ => (z, s)) (Set.Ioo (0:ℝ) (Real.pi / 2))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) :=
    fun s hs => ⟨hz, hs⟩
  have hcomp : ContDiffOn ℝ 1 (fun s : ℝ => f z s) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    have h2 := h.comp hslice hmap
    simpa [Function.comp_def, Function.uncurry] using h2
  -- Hence the slice is differentiable at `θ`, and `deriv` of the slice is exactly
  -- `Work.Spaces.pth f z θ` by definition.
  have hda : DifferentiableAt ℝ (fun s : ℝ => f z s) θ :=
    (hcomp.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  simpa [Work.Spaces.pth] using hda.hasDerivAt

end Work.FTS.RegPkgGal.R2
