import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Blocks.alphaDz_pth_core_clean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.FTS.EllipticEst.RPFresh

/-- **`∂_θ` commutes with the `D_z`-iterates, pointwise on the open quadrant.**  This is the
Clairaut identity `∂_z∂_θ = ∂_θ∂_z` in the coordinates adapted to `D_z = z ∂_z`, packaged at a
single point: on the open quadrant `pth (DzIter i V) = DzIter i (pth V)` (`Blocks.pth_DzIter_eqOn_Q0`),
and `D_z` only sees the values of its argument on an angular slice, so the congruence can be
evaluated pointwise. -/
theorem pth_DzIter_apply {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (i : ℕ)
    {z θ : ℝ} (hz : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pth (Work.Spaces.DzIter i V) z θ
      = Work.Spaces.DzIter i (Work.Spaces.pth V) z θ :=
  Work.Blocks.pth_DzIter_eqOn_Q0 hV i hz

theorem OpIdentDz {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (i : ℕ) {z θ : ℝ}
    (hz : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ
      = Work.Spaces.DzIter (i + 1) (Work.Spaces.pth V) z θ := by
  obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz
  -- `Dz` is computed by a `deriv` along the angular slice, so it only depends on the values of
  -- its argument on a neighbourhood of that slice inside `Q0`.
  have hcongr : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ
      = Work.Spaces.Dz (Work.Spaces.DzIter i (Work.Spaces.pth V)) z θ := by
    have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter i V) z' θ)
        =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter i (Work.Spaces.pth V) z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
      exact pth_DzIter_apply hV i (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ0, hθ1⟩)
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [hev.deriv_eq]
  rw [hcongr, Work.Spaces.DzIter_succ]

end Work.FTS.EllipticEst.RPFresh
