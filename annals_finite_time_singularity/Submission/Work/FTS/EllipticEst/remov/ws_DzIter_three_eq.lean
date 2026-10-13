import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.WProductRule

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology

/-- Pointwise form of the second-order expansion of `D_z`: for a source `C^∞` on the open
quadrant, `D_z²F = D_zF + z²∂_z²F` at every interior point.  (This is the plain product-rule
computation `z∂_z(z∂_zF) = z∂_zF + z²∂_z²F`, proved here so that the file does not depend on
the deferred `ws_DzIter_two_eq`.) -/
private theorem DzIter_two_eq_pt {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
  have hg : HasDerivAt (fun z' : ℝ => Work.Spaces.pz F z' θ)
      (Work.Spaces.pzIter 2 F z θ) z := by
    simpa using hF.hasDerivAt_slice_pzIter 1 hθ hz
  have hAz : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz F z' θ)
      (Work.Spaces.pz F z θ + z * Work.Spaces.pzIter 2 F z θ) z := by
    have h := (hasDerivAt_id z).mul hg
    rw [show (id * fun z' : ℝ => Work.Spaces.pz F z' θ)
        = fun z' => z' * Work.Spaces.pz F z' θ from by funext z'; rfl] at h
    simpa using h
  rw [show Work.Spaces.DzIter 2 F z θ
        = z * deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z from rfl,
      hAz.deriv,
      show Work.Spaces.DzIter 1 F z θ = z * Work.Spaces.pz F z θ from rfl]
  ring

theorem ws_DzIter_three_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 3 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ
        + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  -- derivative of the `z`-slice of `z' ↦ z'² ∂_z²Ψ`, by the product rule
  have hgd : HasDerivAt (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
      (2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ) z := by
    have hp : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h3 : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ)
        (Work.Spaces.pzIter 3 Ψ z θ) z := hΨ.hasDerivAt_slice_pzIter 2 hθ hz
    have h := hp.mul h3
    rw [show ((fun z' : ℝ => z' ^ 2) * fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ)
        = fun z' => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ from by funext z'; rfl] at h
    simpa using h
  have hsum : HasDerivAt
      (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' θ + z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
      (Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ
        + (2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)) z :=
    (hΨ.hasDerivAt_slice_DzIter 1 hθ hz).add hgd
  -- the second-order expansion holds at every interior `z'`, hence eventually at `z`
  have hcongr : (fun z' : ℝ => Work.Spaces.DzIter 2 Ψ z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' θ
        + z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact DzIter_two_eq_pt hΨ hz' hθ
  calc Work.Spaces.DzIter 3 Ψ z θ
      = z * deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' θ
            + z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) z := by
        show z * deriv (fun z' : ℝ => Work.Spaces.DzIter 2 Ψ z' θ) z = _
        rw [hcongr.deriv_eq]
    _ = z * (Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ
            + (2 * z * Work.Spaces.pzIter 2 Ψ z θ
              + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ)) := by
        rw [hsum.deriv]
    _ = Work.Spaces.DzIter 2 Ψ z θ
          + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
        rw [show Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              = z * deriv (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) z from rfl,
            hgd.deriv,
            show Work.Spaces.DzIter 2 Ψ z θ
              = z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ from rfl]
        ring

end Work.FTS.EllipticEst.remov
