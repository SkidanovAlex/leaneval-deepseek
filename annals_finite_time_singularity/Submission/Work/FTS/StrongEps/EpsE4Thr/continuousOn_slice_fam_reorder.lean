import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.PZeroScheme

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-- **Reordering a slice family.**  If `(z, θ, τ) ↦ g z θ τ` is `C¹` on the open half-strip
`{z > 0} × {0 < θ < π/2} × [0,T]`, then the reordered family
`(τ, (z, θ)) ↦ g z θ τ` is continuous on `[0,T] × Quad`.

This is a pure change of variables: the map
`Φ : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ)`, `Φ (τ, (z, θ)) = (z, (θ, τ))` is continuous (it is built from
the projections of a product), and it maps `Icc 0 T ×ˢ Quad` into
`Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc 0 T` (the two sets have the same coordinates, in a different
order).  Then `g τ ↦ g z θ τ` is the composite of the `C¹` (hence continuous) map
`(z, (θ, τ)) ↦ g z θ τ` with `Φ`, restricted to the source set. -/
theorem continuousOn_slice_fam_reorder {g : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hg : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T)) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad) := by
  -- the reordering map `(τ, (z, θ)) ↦ (z, (θ, τ))` is continuous
  have hΦ : Continuous fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)) := by
    fun_prop
  -- it maps the target set to the set on which `hg` holds
  have hmap : Set.MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
      (Set.Icc 0 T ×ˢ Work.FTS.StrongEps.Quad)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T) := by
    intro q hq
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc] at hq ⊢
    exact ⟨hq.2.1, hq.2.2, hq.1⟩
  -- compose the continuity of `hg` with the reordering
  exact hg.continuousOn.comp hΦ.continuousOn hmap

end Work.FTS.StrongEps.EpsE4Thr
