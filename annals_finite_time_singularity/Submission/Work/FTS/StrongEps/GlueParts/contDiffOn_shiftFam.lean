import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.GlueParts.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

/-- The fake-time shift `shiftFam H t = fun z θ τ => H z θ (τ - t)` of a jointly `C¹` family on
the slab `τ ∈ [0,δ]` is jointly `C¹` on the shifted slab `τ ∈ [t, t+δ]` (composition with the
affine map `(z,θ,τ) ↦ (z,θ,τ-t)`, via `ContDiffOn.comp`). -/
theorem contDiffOn_shiftFam {H : Work.FTS.Galerkin.Fam} {t δ : ℝ}
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ)) :
    ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongEps.shiftFam H t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) := by
  -- The affine reparametrisation `φ (z,θ,τ) = (z,θ,τ-t)`; it maps the shifted slab into the
  -- original one, and `uncurry3 (shiftFam H t) = uncurry3 H ∘ φ`.
  have hφ : ContDiffOn ℝ 1 (fun p : Work.FTS.StrongGlobal.P3 => (p.1, p.2.1, p.2.2 - t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) := by fun_prop
  have hmaps : Set.MapsTo (fun p : Work.FTS.StrongGlobal.P3 => (p.1, p.2.1, p.2.2 - t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
    rintro ⟨z, θ, τ⟩ ⟨hz, hθ, hτ⟩
    simp only [Set.mem_Icc] at hτ
    simp only [Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioo, Set.mem_prod]
    exact ⟨hz, hθ, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩
  exact hH.comp hφ hmaps

end Work.FTS.StrongEps.GlueParts
