import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- **Lipschitz (difference) form of the `L₁₂`-zero-mode bound.**

The zero-mode estimate `|L₁₂(f)(0)| ≤ C|f|_{ℋ⁴}` (`Work.FTS.OpenPkg.l12zero_field_all`) is applied
to the difference `f - g`: since `L₁₂` is *additive* on the open class with honest `ℋ⁴`-membership
(`Work.FTS.StrongEps.EComparison.L12_sub_HkMem`) we have
`L₁₂ f(0) - L₁₂ g(0) = L₁₂ (f - g)(0)`, and `HQo α 4 (f - g)` is exactly the hypothesis that lets
the zero-mode bound act on that difference.  The constant is the universal `3` of
`l12zero_field_all`, whose sub-additivity along `f - g` is all that is used. -/
theorem L12_lipschitz_field : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f g : Work.FTS.Galerkin.Fn,
    Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
    Work.FTS.VocabO.HQo α 4 (fun z θ => f z θ - g z θ) →
    |Work.Construction.L12 f 0 - Work.Construction.L12 g 0|
      ≤ C * Work.FTS.Nonlin.Xn α (fun z θ => f z θ - g z θ) := by
  obtain ⟨C, hC, h⟩ := Work.FTS.OpenPkg.l12zero_field_all
  refine ⟨C, hC, ?_⟩
  intro α hα f g hf hg hfg
  -- additivity of `L₁₂` on the open class turns the difference into `L₁₂(f - g)(0)`
  have hsub : Work.Construction.L12 (fun z θ => f z θ - g z θ) 0
      = Work.Construction.L12 f 0 - Work.Construction.L12 g 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hf.1 hg.1 hf.2 hg.2 0
      (by simp [Work.Spaces.Iz])
  rw [← hsub]
  exact h α hα (fun z θ => f z θ - g z θ) hfg

end Work.FTS.StrongEps
