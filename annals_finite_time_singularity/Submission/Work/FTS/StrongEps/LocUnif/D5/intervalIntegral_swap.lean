import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

theorem intervalIntegral_swap {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∫ z in a..b, ∫ θ in c..d, g z θ = ∫ θ in c..d, ∫ z in a..b, g z θ := by
  refine MeasureTheory.intervalIntegral_intervalIntegral_swap (F := g) ?_
  rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd]
  exact (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set (by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨le_of_lt hx.1, hx.2⟩, ⟨le_of_lt hy.1, hy.2⟩⟩)

end Work.FTS.StrongEps.LocUnif.D5
