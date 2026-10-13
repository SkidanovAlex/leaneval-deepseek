import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt

theorem deriv_comp_clamp {F : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => F (max 0 (min θ' (Real.pi / 2)))) θ = deriv F θ := by
  -- Near `θ ∈ (0, π/2)` the clamp `max 0 (min · (π/2))` is the identity, so the two
  -- functions agree on a neighbourhood of `θ`; hence their derivatives at `θ` coincide.
  have h : (fun θ' => F (max 0 (min θ' (Real.pi / 2)))) =ᶠ[nhds θ] F := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    show F (max 0 (min θ' (Real.pi / 2))) = F θ'
    rw [min_eq_left hθ'.2.le, max_eq_right hθ'.1.le]
  exact h.deriv_eq

end Work.FTS.FireFix.Clauses.PsiWt
