import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

theorem contDiff_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv g) ∧ Continuous (deriv g) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := by
    simpa using hg.iterate_deriv 1
  exact ⟨h, h.continuous⟩

end Work.FTS.LocData
