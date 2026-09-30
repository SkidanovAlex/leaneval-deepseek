import Mathlib
import Submission.Work.BMF.liouville.zetaTwPerron_rect
import Submission.Work.BMF.liouville.zetaTwSum_sub_main_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open MeasureTheory

noncomputable section

/-- **The χ = 1 Vinogradov–Korobov twisted sum**, from the ζ VK zero-free region and the
log-derivative bound in it.  This is `Work.BMF.liouville.zetaTwSum_sub_main_le` fed with the
contour-shift identity `Work.BMF.liouville.zetaTwPerron_rect`. -/
theorem zeta_tw_vk_sum_of_region
    (hreg : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₁ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hlog : ∃ c₂ B : ℝ, 0 < c₂ ∧ 0 < B ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₂ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B * (Real.log (|t| + 3)) ^ 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ,
      |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
      ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
        ≤ C * x * Real.exp (-(c * (Real.log x) ^ (1 / 10 : ℝ))) :=
  zetaTwSum_sub_main_le hreg hlog zetaTwPerron_rect

end

end Work.BMF.liouville
