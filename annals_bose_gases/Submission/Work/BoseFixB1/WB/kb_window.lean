import ChallengeDeps
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.kb_window`

The diluteness window for FS's parameter `K_B = t^{-6/323}` (`t = μa³`).

`K_B³ t^{1/2} = t^{287/646}` (`Work.BoseFixB1.KB3_half_eq`, since
`-18/323 + 1/2 = 287/646 > 0`), a positive power of the diluteness.  Hence for
*any* positive threshold `π/(3C_A)` there is a window `μa³ ≤ ε₀` on which
`K_B³ t^{1/2} ≤ π/(3C_A)`; we take `ε₀ = (π/(3C_A))^{646/287}`.
-/

noncomputable section

namespace Work.BoseFixB1.WB

open Work.BoseBox

set_option autoImplicit false

/-- **The `K_B`-window.**  For every positive constant `C_A` there is a diluteness
window on which `K_B³ (μa³)^{1/2} ≤ π/(3C_A)`. -/
theorem kb_window {v : EuclideanSpace ℝ (Fin 3) → ℝ} {C_A : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hCA : 0 < C_A) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ Real.pi / (3 * C_A) := by
  set B : ℝ := Real.pi / (3 * C_A) with hBdef
  have hB : 0 < B := by rw [hBdef]; positivity
  refine ⟨B ^ (646 / 287 : ℝ), Real.rpow_pos_of_pos hB _, ?_⟩
  intro μ hμ ht
  rw [Work.BoseFixB1.KB3_half_eq hav hμ, Work.BoseBox.fsXp]
  rw [show (287 : ℝ) / 2 / 323 = 287 / 646 by norm_num]
  calc (μ * (_root_.BoseGases.a v) ^ 3) ^ (287 / 646 : ℝ)
      ≤ (B ^ (646 / 287 : ℝ)) ^ (287 / 646 : ℝ) :=
        Real.rpow_le_rpow (by positivity) ht (by norm_num)
    _ = B ^ ((646 / 287 : ℝ) * (287 / 646 : ℝ)) := (Real.rpow_mul hB.le _ _).symm
    _ = B := by rw [show (646 : ℝ) / 287 * (287 / 646) = 1 by norm_num, Real.rpow_one]

end Work.BoseFixB1.WB
