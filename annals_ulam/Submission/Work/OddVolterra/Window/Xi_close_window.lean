import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.Anchor.Xi_close

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The `Ξ`-row of the odd transition-slope system is close to the ball's row at `h = 0`.**
This is the `ε`-`δ` form of the Lipschitz estimate `Work.Anchor.Xi_close`: the first two
components of `Ξ` do not depend on `h`, and the last two are controlled by `C δ` with `δ` the
`C^{n+2}` bound on the perturbation. -/
theorem Xi_close_window (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ),
        ‖Work.OddVolterra.Xi n h s - Work.OddVolterra.Xi n 0 s‖ < ε := by
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := Work.Anchor.Xi_close n hn
  have h2C : (0 : ℝ) < 2 * C := by linarith
  refine ⟨min (1 / 100 : ℝ) (ε / (2 * C)),
    lt_min (by norm_num) (div_pos hε h2C), ?_⟩
  intro h hh hsupp hjet s hs
  have hδpos : 0 < min (1 / 100 : ℝ) (ε / (2 * C)) :=
    lt_min (by norm_num) (div_pos hε h2C)
  have hδ100 : min (1 / 100 : ℝ) (ε / (2 * C)) ≤ 1 / 100 := min_le_left _ _
  have hs' : s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ) := ⟨by linarith [hs.1], hs.2⟩
  have hb := hC h hh hsupp (min (1 / 100 : ℝ) (ε / (2 * C))) hδpos hδ100 hjet s hs'
  have hlt : C * min (1 / 100 : ℝ) (ε / (2 * C)) < ε := by
    have hle : min (1 / 100 : ℝ) (ε / (2 * C)) ≤ ε / (2 * C) := min_le_right _ _
    have h1 : C * min (1 / 100 : ℝ) (ε / (2 * C)) ≤ C * (ε / (2 * C)) :=
      mul_le_mul_of_nonneg_left hle hCpos.le
    have h2 : C * (ε / (2 * C)) = ε / 2 := by
      field_simp
    linarith
  linarith

end Work.OddVolterra.Window
