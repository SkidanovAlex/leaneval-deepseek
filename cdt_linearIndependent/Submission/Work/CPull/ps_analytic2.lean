import Mathlib
import Submission.Work.CPull.powerSeries_hasDerivAt

namespace Work.CPull

theorem ps_analytic2 (c : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖c n‖ ≤ C * (1 / 4 : ℝ) ^ n) :
    (∀ y : ℂ, ‖y‖ < 2 → Summable fun n : ℕ => c n * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 2 → Summable fun n : ℕ => (n : ℂ) * c n * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 2 → Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 2 → HasDerivAt (fun z : ℂ => ∑' n : ℕ, c n * z ^ n)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) y) := by
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  have hb' : ∀ n : ℕ, ‖c n‖ ≤ (C + 1) * (1 / 4 : ℝ) ^ n := by
    intro n
    have hp : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := pow_nonneg (by norm_num) n
    have hn := hb n
    nlinarith [hn, hp]
  obtain ⟨h1, h2, h3, h4⟩ := powerSeries_hasDerivAt c (C + 1) hCpos hb'
  exact ⟨fun y hy => h1 y (by linarith), fun y hy => h2 y (by linarith),
    fun y hy => h3 y (by linarith), fun y hy => h4 y (by linarith)⟩

end Work.CPull
