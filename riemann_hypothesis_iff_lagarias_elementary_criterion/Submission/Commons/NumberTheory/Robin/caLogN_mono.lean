import Mathlib
import Submission.Commons.NumberTheory.Robin.caExp_anti_p

namespace Commons.NumberTheory.Robin

theorem caLogN_mono (ε : ℝ) (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≤ p)
    (h : k ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊) :
    k ≤ ⌊Real.log ((((q : ℝ) ^ (1 + ε)) - 1) / ((((q : ℝ) ^ (1 + ε))) - (q : ℝ))) / Real.log (q : ℝ)⌋₊ := by
  rcases eq_or_lt_of_le hqp with hpq | hpq
  · simpa [hpq] using h
  · exact le_trans h (Commons.NumberTheory.Robin.caExp_anti_p hq.two_le hp.two_le hε hpq)

end Commons.NumberTheory.Robin
