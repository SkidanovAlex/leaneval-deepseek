import Mathlib
import Submission.Work.BMF.SD.theta_sub_eq_sum_Ioc
import Submission.Work.BMF.SD.theta_window_increment_lower
import Submission.Work.BMF.SD.sum_log_Ioc_le_card_mul_log

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- **Primes in long windows.**  There is `A` such that for all `b, h` with `A ≤ b`, `0 < h ≤ b`
and `8b/(log b)² ≤ h`, the interval `(b, b+h]` contains at least `h/(2 log (2b))` primes.
(The intended proof imports `Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog`,
i.e. `∃ x₀, ∀ x ≥ x₀, |Chebyshev.theta x - x| ≤ x/(log x)²`.) -/
theorem prime_window_card_ge : ∃ A : ℝ, 0 < A ∧ ∀ b h : ℝ, A ≤ b → 0 < h → h ≤ b →
    8 * b / (Real.log b) ^ 2 ≤ h →
    h / (2 * Real.log (2 * b)) ≤
      (((Finset.Ioc ⌊b⌋₊ ⌊b + h⌋₊).filter Nat.Prime).card : ℝ) := by
  obtain ⟨X, hX⟩ := theta_window_increment_lower
  refine ⟨max X (Real.exp 4), ?_, ?_⟩
  · exact lt_of_lt_of_le (Real.exp_pos 4) (le_max_right _ _)
  · intro b h hAb hh hhb h8
    have hbexp : Real.exp 4 ≤ b := le_trans (le_max_right _ _) hAb
    have hXb : X ≤ b := le_trans (le_max_left _ _) hAb
    have hbh : b ≤ b + h := by linarith
    -- Chebyshev bridge: `θ (b+h) - θ b` is the sum of `log p` over the window's primes
    have hbridge := theta_sub_eq_sum_Ioc b (b + h) hbh
    -- Prime Number Theorem: the `θ`-increase is at least `5h/8`
    have hlow := hX b h hXb hh hhb h8
    -- each summand is at most `log (2b)`
    have hup := sum_log_Ioc_le_card_mul_log b h hhb
    have hLpos : 0 < Real.log (2 * b) := by
      have hexp4 : (1 : ℝ) < Real.exp 4 := by norm_num [Real.one_lt_exp_iff]
      exact Real.log_pos (by linarith)
    have hmain : (5 / 8) * h ≤
        (((Finset.Ioc ⌊b⌋₊ ⌊b + h⌋₊).filter Nat.Prime).card : ℝ) * Real.log (2 * b) := by
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (2 * b))]
    nlinarith [hmain, hh.le, hLpos]

end Work.BMF.SD
