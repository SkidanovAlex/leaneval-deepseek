import Mathlib
import Submission.Work.Analysis.EndVar.Defs

/-!
# The height scale `l_{(N)} = C₀ LogLog N` controls `N` from below

`Work.Analysis.EndVar.heightScale C₀ N = C₀ * LogLog N` is the maximum height scale of §5 of
Krause--Mirek--Tao.  Inverting the chain

`l ≤ C₀ · LogLog N = C₀ · log₂(log₂(max N 2) + 2)`

gives `2^{l/C₀} ≤ log₂ N + 2`, hence the exponential lower bound for `N` used whenever a scale
`L` is admissible for `N`:

`2^{2^{L/C₀} - 2} ≤ N`   (for `1 ≤ C₀`, `1 ≤ L ≤ l_{(N)}`).

The intermediate estimate `2 ^ LogLog N ≤ Nat.log 2 N + 2` is proved separately; it is uniform in
`N` (the case `N ≤ 1` is checked directly).
-/

namespace Work.KMTAreas.A7

open Work.Analysis.EndVar

/-- The iterated logarithm is dominated by `Log N`:
`2 ^ LogLog N ≤ log₂ N + 2`.  Uniform in `N` (for `N ≤ 1` both sides are `2`). -/
lemma two_pow_logLogN_le (N : ℕ) : 2 ^ logLogN N ≤ Nat.log 2 N + 2 := by
  rcases le_or_gt N 1 with h | h
  · have : logLogN N = 1 := by interval_cases N <;> decide
    rw [this, pow_one]
    exact Nat.le_add_left 2 _
  · have hm : max N 2 = N := by omega
    have hl : logLogN N = Nat.log 2 (Nat.log 2 N + 2) := by simp only [logLogN, hm]
    rw [hl]
    exact Nat.pow_log_le_self 2 (by omega)

/-- Real form of `two_pow_logLogN_le`: `2 ^ (LogLog N) ≤ log₂ N + 2`
(here `2 ^ (LogLog N)` is the real power, the exponent being the natural number `LogLog N`). -/
lemma two_rpow_logLogN_le (N : ℕ) :
    (2 : ℝ) ^ (logLogN N : ℝ) ≤ (Nat.log 2 N : ℝ) + 2 := by
  rw [show (2 : ℝ) ^ (logLogN N : ℝ) = ((2 ^ logLogN N : ℕ) : ℝ) from
    (Real.rpow_natCast 2 (logLogN N)).trans (Nat.cast_pow 2 (logLogN N)).symm]
  exact_mod_cast two_pow_logLogN_le N

theorem heightScale_rpow_le {C₀ L N : ℕ} (hC₀ : 1 ≤ C₀) (hL : 1 ≤ L) (hN : 1 ≤ N)
    (h : L ≤ Work.Analysis.EndVar.heightScale C₀ N) :
    (2 : ℝ) ^ ((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) - 2) ≤ (N : ℝ) := by
  -- `l ≤ C₀ · LogLog N`, hence `l / C₀ ≤ LogLog N`
  have hC₀pos : (0 : ℝ) < C₀ := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  have hcast : (L : ℝ) ≤ (C₀ : ℝ) * (logLogN N : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    simpa only [heightScale, Nat.cast_mul] using this
  have hdiv : (L : ℝ) / (C₀ : ℝ) ≤ (logLogN N : ℝ) := by
    rw [div_le_iff₀ hC₀pos]
    linarith
  -- `2 ^ (l/C₀) ≤ log₂ N + 2`
  have hp : (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) ≤ (Nat.log 2 N : ℝ) + 2 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hdiv).trans
      (two_rpow_logLogN_le N)
  have he : (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) - 2 ≤ (Nat.log 2 N : ℝ) := by linarith
  -- exponentiate once more and use `2 ^ log₂ N ≤ N`
  calc (2 : ℝ) ^ ((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) - 2)
      ≤ (2 : ℝ) ^ (Nat.log 2 N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = ((2 ^ Nat.log 2 N : ℕ) : ℝ) :=
        (Real.rpow_natCast 2 (Nat.log 2 N)).trans (Nat.cast_pow 2 (Nat.log 2 N)).symm
    _ ≤ (N : ℝ) := by
        have := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
        exact_mod_cast this

end Work.KMTAreas.A7
