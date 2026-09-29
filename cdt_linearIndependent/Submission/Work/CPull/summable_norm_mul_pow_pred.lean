import Mathlib

namespace Work.CPull

/-- If `∑ ‖a n‖ * n * sⁿ` converges and `0 ≤ r < s`, then `∑ ‖a n‖ * n * r^(n-1)`
converges: the ratio `r^(n-1) / sⁿ = (1/s) * (r/s)^(n-1)` is bounded. -/
theorem summable_norm_mul_pow_pred {a : ℕ → ℂ} {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (hrs : r < s) (hsum : Summable (fun n : ℕ => ‖a n‖ * n * s ^ n)) :
    Summable (fun n : ℕ => ‖a n‖ * (n : ℝ) * r ^ (n - 1)) := by
  have hne : s ≠ 0 := ne_of_gt hs
  -- majorant: `(1/s) • (‖a n‖ * n * sⁿ)`, summable by `hsum.mul_left`
  have hmaj : Summable (fun n : ℕ => (1/s) * (‖a n‖ * (n:ℝ) * s ^ n)) :=
    hsum.mul_left (1/s)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · positivity
  · cases n with
    | zero => simp
    | succ m =>
      have h1 : r ^ m ≤ s ^ m := pow_le_pow_left₀ hr (le_of_lt hrs) m
      have h2 : ‖a (m+1)‖ * ((m+1 : ℕ) : ℝ) * r ^ m ≤
          ‖a (m+1)‖ * ((m+1 : ℕ) : ℝ) * s ^ m :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : ‖a (m+1)‖ * ((m+1 : ℕ) : ℝ) * s ^ m
          = (1/s) * (‖a (m+1)‖ * ((m+1 : ℕ) : ℝ) * s ^ (m+1)) := by
        rw [pow_succ]
        field_simp
      calc ‖a (m+1)‖ * ((m+1:ℕ):ℝ) * r ^ (m + 1 - 1)
          = ‖a (m+1)‖ * ((m+1:ℕ):ℝ) * r ^ m := by rw [Nat.succ_sub_one]
        _ ≤ ‖a (m+1)‖ * ((m+1:ℕ):ℝ) * s ^ m := h2
        _ = (1/s) * (‖a (m+1)‖ * ((m+1:ℕ):ℝ) * s ^ (m+1)) := h3

end Work.CPull
