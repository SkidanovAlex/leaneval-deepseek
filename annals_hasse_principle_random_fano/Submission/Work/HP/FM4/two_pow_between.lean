import Mathlib

namespace Work.HP.FM4

/-- For every real `X ≥ 1` there is a dyadic scale comparable to it: `X ≤ 2^K ≤ 4X`.

Proof route: `K = Nat.log 2 ⌈X⌉₊ + 1`. Then `Nat.lt_pow_succ_log_self` gives
`⌈X⌉₊ < 2^K` hence `X ≤ ⌈X⌉₊ ≤ 2^K`, while `Nat.pow_log_le_self` gives
`2^K = 2·2^{log 2 ⌈X⌉₊} ≤ 2⌈X⌉₊ < 2(X+1) ≤ 4X` (using `Nat.ceil_lt_add_one` and `X ≥ 1`). -/
lemma two_pow_between (X : ℝ) (hX : 1 ≤ X) :
    ∃ K : ℕ, X ≤ (2:ℝ)^K ∧ (2:ℝ)^K ≤ 4 * X := by
  have hpos : (0:ℝ) < X := by linarith
  have hne : ⌈X⌉₊ ≠ 0 := by
    have : 1 ≤ ⌈X⌉₊ := Nat.one_le_ceil_iff.mpr hpos
    omega
  refine ⟨Nat.log 2 ⌈X⌉₊ + 1, ?_, ?_⟩
  · have h2 : ((⌈X⌉₊ : ℕ) : ℝ) < (2:ℝ) ^ (Nat.log 2 ⌈X⌉₊ + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌈X⌉₊
      simp only [Nat.succ_eq_add_one] at h
      exact_mod_cast h
    exact le_trans (Nat.le_ceil X) (le_of_lt h2)
  · have hlog : (2:ℕ) ^ Nat.log 2 ⌈X⌉₊ ≤ ⌈X⌉₊ := Nat.pow_log_le_self 2 hne
    have hceil : ((⌈X⌉₊ : ℕ) : ℝ) < X + 1 := Nat.ceil_lt_add_one (le_of_lt hpos)
    have hnat : (2:ℕ) ^ (Nat.log 2 ⌈X⌉₊ + 1) ≤ 2 * ⌈X⌉₊ := by
      rw [pow_succ']
      exact Nat.mul_le_mul_left 2 hlog
    have hmain : ((2:ℕ) ^ (Nat.log 2 ⌈X⌉₊ + 1) : ℝ) ≤ 4 * X := by
      have h1 : ((2:ℕ) ^ (Nat.log 2 ⌈X⌉₊ + 1) : ℝ) ≤ ((2 * ⌈X⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have h2 : ((2 * ⌈X⌉₊ : ℕ) : ℝ) = 2 * (⌈X⌉₊ : ℝ) := by push_cast; ring
      rw [h2] at h1
      linarith
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmain

end Work.HP.FM4
