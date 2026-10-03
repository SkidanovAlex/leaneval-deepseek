import Mathlib

namespace Work.Horn.FatouQ

/-- Binomial-type second-order estimate: for `‖s‖ ≤ 1` and any `m : ℕ`,
`(1+s)^m - 1 - m s` is bounded by `m * 2^m * ‖s‖^2`.  Proved by the recurrence
`E_{m+1} = (1+s) E_m + m s^2`, `E_m = (1+s)^m - 1 - m s`. -/
lemma norm_pow_sub_one_sub_mul_le (s : ℂ) (hs : ‖s‖ ≤ 1) (m : ℕ) :
    ‖(1 + s) ^ m - 1 - (m : ℂ) * s‖ ≤ (m : ℝ) * (2 : ℝ) ^ m * ‖s‖ ^ 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hrec : (1 + s) ^ (k+1) - 1 - ((k+1 : ℕ) : ℂ) * s
        = (1+s) * ((1+s)^k - 1 - (k:ℂ)*s) + (k:ℂ) * s^2 := by
      push_cast
      rw [pow_succ]
      ring
    rw [hrec]
    have h1s : ‖1 + s‖ ≤ 2 := by
      have h := norm_add_le (1:ℂ) s
      simp only [norm_one] at h
      linarith
    calc ‖(1+s) * ((1+s)^k - 1 - (k:ℂ)*s) + (k:ℂ) * s^2‖
        ≤ ‖(1+s) * ((1+s)^k - 1 - (k:ℂ)*s)‖ + ‖(k:ℂ) * s^2‖ := norm_add_le _ _
      _ = ‖1+s‖ * ‖(1+s)^k - 1 - (k:ℂ)*s‖ + (k:ℝ) * ‖s‖^2 := by
            rw [norm_mul, norm_mul, norm_natCast, norm_pow]
      _ ≤ 2 * ((k:ℝ) * (2:ℝ)^k * ‖s‖^2) + (k:ℝ) * ‖s‖^2 := by
            exact add_le_add (mul_le_mul h1s ih (norm_nonneg _) (by positivity)) le_rfl
      _ ≤ ((k+1 : ℕ) : ℝ) * (2:ℝ)^(k+1) * ‖s‖^2 := by
            have hpow : (2:ℝ)^(k+1) = (2:ℝ)^k * 2 := pow_succ 2 k
            have h3 : (k:ℝ) ≤ (2:ℝ)^(k+1) := by
              have h2 : k + 1 < 2 ^ (k+1) := Nat.lt_two_pow_self
              have h4 : k ≤ 2 ^ (k+1) := by omega
              exact_mod_cast h4
            rw [hpow]
            push_cast
            have key : (0:ℝ) ≤ ((2:ℝ)^k * 2 - (k:ℝ)) * ‖s‖^2 :=
              mul_nonneg (by linarith) (sq_nonneg _)
            nlinarith [key]

/-- Uniform second-order bound for `(1+t)^{-m} - 1 + m t` on `‖t‖ ≤ 1/2`,
with a constant depending only on an upper bound `q` for `m`. -/
theorem inv_pow_sub_linear (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℂ), 1 ≤ m → m ≤ q → ‖t‖ ≤ 1 / 2 →
      ‖(1 + t)⁻¹ ^ m - 1 + (m : ℂ) * t‖ ≤ C * ‖t‖ ^ 2 := by
  refine ⟨6 * (q:ℝ) * (2:ℝ)^q, by positivity, ?_⟩
  intro m t hm1 hmq ht
  have hnorm1t : (1/2:ℝ) ≤ ‖1 + t‖ := by
    have h := norm_sub_le (1 + t) t
    have hsub : (1 + t) - t = (1:ℂ) := by ring
    rw [hsub, norm_one] at h
    linarith
  have hne : (1 + t) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm1t
    norm_num at hnorm1t
  set w : ℂ := (1 + t)⁻¹ with hwdef
  have hwinv : w * (1 + t) = 1 := by
    rw [hwdef]
    exact inv_mul_cancel₀ hne
  have hw_le : ‖w‖ ≤ 2 := by
    rw [hwdef, norm_inv]
    have h := one_div_le_one_div_of_le (show (0:ℝ) < 1/2 by norm_num) hnorm1t
    simpa using h
  set s : ℂ := w - 1 with hsdef
  have hs1 : 1 + s = w := by rw [hsdef]; ring
  have hs_eq : s = -(t * w) := by
    rw [hsdef]
    linear_combination hwinv
  have hst : s + t = t^2 * w := by
    rw [hsdef]
    linear_combination (1 - t) * hwinv
  have hid : w^m - 1 + (m:ℂ)*t = ((1+s)^m - 1 - (m:ℂ)*s) + (m:ℂ)*(t^2 * w) := by
    have hsw : (1+s)^m = w^m := by rw [hs1]
    rw [hsw, ← hst]
    ring
  have hs_norm : ‖s‖ ≤ 1 := by
    rw [hs_eq, norm_neg, norm_mul]
    calc ‖t‖ * ‖w‖ ≤ (1/2) * 2 := mul_le_mul ht hw_le (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hE := norm_pow_sub_one_sub_mul_le s hs_norm m
  have hs2 : ‖s‖^2 ≤ 4 * ‖t‖^2 := by
    have h2 : ‖s‖ ≤ 2 * ‖t‖ := by
      rw [hs_eq, norm_neg, norm_mul]
      calc ‖t‖ * ‖w‖ ≤ ‖t‖ * 2 := mul_le_mul_of_nonneg_left hw_le (norm_nonneg _)
        _ = 2 * ‖t‖ := by ring
    nlinarith [mul_self_le_mul_self (norm_nonneg s) h2, norm_nonneg t, norm_nonneg s]
  have hW : ‖(m:ℂ)*(t^2*w)‖ = (m:ℝ) * (‖t‖^2 * ‖w‖) := by
    simp only [norm_mul, norm_natCast, norm_pow]
  calc ‖w^m - 1 + (m:ℂ)*t‖
      = ‖((1+s)^m - 1 - (m:ℂ)*s) + (m:ℂ)*(t^2*w)‖ := by rw [hid]
    _ ≤ ‖(1+s)^m - 1 - (m:ℂ)*s‖ + ‖(m:ℂ)*(t^2*w)‖ := norm_add_le _ _
    _ ≤ (m:ℝ)*(2:ℝ)^m*‖s‖^2 + (m:ℝ)*(‖t‖^2*‖w‖) := by
          exact add_le_add hE (le_of_eq hW)
    _ ≤ (m:ℝ)*(2:ℝ)^m*(4*‖t‖^2) + (m:ℝ)*(‖t‖^2*2) := by
          have h1 : (m:ℝ)*(2:ℝ)^m*‖s‖^2 ≤ (m:ℝ)*(2:ℝ)^m*(4*‖t‖^2) := by
            apply mul_le_mul_of_nonneg_left hs2
            positivity
          have h2 : (m:ℝ)*(‖t‖^2*‖w‖) ≤ (m:ℝ)*(‖t‖^2*2) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hw_le (sq_nonneg _)
            · positivity
          exact add_le_add h1 h2
    _ ≤ 6*(q:ℝ)*(2:ℝ)^q * ‖t‖^2 := by
          have hmq' : (m:ℝ) ≤ (q:ℝ) := by exact_mod_cast hmq
          have hPq : (2:ℝ)^m ≤ (2:ℝ)^q := pow_le_pow_right₀ (by norm_num) hmq
          have hR2 : (1:ℝ) ≤ (2:ℝ)^q := one_le_pow₀ (by norm_num)
          have hN : (0:ℝ) ≤ ‖t‖^2 := sq_nonneg _
          have hMP : (m:ℝ)*(2:ℝ)^m ≤ (q:ℝ)*(2:ℝ)^q :=
            mul_le_mul hmq' hPq (by positivity) (by positivity)
          have hq2' : (q:ℝ) ≤ (q:ℝ)*(2:ℝ)^q := by
            have := mul_le_mul_of_nonneg_left hR2 (show (0:ℝ) ≤ (q:ℝ) by positivity)
            simpa using this
          have hq2 : (m:ℝ) ≤ (q:ℝ)*(2:ℝ)^q := le_trans hmq' hq2'
          nlinarith [hMP, hq2, hN]

end Work.Horn.FatouQ
