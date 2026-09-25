import Mathlib
import Submission.Work.RHContract.A.regionII.caK3B_defs

namespace Work.RHContract.A.regionII

/-- `x^(1/k) < c` when `x < c^k`, `0 ≤ c`, `0 ≤ x`, `0 < k`. -/
lemma rpow_div_lt_of_lt_pow {x c : ℝ} (k : ℕ) (hc : 0 ≤ c) (hx : 0 ≤ x) (hk : 0 < k)
    (h : x < c ^ k) : x ^ (1 / (k : ℝ)) < c := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : x ^ (1 / (k : ℝ)) < (c ^ k : ℝ) ^ (1 / (k : ℝ)) :=
    Real.rpow_lt_rpow hx h (by positivity)
  have h2 : ((c ^ k : ℝ)) ^ (1 / (k : ℝ)) = c := by
    rw [← Real.rpow_natCast c k, ← Real.rpow_mul hc]
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
    have hmul : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  linarith

theorem caK3B_rpow_window {m p : ℕ} (hp : 1 < p) (hpm : p ≤ m) :
    (m : ℝ) ^ (1 / ((Nat.log p m + 1 : ℕ) : ℝ)) < (p : ℝ) ∧
    (p : ℝ) ≤ (m : ℝ) ^ (1 / ((Nat.log p m : ℕ) : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  have hk1 : 1 ≤ Nat.log p m := Nat.le_log_of_pow_le hp (by simpa using hpm)
  have hkpos : 0 < Nat.log p m := by omega
  have hpow : (p : ℝ) ^ Nat.log p m ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p hm0
  have hlt : (m : ℝ) < (p : ℝ) ^ (Nat.log p m + 1) := by
    have h := Nat.lt_pow_succ_log_self hp m
    exact_mod_cast h
  constructor
  · exact rpow_div_lt_of_lt_pow (Nat.log p m + 1) (by positivity) (by positivity)
      (by omega) hlt
  · exact le_rpow_div_of_pow_le (Nat.log p m) (by positivity) (by positivity) hkpos hpow

end Work.RHContract.A.regionII
