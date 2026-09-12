import Mathlib

set_option autoImplicit false

namespace Submission

/-- `m_t := 2^(t+11) + 2^t − 1` (matches `Sec3.m_t`). -/
def mt (t : ℕ) : ℕ := 2 ^ (t + 11) + 2 ^ t - 1

/-- The `m_t` sequence for odd indices grows by `+3` over four steps:
`m_{t+2} = 4·m_t + 3`. -/
lemma mt_add_two (t : ℕ) : mt (t + 2) = 4 * mt t + 3 := by
  unfold mt
  rw [show (t + 2) + 11 = t + 13 by omega]
  have hA : 2 ^ (t + 13) = 4 * 2 ^ (t + 11) := by
    rw [show t + 13 = (t + 11) + 2 by omega, pow_add]
    norm_num
    ring
  have hB : 2 ^ (t + 2) = 4 * 2 ^ t := by
    rw [pow_add]
    norm_num
    ring
  rw [hA, hB]
  have hx : 1 ≤ 2 ^ (t + 11) := Nat.one_le_pow (t + 11) 2 (by norm_num)
  have hy : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by norm_num)
  omega

/-- `m_t` is positive. -/
lemma mt_pos (t : ℕ) : 0 < mt t := by
  unfold mt
  have hx : 1 ≤ 2 ^ (t + 11) := Nat.one_le_pow (t + 11) 2 (by norm_num)
  have hy : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by norm_num)
  omega

/-- `m_t` dominates `2^t`. -/
lemma mt_ge_two_pow (t : ℕ) : 2 ^ t ≤ mt t := by
  unfold mt
  have hx : 1 ≤ 2 ^ (t + 11) := Nat.one_le_pow (t + 11) 2 (by norm_num)
  omega

/-- `m_t` grows no faster than `2^(t+12)`. -/
lemma mt_lt_two_pow (t : ℕ) : mt t < 2 ^ (t + 12) := by
  unfold mt
  have hpow : 2 ^ t ≤ 2 ^ (t + 11) := by
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by omega)
  have hx : 1 ≤ 2 ^ (t + 11) := Nat.one_le_pow (t + 11) 2 (by norm_num)
  have hsum : 2 ^ (t + 11) + 2 ^ t ≤ 2 ^ (t + 11) + 2 ^ (t + 11) := by omega
  have htwo : 2 ^ (t + 11) + 2 ^ (t + 11) = 2 ^ (t + 12) := by
    rw [show t + 12 = (t + 11) + 1 by omega, pow_succ]
    ring
  have hle : 2 ^ (t + 11) + 2 ^ t ≤ 2 ^ (t + 12) := by
    exact le_trans hsum (by rw [htwo])
  have hbig : 1 ≤ 2 ^ (t + 12) := Nat.one_le_pow (t + 12) 2 (by norm_num)
  omega

/-- Covering: every `q ≥ 2^43·m_1` sits in a tile for a unique odd `t`. -/
lemma exists_odd_t_tile (q : ℕ) (hq : 2 ^ 43 * mt 1 ≤ q) :
    ∃ t : ℕ, Odd t ∧ 2 ^ 43 * mt t ≤ q ∧ q < 2 ^ 43 * mt (t + 2) := by
  classical
  let P : ℕ → Prop := fun n => q < 2 ^ 43 * mt (2 * n + 1)
  have hex : ∃ n, P n := by
    refine ⟨q + 1, ?_⟩
    dsimp [P]
    have hmt : 2 ^ (2 * (q + 1) + 1) ≤ mt (2 * (q + 1) + 1) :=
      mt_ge_two_pow (2 * (q + 1) + 1)
    have hlt : 2 * (q + 1) + 1 < 2 ^ (2 * (q + 1) + 1) :=
      Nat.lt_two_pow_self
    have hqlt : q < mt (2 * (q + 1) + 1) := by
      calc
        q < 2 * (q + 1) + 1 := by omega
        _ < 2 ^ (2 * (q + 1) + 1) := hlt
        _ ≤ mt (2 * (q + 1) + 1) := hmt
    have hmul : mt (2 * (q + 1) + 1) ≤ 2 ^ 43 * mt (2 * (q + 1) + 1) := by
      exact Nat.le_mul_of_pos_left _ (by positivity)
    exact lt_of_lt_of_le hqlt hmul
  let n := Nat.find hex
  have hPn : P n := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra hnon
    have hnz : n = 0 := by omega
    have hc : q < 2 ^ 43 * mt 1 := by
      simpa [P, hnz] using hPn
    omega
  let t := 2 * (n - 1) + 1
  have ht2 : t + 2 = 2 * n + 1 := by
    dsimp [t]
    omega
  refine ⟨t, ?_, ?_, ?_⟩
  · exact ⟨n - 1, rfl⟩
  · have hmin : ¬ P (n - 1) := Nat.find_min hex (by omega)
    dsimp [t]
    have hmin' : ¬ q < 2 ^ 43 * mt (2 * (n - 1) + 1) := by
      simpa [P] using hmin
    omega
  · have hP : q < 2 ^ 43 * mt (2 * n + 1) := by
      simpa [P] using hPn
    rw [ht2]
    exact hP

/-- Consequence: the tile gives `m_t ≤ q/2^43` and a frequency bound
`q ≤ 2^(t+60)` (crude; slack is enormous). -/
lemma tile_consequences {q t : ℕ} (_ht : Odd t)
    (hlo : 2 ^ 43 * mt t ≤ q) (hhi : q < 2 ^ 43 * mt (t + 2)) :
    (2 ^ 43 * mt t ≤ q) ∧ q ≤ 2 ^ (t + 60) := by
  constructor
  · exact hlo
  · have hmt : mt (t + 2) < 2 ^ (t + 14) := by
      have h := mt_lt_two_pow (t + 2)
      rw [show (t + 2) + 12 = t + 14 by omega] at h
      exact h
    have hq1 : q < 2 ^ (t + 57) := by
      calc
        q < 2 ^ 43 * mt (t + 2) := hhi
        _ < 2 ^ 43 * 2 ^ (t + 14) := by
          exact Nat.mul_lt_mul_of_pos_left hmt (by positivity : 0 < 2 ^ 43)
        _ = 2 ^ (t + 57) := by
          rw [← pow_add, show 43 + (t + 14) = t + 57 by omega]
    have hq2 : q ≤ 2 ^ (t + 57) := le_of_lt hq1
    have hpow : 2 ^ (t + 57) ≤ 2 ^ (t + 60) :=
      pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by omega)
    exact le_trans hq2 hpow

/-- For the final assembly: with `q = ⌈m/4⌉`, `q` is large whenever `m` is;
and `4q − 3 ≤ m ≤ 4q`. -/
lemma ceil_div_four (m : ℕ) : 4 * ((m + 3) / 4) - 3 ≤ m ∧ m ≤ 4 * ((m + 3) / 4) := by
  let q := (m + 3) / 4
  have hdiv : (m + 3) = 4 * q + (m + 3) % 4 := by
    dsimp [q]
    exact (Nat.div_add_mod (m + 3) 4).symm
  have hrlt : (m + 3) % 4 < 4 := Nat.mod_lt (m + 3) (by norm_num)
  constructor
  · have h4 : 4 * q ≤ (m + 3) := by omega
    omega
  · have h4 : (m + 3) ≤ 4 * q + 3 := by omega
    omega

end Submission
