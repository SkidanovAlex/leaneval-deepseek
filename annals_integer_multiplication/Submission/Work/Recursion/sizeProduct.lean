import Mathlib
import Submission.Work.Recursion.defs

namespace Work.Recursion

/-- For `m ≥ 1`, the bit-size of `m` is at most `log₂ m + 1`.  This is the real-valued form of
`2 ^ (m.size - 1) ≤ m` together with monotonicity of `Real.logb`. -/
private lemma size_le_logb_add_one (m : ℕ) (hm : 1 ≤ m) :
    (m.size : ℝ) ≤ Real.logb 2 (m : ℝ) + 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hs1 : 1 ≤ m.size := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.size_eq_zero]; omega
  have hpow : 2 ^ (m.size - 1) ≤ m := by
    rw [← Nat.lt_size]; omega
  have hpowR : (2 : ℝ) ^ (m.size - 1) ≤ (m : ℝ) := by exact_mod_cast hpow
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hm0).mpr hpowR
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  simp only [mul_one] at hlog
  have hcast : ((m.size - 1 : ℕ) : ℝ) = (m.size : ℝ) - 1 := by
    rw [Nat.cast_sub hs1, Nat.cast_one]
  rw [hcast] at hlog
  linarith

/-- Paper §5.1: bit-size of `3 r p` where `r = rpar n`, `p = ppar n = 6b`. -/
theorem sizeProduct (n : ℕ) (hn : 2 ≤ n) :
    ((3 * HvdH.rpar n * HvdH.ppar n).size : ℝ) ≤
      (HvdH.kTpar n : ℝ) / (HvdH.D : ℝ) + Real.logb 2 (18 * (HvdH.bpar n : ℝ)) + 3 := by
  -- `3 r p = 18 b · 2^e` with `e = ⌈k_T / d⌉`
  have hppar : HvdH.ppar n = 6 * HvdH.bpar n := rfl
  have hne : 18 * HvdH.bpar n ≠ 0 := by
    have : 1 ≤ HvdH.bpar n := by
      rw [HvdH.bpar]; exact Nat.clog_pos (by norm_num) (by omega)
    omega
  have hmul : 3 * HvdH.rpar n * HvdH.ppar n
      = 18 * HvdH.bpar n * 2 ^ ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) := by
    rw [hppar, HvdH.rpar]
    ring
  -- the `Nat.size` of a nonzero number times a power of two splits
  have hsize : (3 * HvdH.rpar n * HvdH.ppar n).size
      = (18 * HvdH.bpar n).size + ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) := by
    rw [hmul, ← Nat.shiftLeft_eq_mul_pow]
    exact Nat.size_shiftLeft hne _
  -- `size (18b) ≤ log₂ (18b) + 1`
  have hsb : ((18 * HvdH.bpar n).size : ℝ)
      ≤ Real.logb 2 (18 * (HvdH.bpar n : ℝ)) + 1 := by
    have h := size_le_logb_add_one (18 * HvdH.bpar n) (by omega)
    rwa [Nat.cast_mul] at h
  -- `⌈k_T/d⌉ ≤ k_T/d + 1`
  have hDpos : (0 : ℝ) < (HvdH.D : ℝ) := by norm_num [HvdH.D]
  have he : (((HvdH.kTpar n + HvdH.D - 1) / HvdH.D : ℕ) : ℝ)
      ≤ (HvdH.kTpar n : ℝ) / (HvdH.D : ℝ) + 1 := by
    have hcast_div : (((HvdH.kTpar n + HvdH.D - 1) / HvdH.D : ℕ) : ℝ)
        ≤ ((HvdH.kTpar n + HvdH.D - 1 : ℕ) : ℝ) / (HvdH.D : ℝ) := Nat.cast_div_le
    have hle : ((HvdH.kTpar n + HvdH.D - 1 : ℕ) : ℝ)
        ≤ (HvdH.kTpar n : ℝ) + (HvdH.D : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr (Nat.sub_le (HvdH.kTpar n + HvdH.D) 1)
      simpa [Nat.cast_add] using this
    have h2 : ((HvdH.kTpar n + HvdH.D - 1 : ℕ) : ℝ) / (HvdH.D : ℝ)
        ≤ (HvdH.kTpar n : ℝ) / (HvdH.D : ℝ) + 1 := by
      calc ((HvdH.kTpar n + HvdH.D - 1 : ℕ) : ℝ) / (HvdH.D : ℝ)
          ≤ ((HvdH.kTpar n : ℝ) + (HvdH.D : ℝ)) / (HvdH.D : ℝ) :=
            div_le_div_of_nonneg_right hle (le_of_lt hDpos)
        _ = (HvdH.kTpar n : ℝ) / (HvdH.D : ℝ) + 1 := by
            rw [add_div, div_self (ne_of_gt hDpos)]
    linarith
  have hsize' : ((3 * HvdH.rpar n * HvdH.ppar n).size : ℝ)
      = ((18 * HvdH.bpar n).size : ℝ)
        + (((HvdH.kTpar n + HvdH.D - 1) / HvdH.D : ℕ) : ℝ) := by
    rw [hsize]; push_cast; ring
  rw [hsize']
  linarith

end Work.Recursion
