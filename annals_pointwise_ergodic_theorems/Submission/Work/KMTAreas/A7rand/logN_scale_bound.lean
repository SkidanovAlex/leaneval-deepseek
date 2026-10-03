import Mathlib

namespace Work.KMTAreas.A7rand

/-- Auxiliary elementary bound: `2m + 9 ≤ 2^(m+4)`. -/
private lemma two_mul_add_nine_le (m : ℕ) : 2 * m + 9 ≤ 2 ^ (4 + m) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    calc 2 * (m + 1) + 9 ≤ 2 * (2 * m + 9) := by omega
      _ ≤ 2 * 2 ^ (4 + m) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (4 + (m + 1)) := by
            rw [show 4 + (m + 1) = (4 + m) + 1 by omega, pow_succ]; ring

/-- For `n ≥ 4`, `n ^ 2 ≤ 2 ^ n`. -/
private lemma sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  subst hm
  clear hn
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hlin : 2 * m + 9 ≤ 2 ^ (4 + m) := two_mul_add_nine_le m
    have e1 : (4 + (m + 1)) ^ 2 = (4 + m) ^ 2 + (2 * m + 9) := by ring
    rw [e1]
    have e2 : 2 ^ (4 + (m + 1)) = 2 ^ (4 + m) + 2 ^ (4 + m) := by
      rw [show 4 + (m + 1) = (4 + m) + 1 by omega, pow_succ]; ring
    rw [e2]
    exact Nat.add_le_add ih hlin

theorem logN_scale_bound (C₀ R : ℕ) (hC₀ : 1 ≤ C₀)
    (h : (R : ℝ) < (C₀ : ℝ) * (Nat.log 2 (R + 2) : ℝ) + 2 * Real.sqrt ((R : ℝ) + 2)) :
    R ≤ (8 * C₀ + 8) ^ 2 := by
  by_contra hcontra
  simp only [not_le] at hcontra
  -- hcontra : (8 * C₀ + 8) ^ 2 < R
  obtain ⟨L, hL⟩ := (show ∃ L : ℕ, L = Nat.log 2 (R + 2) from ⟨_, rfl⟩)
  obtain ⟨s, hs⟩ := (show ∃ s : ℝ, s = Real.sqrt ((R : ℝ) + 2) from ⟨_, rfl⟩)
  have hR2pos : (0 : ℝ) ≤ (R : ℝ) + 2 := by positivity
  have hsq : s ^ 2 = (R : ℝ) + 2 := by rw [hs]; exact Real.sq_sqrt hR2pos
  have hsnn : 0 ≤ s := by rw [hs]; positivity
  have hh : (R : ℝ) < (C₀ : ℝ) * (L : ℝ) + 2 * s := by
    have h' := h
    rw [← hs, ← hL] at h'
    exact h'
  -- R is large
  have h256 : (256 : ℕ) ≤ (8 * C₀ + 8) ^ 2 := by
    have h16 : 16 ≤ 8 * C₀ + 8 := by omega
    calc (256 : ℕ) = 16 * 16 := by norm_num
      _ ≤ (8 * C₀ + 8) * (8 * C₀ + 8) := Nat.mul_le_mul h16 h16
      _ = (8 * C₀ + 8) ^ 2 := by ring
  have hbig : (256 : ℕ) ≤ R := by omega
  have hRge : (256 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hbig
  -- s is bigger than 16 and than 8(C₀+1)
  have hs16 : (16 : ℝ) < s := by
    rw [hs, Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
    linarith [hRge]
  have hMC : ((8 * C₀ + 8 : ℕ) : ℝ) = 8 * ((C₀ : ℝ) + 1) := by push_cast; ring
  have hsC : 8 * ((C₀ : ℝ) + 1) < s := by
    have hc : ((8 * C₀ + 8 : ℕ) : ℝ) ^ 2 < (R : ℝ) := by
      have hcast : (((8 * C₀ + 8) ^ 2 : ℕ) : ℝ) < (R : ℝ) := by exact_mod_cast hcontra
      simpa using hcast
    rw [hMC] at hc
    rw [hs, Real.lt_sqrt (by positivity : (0 : ℝ) ≤ 8 * ((C₀ : ℝ) + 1))]
    linarith
  -- the logarithmic factor is at least 4 and 2^L ≤ R + 2
  have hL4 : 4 ≤ L := by
    rw [hL, Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega : R + 2 ≠ 0)]
    norm_num
    omega
  have hpow : 2 ^ L ≤ R + 2 := by
    rw [hL]; exact Nat.pow_log_le_self 2 (by omega)
  -- hence L ≤ s
  have hLsq : ((L : ℝ)) ^ 2 ≤ s ^ 2 := by
    have h1 : L ^ 2 ≤ 2 ^ L := sq_le_two_pow L hL4
    have h2 : ((L ^ 2 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ L) := by
      have h2' : ((L ^ 2 : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast h1
      simpa using h2'
    have h3 : ((2 : ℝ) ^ L) ≤ (R : ℝ) + 2 := by
      have h3' : ((2 ^ L : ℕ) : ℝ) ≤ ((R + 2 : ℕ) : ℝ) := by exact_mod_cast hpow
      simpa using h3'
    calc ((L : ℝ)) ^ 2 = ((L ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 : ℝ) ^ L) := h2
      _ ≤ (R : ℝ) + 2 := h3
      _ = s ^ 2 := hsq.symm
  have hLs : (L : ℝ) ≤ s := by
    have h' := sq_le_sq.mp hLsq
    rwa [abs_of_nonneg (show (0 : ℝ) ≤ (L : ℝ) by positivity),
         abs_of_nonneg hsnn] at h'
  -- conclusion: the two sides cannot be ordered this way
  have hC0nn : (0 : ℝ) ≤ (C₀ : ℝ) := by positivity
  have hfinal : (C₀ : ℝ) * (L : ℝ) + 2 * s ≤ (R : ℝ) := by
    have h1 : (C₀ : ℝ) * (L : ℝ) ≤ (C₀ : ℝ) * s := mul_le_mul_of_nonneg_left hLs hC0nn
    have hC0le : (C₀ : ℝ) + 2 ≤ s / 4 := by linarith [hsC, hC0nn]
    have h2 : ((C₀ : ℝ) + 2) * s ≤ (s / 4) * s := mul_le_mul_of_nonneg_right hC0le hsnn
    have h3 : (s / 4) * s ≤ s ^ 2 - 2 := by nlinarith only [hs16]
    have h4 : ((C₀ : ℝ) + 2) * s = (C₀ : ℝ) * s + 2 * s := by ring
    linarith [hsq, h1, h2, h3, h4]
  linarith [hh, hfinal]

end Work.KMTAreas.A7rand
