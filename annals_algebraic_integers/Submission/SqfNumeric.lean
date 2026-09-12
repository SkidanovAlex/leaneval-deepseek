import Mathlib

/-! General numeric facts for the squarefree tail: ceiling/sqrt manipulations
and rpow/log inequalities (all pure ℝ/ℕ). -/

noncomputable section
open scoped Real

namespace Submission.SqfNumeric

/-- `⌈√n⌉₊ ≤ n` (naturals), for `1 ≤ n`. -/
lemma ceil_sqrt_le_self_nat {n : ℕ} (hn : 1 ≤ n) : Nat.ceil (Real.sqrt (n : ℝ)) ≤ n := by
  rw [Nat.ceil_le]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : 0 ≤ ((n : ℝ) - 1) ^ 2 := sq_nonneg _
    nlinarith

/-- `√n ≤ n` (reals), for `1 ≤ n`. -/
lemma sqrt_le_self_real {n : ℕ} (hn : 1 ≤ n) : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : 0 ≤ ((n : ℝ) - 1) ^ 2 := sq_nonneg _
    nlinarith

/-- `0 < ⌈√n⌉₊`, for `1 ≤ n`. -/
lemma ceil_sqrt_pos {n : ℕ} (hn : 1 ≤ n) : 0 < Nat.ceil (Real.sqrt (n : ℝ)) := by
  have h : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity : 0 < (n : ℝ))
  exact Nat.ceil_pos.mpr h

/-- `1 ≤ √n`, for `1 ≤ n`. -/
lemma sqrt_ge_one {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hsq : (1 : ℝ) ^ 2 ≤ (n : ℝ) := by
    nlinarith [show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn]
  exact (Real.le_sqrt (by norm_num) (by positivity : 0 ≤ (n : ℝ))).2 hsq

/-- real difference of naturals. -/
lemma nat_sub_real {n m : ℕ} (hm : m ≤ n) : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
  rw [Nat.cast_sub hm]

/-- `√n ≤ n − m` whenever `m ≤ n − ⌈√n⌉` (naturals). -/
lemma sqrt_le_sub_of_mem {n m : ℕ} (hn : 1 ≤ n) (hms : m ≤ n - Nat.ceil (Real.sqrt (n : ℝ))) :
    Real.sqrt (n : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
  let s : ℕ := Nat.ceil (Real.sqrt (n : ℝ))
  have hs_le_n : s ≤ n := ceil_sqrt_le_self_nat hn
  have hm' : (m : ℝ) ≤ (n : ℝ) - (s : ℝ) := by
    calc
      (m : ℝ) ≤ ((n - s : ℕ) : ℝ) := by exact_mod_cast hms
      _ = (n : ℝ) - (s : ℝ) := by rw [Nat.cast_sub hs_le_n]
  have hs_ge : Real.sqrt (n : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  linarith

/-- `⌈√n⌉ − 1 ≤ √n` (reals). -/
lemma ceil_sqrt_sub_one_le_sqrt {n : ℕ} :
    ((Nat.ceil (Real.sqrt (n : ℝ)) : ℝ) - 1) ≤ Real.sqrt (n : ℝ) := by
  have hlt : (Nat.ceil (Real.sqrt (n : ℝ)) : ℝ) < Real.sqrt (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  linarith

/-- `d ≤ √n` (real) when `d ≤ ⌈√n⌉ − 1` (natural). -/
lemma nat_le_sqrt_of_le_ceil_sub_one {d n : ℕ}
    (hd : d ≤ Nat.ceil (Real.sqrt (n : ℝ)) - 1) :
    (d : ℝ) ≤ Real.sqrt (n : ℝ) := by
  by_cases hs0 : Nat.ceil (Real.sqrt (n : ℝ)) = 0
  · have hd0 : d ≤ 0 := by simpa [hs0] using hd
    have hd0' : d = 0 := by omega
    subst d
    simpa using (Real.sqrt_nonneg (n : ℝ))
  · have hs_pos : 0 < Nat.ceil (Real.sqrt (n : ℝ)) := Nat.pos_of_ne_zero hs0
    have hcast : ((Nat.ceil (Real.sqrt (n : ℝ)) - 1 : ℕ) : ℝ) =
        (Nat.ceil (Real.sqrt (n : ℝ)) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil (Real.sqrt (n : ℝ)))]
      norm_num
    have hd' : (d : ℝ) ≤ ((Nat.ceil (Real.sqrt (n : ℝ)) - 1 : ℕ) : ℝ) := by
      exact_mod_cast hd
    exact le_trans (by simpa [hcast] using hd') (ceil_sqrt_sub_one_le_sqrt (n := n))

/-- exponent absorption: `C·(n/m) ≤ C·√n` when `0 ≤ C`, `√n ≤ m`, `0 < m`, `0 ≤ n`. -/
lemma div_le_sqrt_mul {C n m : ℝ} (hC : 0 ≤ C) (hm : 0 < m)
    (h : Real.sqrt n ≤ m) (hn0 : 0 ≤ n) :
    C * (n / m) ≤ C * Real.sqrt n := by
  have hdiv : n / m ≤ Real.sqrt n := by
    rw [div_le_iff₀ hm]
    calc
      n = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0).symm
      _ ≤ Real.sqrt n * m := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg n)
  exact mul_le_mul_of_nonneg_left hdiv hC

end Submission.SqfNumeric
