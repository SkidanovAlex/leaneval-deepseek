import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **Logarithmic size of `⌊(2P)^m⌋`: it is `O(P^m log P)`.** -/
lemma n4_log_term_bound (m : ℕ) : ∃ C P₀ : ℝ, 0 < C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
    (((⌊(2*P)^m⌋₊ : ℕ) : ℝ)) * Real.log (2 + ((⌊(2*P)^m⌋₊ : ℕ) : ℝ))
      ≤ C * P ^ m * Real.log P := by
  -- For `P ≥ 3` the floor is at most `(2P)^m` and the logarithm is at most
  -- `2(m+1) log P`, so the product is at most `2^(m+1) (m+1) P^m log P`.
  refine ⟨(2:ℝ)^(m+1) * ((m:ℝ)+1), 3, by positivity, by norm_num, ?_⟩
  intro P hP
  have hP0 : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) (by linarith)
  set X : ℝ := (2*P)^m with hXdef
  set N : ℕ := ⌊X⌋₊ with hNdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hNX : (N:ℝ) ≤ X := by rw [hNdef]; exact Nat.floor_le hX0
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hX1 : 1 ≤ X := by rw [hXdef]; exact one_le_pow₀ (by linarith : (1:ℝ) ≤ 2*P)
  -- the logarithm's argument is dominated by `(2P)^(m+1) = X * (2P)`
  have h2X : 2 + X ≤ X * (2*P) := by nlinarith
  have hpow : X * (2*P) = (2*P)^(m+1) := by rw [hXdef, pow_succ]
  have hle : 2 + (N:ℝ) ≤ (2*P)^(m+1) := by rw [← hpow]; linarith
  have harg : 0 < 2 + (N:ℝ) := lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_right hN0)
  have harg1 : 1 ≤ 2 + (N:ℝ) := by linarith
  have hlog_le : Real.log (2 + (N:ℝ)) ≤ 2 * ((m:ℝ)+1) * Real.log P := by
    have h1 : Real.log (2 + (N:ℝ)) ≤ ((m+1 : ℕ) : ℝ) * Real.log (2*P) := by
      calc Real.log (2 + (N:ℝ)) ≤ Real.log ((2*P)^(m+1)) := Real.log_le_log harg hle
        _ = ((m+1 : ℕ) : ℝ) * Real.log (2*P) := Real.log_pow _ _
    rw [Real.log_mul (by norm_num) (ne_of_gt hP0)] at h1
    have hm : ((m+1 : ℕ) : ℝ) = (m:ℝ)+1 := by push_cast; ring
    rw [hm] at h1
    calc Real.log (2 + (N:ℝ)) ≤ ((m:ℝ)+1) * (Real.log 2 + Real.log P) := h1
      _ ≤ ((m:ℝ)+1) * (2 * Real.log P) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 2 * ((m:ℝ)+1) * Real.log P := by ring
  have hmain : (N:ℝ) * Real.log (2 + (N:ℝ)) ≤ X * (2 * ((m:ℝ)+1) * Real.log P) :=
    mul_le_mul hNX hlog_le (Real.log_nonneg harg1) hX0
  have hfin : X * (2 * ((m:ℝ)+1) * Real.log P)
      = ((2:ℝ)^(m+1) * ((m:ℝ)+1)) * P^m * Real.log P := by
    rw [hXdef, mul_pow]
    rw [pow_succ]
    ring
  rw [hNdef, hXdef] at hmain
  linarith [hmain, hfin]

end Work.BMF
