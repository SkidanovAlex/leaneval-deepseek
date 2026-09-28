import Mathlib

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

/-- Helper: `(2:ℝ)^(n+1)` (a natural power) equals `(2:ℝ)^((n:ℝ)+1)` (a real power). -/
private lemma two_pow_succ_eq_rpow (n : ℕ) :
    (2:ℝ)^(n+1) = (2:ℝ)^((n:ℝ)+1) := by
  have hcast : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
  rw [← hcast, Real.rpow_natCast]

/-- If `k = ⌊logb 2 x⌋₊` and `x ≥ 1`, then `2^k ≤ x < 2^(k+1)`. -/
private lemma dyadic_bracket_of_floor_logb {x : ℝ} (hx : 1 ≤ x) :
    (2:ℝ)^(⌊Real.logb 2 x⌋₊ : ℝ) ≤ x ∧
    x < (2:ℝ)^((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hlog0 : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hlogeq : (2:ℝ) ^ Real.logb 2 x = x := Real.rpow_logb (by norm_num) (by norm_num) hx0
  refine ⟨?_, ?_⟩
  · calc (2:ℝ)^(⌊Real.logb 2 x⌋₊ : ℝ) ≤ (2:ℝ)^(Real.logb 2 x) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlog0)
    _ = x := hlogeq
  · calc x = (2:ℝ)^(Real.logb 2 x) := hlogeq.symm
    _ < (2:ℝ)^((⌊Real.logb 2 x⌋₊ : ℝ) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Nat.lt_floor_add_one _)

/-- `x^(-m) ≤ 2^(-(k:ℝ)*m)` when `k = ⌊logb 2 x⌋₊`, `x ≥ 1` and `m ≥ 0`. -/
private lemma rpow_neg_le_of_dyadic_floor {x : ℝ} (hx : 1 ≤ x) {m : ℝ} (hm : 0 ≤ m) :
    x ^ (-m) ≤ (2:ℝ)^(-((⌊Real.logb 2 x⌋₊ : ℝ))*m) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  obtain ⟨hlow, _⟩ := dyadic_bracket_of_floor_logb hx
  have hpos2 : (0:ℝ) < (2:ℝ)^(⌊Real.logb 2 x⌋₊ : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  calc x ^ (-m) ≤ ((2:ℝ)^(⌊Real.logb 2 x⌋₊ : ℝ)) ^ (-m) :=
        Real.rpow_le_rpow_of_nonpos hpos2 hlow (by linarith)
    _ = (2:ℝ)^(-((⌊Real.logb 2 x⌋₊ : ℝ))*m) := by
        rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (⌊Real.logb 2 x⌋₊ : ℝ) (-m)]
        ring_nf

theorem DyadicRpowLeIndicatorSum (x : ℝ) (hx : 1 ≤ x) (m : ℝ) (hm : 0 ≤ m) (J : ℕ)
    (hJ : ⌊Real.logb 2 x⌋₊ ≤ J) :
    x ^ (-m) ≤ ∑ j ∈ Finset.range (J + 1),
      (2:ℝ)^(-(j:ℝ)*m) * (if x < (2:ℝ)^(j+1) then (1:ℝ) else 0) := by
  classical
  set k : ℕ := ⌊Real.logb 2 x⌋₊ with hkdef
  -- the bracketing inequality for `x`
  have hhigh : x < (2:ℝ)^(k+1) := by
    have h := (dyadic_bracket_of_floor_logb hx).2
    rw [← hkdef] at h
    rw [two_pow_succ_eq_rpow]
    exact h
  -- monotonicity step: `x^(-m) ≤ 2^(-(k:ℝ)*m)`
  have hstep1 : x ^ (-m) ≤ (2:ℝ)^(-(k:ℝ)*m) := by
    have h := rpow_neg_le_of_dyadic_floor hx hm
    rwa [← hkdef] at h
  -- the index `k` belongs to the summation range
  have hmem : k ∈ Finset.range (J + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hJ)
  -- the `k`-th summand equals `2^(-(k:ℝ)*m)`
  have hkterm :
      (2:ℝ)^(-(k:ℝ)*m) * (if x < (2:ℝ)^(k+1) then (1:ℝ) else 0) = (2:ℝ)^(-(k:ℝ)*m) := by
    simp [hhigh]
  -- all summands are nonnegative
  have hnonneg : ∀ j ∈ Finset.range (J + 1),
      0 ≤ (2:ℝ)^(-(j:ℝ)*m) * (if x < (2:ℝ)^(j+1) then (1:ℝ) else 0) := by
    intro j _
    refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
    split
    · norm_num
    · norm_num
  have hsingle := Finset.single_le_sum hnonneg hmem
  rw [hkterm] at hsingle
  exact le_trans hstep1 hsingle

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
