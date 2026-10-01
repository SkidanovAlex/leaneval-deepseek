import Mathlib

namespace Work.LinnikAreas.JMAux

/-- The geometric series of ratio `a` (with `0 ≤ a < 1`) is bounded by `(1 - a)⁻¹`. -/
lemma geom_sum_range_le_inv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, a ^ j ≤ (1 - a)⁻¹ := by
  have h1a : 0 < 1 - a := by linarith
  have hgeom : (∑ j ∈ Finset.range n, a ^ j) * (1 - a) = 1 - a ^ n := by
    have h := geom_sum_mul a n
    nlinarith [h]
  have hle : (∑ j ∈ Finset.range n, a ^ j) * (1 - a) ≤ 1 := by
    rw [hgeom]
    have : (0:ℝ) ≤ a^n := pow_nonneg ha0 n
    linarith
  rw [← one_div]
  rw [le_div_iff₀ h1a]
  linarith

lemma GeomIndicatorSum (R : ℕ) (hR : 1 ≤ R) (N : ℕ) :
    (∑ k ∈ Finset.range N, (if (R:ℝ) ≤ (2:ℝ)^k then ((2:ℝ) ^ (-(3/2:ℝ)))^k else 0))
      ≤ 2 * (R:ℝ) ^ (-(3/2:ℝ)) := by
  set a : ℝ := (2:ℝ)^(-(3/2:ℝ)) with ha_def
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  have hex : ∃ k, (R:ℝ) ≤ (2:ℝ)^k := by
    refine ⟨R, ?_⟩
    have h : R < 2 ^ R := Nat.lt_two_pow_self
    have h' : (R:ℝ) < (2:ℝ)^R := by exact_mod_cast h
    linarith
  obtain ⟨m, hmk, hmmin⟩ : ∃ m, (R:ℝ) ≤ (2:ℝ)^m ∧ ∀ k, (R:ℝ) ≤ (2:ℝ)^k → m ≤ k :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min' hex hk⟩
  have hiff : ∀ k, ((R:ℝ) ≤ (2:ℝ)^k) ↔ m ≤ k := by
    intro k
    exact ⟨hmmin k, fun hk => by
      have h2 : (2:ℝ)^m ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk
      linarith⟩
  have hS : (∑ k ∈ Finset.range N, (if (R:ℝ) ≤ (2:ℝ)^k then a^k else 0))
          = ∑ k ∈ Finset.range N, (if m ≤ k then a^k else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : (R:ℝ) ≤ (2:ℝ)^k
    · rw [if_pos h, if_pos ((hiff k).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((hiff k).mpr hc))]
  have hshift : (∑ k ∈ Finset.range N, (if m ≤ k then a^k else 0))
      = a^m * ∑ k ∈ Finset.range N, (if m ≤ k then a^(k-m) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : m ≤ k
    · rw [if_pos h, if_pos h, ← pow_add, Nat.add_sub_of_le h]
    · rw [if_neg h, if_neg h, mul_zero]
  have hT : (∑ k ∈ Finset.range N, (if m ≤ k then a^(k-m) else 0))
          = ∑ j ∈ Finset.range (N - m), a^j := by
    rw [← Finset.sum_filter (s := Finset.range N) (fun k => m ≤ k) (fun k => a^(k-m))]
    have hfilt : (Finset.range N).filter (fun k => m ≤ k) = Finset.Ico m N := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfilt, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_sub_cancel_left]
  have ha0 : 0 ≤ a := by rw [ha_def]; positivity
  have hahalf : a ≤ 1/2 := by
    rw [ha_def]
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (-(3/2:ℝ)) ≤ (-1:ℝ))
    have h2 : (2:ℝ)^(-1:ℝ) = 1/2 := by rw [Real.rpow_neg_one]; norm_num
    rw [h2] at h; exact h
  have ha1 : a < 1 := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hpow : a^m = ((2:ℝ)^m)^(-(3/2:ℝ)) := by
    rw [ha_def]
    rw [← Real.rpow_natCast ((2:ℝ)^(-(3/2:ℝ))) m]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [← Real.rpow_natCast (2:ℝ) m]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have ham : a^m ≤ (R:ℝ)^(-(3/2:ℝ)) := by
    rw [hpow]
    exact Real.rpow_le_rpow_of_nonpos hRpos hmk (by norm_num)
  have hinv : (1-a)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ h1a]
    linarith
  have hTle : (∑ j ∈ Finset.range (N - m), a^j) ≤ (1 - a)⁻¹ :=
    geom_sum_range_le_inv ha0 ha1 (N - m)
  calc (∑ k ∈ Finset.range N, (if (R:ℝ) ≤ (2:ℝ)^k then a^k else 0))
      = ∑ k ∈ Finset.range N, (if m ≤ k then a^k else 0) := hS
    _ = a^m * ∑ k ∈ Finset.range N, (if m ≤ k then a^(k-m) else 0) := hshift
    _ = a^m * ∑ j ∈ Finset.range (N - m), a^j := by rw [hT]
    _ ≤ a^m * (1 - a)⁻¹ := mul_le_mul_of_nonneg_left hTle (pow_nonneg ha0 m)
    _ ≤ (R:ℝ)^(-(3/2:ℝ)) * (1 - a)⁻¹ :=
        mul_le_mul_of_nonneg_right ham (inv_nonneg.mpr (le_of_lt h1a))
    _ ≤ (R:ℝ)^(-(3/2:ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg (le_of_lt hRpos) _)
    _ = 2 * (R:ℝ)^(-(3/2:ℝ)) := by ring

end Work.LinnikAreas.JMAux
