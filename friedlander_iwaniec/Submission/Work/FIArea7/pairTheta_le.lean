import Mathlib

namespace Work.FIArea7

open Finset

/-- `4*b*e ∣ 4*L` is equivalent to `b*e ∣ L`. -/
lemma dvd_four_mul_iff (b e L : ℕ) : 4 * b * e ∣ 4 * L ↔ b * e ∣ L := by
  rw [show (4:ℕ) * b * e = 4 * (b * e) by ring]
  exact Nat.mul_dvd_mul_iff_left (by norm_num)

/-- The truncated sum `∑_{b=1}^{n} 1/b²` is at most `2`. -/
lemma sum_Icc_one_div_sq_le_two (n : ℕ) :
    ∑ b ∈ Finset.Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 := by
  have h : Finset.Ioo 0 (n+1) = Finset.Icc 1 n := by
    ext i; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
  rw [← h]
  have h2 : ∀ b, (1:ℝ)/(b:ℝ)^2 = ((b:ℝ)^2)⁻¹ := fun b => one_div _
  simp_rw [h2]
  have h4 := sum_Ioo_inv_sq_le (α := ℝ) 0 (n+1)
  have h3 : (2:ℝ) / ((0:ℝ) + 1) = 2 := by norm_num
  linarith

/-- Core bound: the weighted double sum over pairs `(b,e)` with `b*e ∣ L`
is at most `2*L`. -/
lemma double_sum_bound (L B0 X : ℕ) (hL : 0 < L) :
    (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (if b * e ∣ L then (1 : ℝ) else 0)) ≤ 2 * (L:ℝ) := by
  have hterm : ∀ b ∈ Finset.Icc 1 B0,
      (∑ e ∈ Finset.Icc 1 X, (1/(b:ℝ)) * (if b*e ∣ L then (1:ℝ) else 0))
        ≤ (1/(b:ℝ)) * (if b ∣ L then ((L/b : ℕ):ℝ) else 0) := by
    intro b hb
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    by_cases hbL : b ∣ L
    · rw [if_pos hbL]
      rw [Finset.sum_boole]
      apply Nat.cast_le.mpr
      have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbL hL
      have hle : b ≤ L := Nat.le_of_dvd hL hbL
      have hdpos : 0 < L / b := Nat.div_pos hle hbpos
      have hsub : (Finset.Icc 1 X).filter (fun e => b * e ∣ L) ⊆ (L/b).divisors := by
        intro e he
        simp only [Finset.mem_filter, Finset.mem_Icc] at he
        obtain ⟨⟨he1, _⟩, hee⟩ := he
        rw [Nat.mem_divisors]
        refine ⟨?_, Nat.pos_iff_ne_zero.mp hdpos⟩
        have h2 : b * e ∣ b * (L/b) := by rw [Nat.mul_div_cancel' hbL]; exact hee
        exact (Nat.mul_dvd_mul_iff_left hbpos).mp h2
      calc ((Finset.Icc 1 X).filter (fun e => b * e ∣ L)).card
          ≤ (L/b).divisors.card := Finset.card_le_card hsub
        _ ≤ L/b := Nat.card_divisors_le_self _
    · rw [if_neg hbL]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro e he
      have hne : ¬ (b * e ∣ L) := fun hh => hbL (dvd_trans ⟨e, by ring⟩ hh)
      simp [hne]
  have hA := Finset.sum_le_sum hterm
  have heq : ∑ b ∈ Finset.Icc 1 B0, (1/(b:ℝ)) * (if b ∣ L then ((L/b : ℕ):ℝ) else 0)
      = ∑ b ∈ Finset.Icc 1 B0, (if b ∣ L then (L:ℝ)/(b:ℝ)^2 else 0) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hb0 : (b:ℝ) ≠ 0 := by
      have : b ≠ 0 := by omega
      exact_mod_cast this
    by_cases hbL : b ∣ L
    · rw [if_pos hbL, if_pos hbL, Nat.cast_div hbL hb0]
      field_simp
    · rw [if_neg hbL, if_neg hbL, mul_zero]
  have hsub : (Finset.Icc 1 B0).filter (fun b => b ∣ L) ⊆ Finset.Icc 1 L := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb1, _⟩, hbdvd⟩ := hb
    simp only [Finset.mem_Icc]
    exact ⟨hb1, Nat.le_of_dvd hL hbdvd⟩
  have hB : ∑ b ∈ Finset.Icc 1 B0, (if b ∣ L then (L:ℝ)/(b:ℝ)^2 else 0) ≤ 2 * (L:ℝ) := by
    rw [← Finset.sum_filter]
    calc ∑ b ∈ (Finset.Icc 1 B0).filter (fun b => b ∣ L), (L:ℝ)/(b:ℝ)^2
        ≤ ∑ b ∈ Finset.Icc 1 L, (L:ℝ)/(b:ℝ)^2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => div_nonneg (by positivity) (sq_nonneg _))
      _ = (L:ℝ) * ∑ b ∈ Finset.Icc 1 L, (1:ℝ)/(b:ℝ)^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
      _ ≤ (L:ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_Icc_one_div_sq_le_two L) (by positivity)
      _ = 2 * (L:ℝ) := by ring
  calc (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
          (1 / (b : ℝ)) * (if b * e ∣ L then (1 : ℝ) else 0))
      ≤ ∑ b ∈ Finset.Icc 1 B0, (1/(b:ℝ)) * (if b ∣ L then ((L/b : ℕ):ℝ) else 0) := hA
    _ = ∑ b ∈ Finset.Icc 1 B0, (if b ∣ L then (L:ℝ)/(b:ℝ)^2 else 0) := heq
    _ ≤ 2 * (L:ℝ) := hB

theorem pairTheta_le (B0 X D : ℕ) :
    ((D : ℝ))⁻¹ * (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (if 4 * b * e ∣ D then (1 : ℝ) else 0)) ≤ 2 := by
  by_cases hD : D = 0
  · subst hD; simp
  · by_cases h4 : 4 ∣ D
    · obtain ⟨L, rfl⟩ := h4
      simp_rw [dvd_four_mul_iff]
      have hL : 0 < L := by omega
      have hS := double_sum_bound L B0 X hL
      have hnn : (0:ℝ) ≤ ((4 * L : ℕ) : ℝ)⁻¹ := by positivity
      calc ((4 * L : ℕ) : ℝ)⁻¹ *
              (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
                (1 / (b : ℝ)) * (if b * e ∣ L then (1 : ℝ) else 0))
          ≤ ((4 * L : ℕ) : ℝ)⁻¹ * (2 * (L:ℝ)) := mul_le_mul_of_nonneg_left hS hnn
        _ = 1/2 := by
            have hLb : (L:ℝ) ≠ 0 := by
              have : L ≠ 0 := by omega
              exact_mod_cast this
            rw [Nat.cast_mul]
            field_simp
            norm_num
        _ ≤ 2 := by norm_num
    · have hzero : ∀ b e, ¬ (4*b*e ∣ D) := fun b e hd => h4 (dvd_trans ⟨b*e, by ring⟩ hd)
      have hsum : (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
              (1 / (b : ℝ)) * (if 4 * b * e ∣ D then (1 : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        apply Finset.sum_eq_zero
        intro e he
        simp [hzero b e]
      rw [hsum, mul_zero]
      norm_num

end Work.FIArea7
