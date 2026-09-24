import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

open Finset

/-- Telescoping identity: `∑_{k ∈ Ico m n} (f k - f (k+1)) = f m - f n` for `m ≤ n`. -/
lemma sum_Ico_sub_succ_eq (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.Ico m n, (f k - f (k + 1)) = f m - f n := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := Finset.sum_range_sub' (fun k => f (m + k)) (n - m)
  simp only [Nat.add_assoc, Nat.add_zero] at h ⊢
  rw [h, Nat.add_sub_cancel' hmn]

/-- `Real.log n ≥ 1` for natural `n ≥ 4`. -/
lemma one_le_log_of_four_le {n : ℕ} (hn : 4 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  rw [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (n : ℝ))]
  have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
  linarith [Real.exp_one_lt_three]

theorem abelLogWeightBound (g : ℕ → ℂ) (K : ℝ) (t Y : ℕ)
    (hK : 0 ≤ K) (hY : 3 ≤ Y) (hYt : Y + 1 ≤ t)
    (hG : ∀ n : ℕ, Y + 1 ≤ n → n ≤ t + 1 → ‖∑ i ∈ Finset.range n, g i‖ ≤ K * n) :
    ‖∑ i ∈ Finset.Ico (Y + 1) (t + 1), ((Real.log (i : ℝ))⁻¹ : ℝ) • g i‖ ≤ 100 * K * t := by
  have hY4 : 4 ≤ Y + 1 := by omega
  have ht4 : 4 ≤ t := by omega
  have hmn : Y + 1 < t + 1 := by omega
  -- the weight `1 / log i` is positive, at most `1`, and decreasing on `i ≥ 4`
  have hpos : ∀ i : ℕ, 4 ≤ i → 0 < (Real.log (i : ℝ))⁻¹ := by
    intro i hi
    have h1 : (1 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 1 < i)
    exact inv_pos.mpr (Real.log_pos h1)
  have hle1 : ∀ i : ℕ, 4 ≤ i → (Real.log (i : ℝ))⁻¹ ≤ 1 := by
    intro i hi
    exact inv_le_one_of_one_le₀ (one_le_log_of_four_le hi)
  have hdec : ∀ i : ℕ, 4 ≤ i → (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.log (i : ℝ))⁻¹ := by
    intro i hi
    have h1 : 0 < Real.log (i : ℝ) := by
      have h2 : (1 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 1 < i)
      exact Real.log_pos h2
    have h2 : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    simpa only [one_div] using one_div_le_one_div_of_le h1 h2
  -- Abel summation
  rw [Finset.sum_Ico_by_parts (f := fun i : ℕ => ((Real.log (i : ℝ))⁻¹ : ℝ)) (g := g) hmn,
    Nat.add_sub_cancel]
  set A : ℂ := ((Real.log (t : ℝ))⁻¹ : ℝ) • (∑ i ∈ Finset.range (t + 1), g i) with hAdef
  set B : ℂ := ((Real.log ((Y + 1 : ℕ) : ℝ))⁻¹ : ℝ) • (∑ i ∈ Finset.range (Y + 1), g i)
    with hBdef
  set C : ℂ := ∑ i ∈ Finset.Ico (Y + 1) t,
      (((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ) - ((Real.log (i : ℝ))⁻¹ : ℝ)) •
        (∑ j ∈ Finset.range (i + 1), g j) with hCdef
  have hA : ‖A‖ ≤ 2 * K * t := by
    rw [hAdef, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos t ht4)]
    have hGt : ‖∑ i ∈ Finset.range (t + 1), g i‖ ≤ K * ((t + 1 : ℕ) : ℝ) :=
      hG (t + 1) (by omega) le_rfl
    have hGt2 : ‖∑ i ∈ Finset.range (t + 1), g i‖ ≤ K * (2 * (t : ℝ)) := by
      refine le_trans hGt (mul_le_mul_of_nonneg_left ?_ hK)
      have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
      push_cast
      linarith
    calc (Real.log (t : ℝ))⁻¹ * ‖∑ i ∈ Finset.range (t + 1), g i‖
        ≤ 1 * (K * (2 * (t : ℝ))) :=
          mul_le_mul (hle1 t ht4) hGt2 (norm_nonneg _) zero_le_one
      _ = 2 * K * t := by ring
  have hB : ‖B‖ ≤ K * t := by
    rw [hBdef, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos (Y + 1) hY4)]
    have hGY : ‖∑ i ∈ Finset.range (Y + 1), g i‖ ≤ K * ((Y + 1 : ℕ) : ℝ) :=
      hG (Y + 1) le_rfl (by omega)
    calc (Real.log ((Y + 1 : ℕ) : ℝ))⁻¹ * ‖∑ i ∈ Finset.range (Y + 1), g i‖
        ≤ 1 * (K * ((Y + 1 : ℕ) : ℝ)) :=
          mul_le_mul (hle1 (Y + 1) hY4) hGY (norm_nonneg _) zero_le_one
      _ ≤ K * t := by
          rw [one_mul]
          apply mul_le_mul_of_nonneg_left _ hK
          exact_mod_cast hYt
  have hC : ‖C‖ ≤ K * t := by
    rw [hCdef]
    calc ‖∑ i ∈ Finset.Ico (Y + 1) t,
            (((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ) - ((Real.log (i : ℝ))⁻¹ : ℝ)) •
              (∑ j ∈ Finset.range (i + 1), g j)‖
        ≤ ∑ i ∈ Finset.Ico (Y + 1) t,
            ‖(((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ) - ((Real.log (i : ℝ))⁻¹ : ℝ)) •
              (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.Ico (Y + 1) t,
            |((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ) - ((Real.log (i : ℝ))⁻¹ : ℝ)| *
              ‖∑ j ∈ Finset.range (i + 1), g j‖ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i ∈ Finset.Ico (Y + 1) t,
            (((Real.log (i : ℝ))⁻¹ : ℝ) - ((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ)) *
              (K * t) := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
          have hi4 : 4 ≤ i := le_trans hY4 hi1
          have hle : (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.log (i : ℝ))⁻¹ := hdec i hi4
          have habs : |((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ) - ((Real.log (i : ℝ))⁻¹ : ℝ)|
              = ((Real.log (i : ℝ))⁻¹ : ℝ) - ((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ) := by
            rw [abs_of_nonpos (sub_nonpos.mpr hle)]
            ring
          rw [habs]
          have hGi : ‖∑ j ∈ Finset.range (i + 1), g j‖ ≤ K * t := by
            have h1 : ‖∑ j ∈ Finset.range (i + 1), g j‖ ≤ K * ((i + 1 : ℕ) : ℝ) :=
              hG (i + 1) (by omega) (by omega)
            have h2 : ((i + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by
              exact_mod_cast (by omega : i + 1 ≤ t)
            exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hK)
          exact mul_le_mul le_rfl hGi (norm_nonneg _) (by linarith)
      _ = K * t * ∑ i ∈ Finset.Ico (Y + 1) t,
            (((Real.log (i : ℝ))⁻¹ : ℝ) - ((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ)) := by
          rw [← Finset.sum_mul, mul_comm]
      _ = K * t * (((Real.log ((Y + 1 : ℕ) : ℝ))⁻¹ : ℝ) - ((Real.log (t : ℝ))⁻¹ : ℝ)) := by
          rw [sum_Ico_sub_succ_eq (fun i : ℕ => ((Real.log (i : ℝ))⁻¹ : ℝ)) hYt]
      _ ≤ K * t := by
          have hft : (0 : ℝ) ≤ (Real.log (t : ℝ))⁻¹ := le_of_lt (hpos t ht4)
          have hfY : (Real.log ((Y + 1 : ℕ) : ℝ))⁻¹ ≤ 1 := hle1 (Y + 1) hY4
          have hKt : (0 : ℝ) ≤ K * t := mul_nonneg hK (Nat.cast_nonneg t)
          calc K * t * (((Real.log ((Y + 1 : ℕ) : ℝ))⁻¹ : ℝ) - ((Real.log (t : ℝ))⁻¹ : ℝ))
              ≤ K * t * 1 := mul_le_mul_of_nonneg_left (by linarith) hKt
            _ = K * t := mul_one _
  have h1 : ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le _ _
  have h2 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  have h4 : (4 : ℝ) * K * t ≤ 100 * K * t := by
    nlinarith [mul_nonneg hK (Nat.cast_nonneg t)]
  linarith

end Work.NumberTheory.Chen.BTermCount
