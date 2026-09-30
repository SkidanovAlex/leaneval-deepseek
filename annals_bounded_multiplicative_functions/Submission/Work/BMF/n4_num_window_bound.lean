import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Core real-variable inequality used by `n4_num_window_bound`.

For `ℓ ≥ 2`, positive constants `C₁, K` there is a threshold `B₀` such that whenever
`L ≥ B₀`, `q ≥ 1`, `L^{ℓ+3} ≤ q`, `0 ≤ M ≤ (ℓ-1) L` and `r ≤ q^{1/(2ℓ)}`, one has
`2 C₁^ℓ (ℓ+1)^ℓ r L^ℓ M ≤ K q`.  The slack comes from the fact that `q` eventually dwarfs
`q^{1/(2ℓ) + (ℓ+1)/(ℓ+3)}` since `1/(2ℓ) + (ℓ+1)/(ℓ+3) < 1`. -/
lemma rpow_core (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (C₁ K : ℝ) (hC₁ : 0 < C₁) (hK : 0 < K) :
    ∃ B₀ : ℝ, ∀ L M q r : ℝ, B₀ ≤ L → 1 ≤ q → L ^ (ℓ + 3) ≤ q → 0 ≤ M →
      M ≤ ((ℓ : ℝ) - 1) * L → r ≤ q ^ ((1 : ℝ) / (2 * (ℓ : ℝ))) →
      2 * C₁ ^ ℓ * ((ℓ + 1 : ℕ) : ℝ) ^ ℓ * r * L ^ ℓ * M ≤ K * q := by
  set A : ℝ := 2 * C₁ ^ ℓ * ((ℓ + 1 : ℕ) : ℝ) ^ ℓ with hA_def
  have hA_pos : 0 < A := by rw [hA_def]; positivity
  have hA_nn : 0 ≤ A := le_of_lt hA_pos
  set d : ℝ := 2 / ((ℓ : ℝ) + 3) - 1 / (2 * (ℓ : ℝ)) with hd_def
  have h3pos : (0:ℝ) < (ℓ:ℝ)+3 := by positivity
  have hd_pos : 0 < d := by
    rw [hd_def]
    have h2 : (0:ℝ) < 2*(ℓ:ℝ) := by positivity
    rw [sub_pos, div_lt_div_iff₀ h2 h3pos]
    have : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
    nlinarith [this]
  have hℓm1 : 0 ≤ (ℓ:ℝ) - 1 := by
    have : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
    linarith
  have hd3pos : 0 < d * ((ℓ:ℝ)+3) := by positivity
  set W : ℝ := A * ((ℓ:ℝ) - 1) / K with hW_def
  have hW_nn : 0 ≤ W := by rw [hW_def]; positivity
  refine ⟨max 1 (W ^ (1 / (d * ((ℓ:ℝ)+3)))), ?_⟩
  intro L M q r hB hq1 hLq hM0 hML hr
  have hB1 : (1:ℝ) ≤ max 1 (W ^ (1 / (d * ((ℓ:ℝ)+3)))) := le_max_left _ _
  have hL1 : (1:ℝ) ≤ L := le_trans hB1 hB
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hqpos : 0 < q := by linarith
  have hB0pos : (0:ℝ) < max 1 (W ^ (1 / (d * ((ℓ:ℝ)+3)))) := by positivity
  have hLq' : L ^ ((ℓ:ℝ) + 3) ≤ q := by
    have hcast : ((ℓ+3:ℕ):ℝ) = (ℓ:ℝ)+3 := by push_cast; ring
    rw [← hcast, Real.rpow_natCast]; exact hLq
  have hB0L : (max 1 (W ^ (1 / (d * ((ℓ:ℝ)+3))))) ^ ((ℓ:ℝ)+3) ≤ q := by
    have := Real.rpow_le_rpow (le_of_lt hB0pos) hB (le_of_lt h3pos)
    exact le_trans this hLq'
  have hB0q : (max 1 (W ^ (1 / (d * ((ℓ:ℝ)+3))))) ^ (d*((ℓ:ℝ)+3)) ≤ q ^ d := by
    have h1 : ((max 1 (W ^ (1 / (d * ((ℓ:ℝ)+3))))) ^ ((ℓ:ℝ)+3)) ^ d ≤ q ^ d :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hB0pos) _) hB0L (le_of_lt hd_pos)
    rw [← Real.rpow_mul (le_of_lt hB0pos)] at h1
    rwa [mul_comm ((ℓ:ℝ)+3) d] at h1
  have hWq : W ≤ (max 1 (W ^ (1 / (d * ((ℓ:ℝ)+3))))) ^ (d*((ℓ:ℝ)+3)) := by
    have h1 : (W ^ (1 / (d * ((ℓ:ℝ)+3)))) ^ (d*((ℓ:ℝ)+3)) ≤
        (max 1 (W ^ (1 / (d * ((ℓ:ℝ)+3))))) ^ (d*((ℓ:ℝ)+3)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hW_nn _) (le_max_right _ _) (le_of_lt hd3pos)
    rw [← Real.rpow_mul hW_nn] at h1
    have hyz : (1 / (d * ((ℓ:ℝ)+3))) * (d*((ℓ:ℝ)+3)) = 1 := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hd3pos)]
    rwa [hyz, Real.rpow_one] at h1
  have hWqd : W ≤ q ^ d := le_trans hWq hB0q
  have hKW : A * ((ℓ:ℝ) - 1) ≤ K * q ^ d := by
    have h2 : K * W ≤ K * q ^ d := mul_le_mul_of_nonneg_left hWqd (le_of_lt hK)
    rw [hW_def] at h2
    have hKW_eq : K * (A * ((ℓ:ℝ)-1) / K) = A * ((ℓ:ℝ)-1) := by field_simp
    rwa [hKW_eq] at h2
  have hfac : ((ℓ:ℝ)+3) * (((ℓ:ℝ)+1)/((ℓ:ℝ)+3)) = (ℓ:ℝ)+1 := by field_simp
  have hstep : L ^ (ℓ+1) = (L ^ ((ℓ:ℝ)+3)) ^ (((ℓ:ℝ)+1)/((ℓ:ℝ)+3)) := by
    rw [show L ^ (ℓ+1) = L ^ ((ℓ:ℝ)+1) by
        rw [show ((ℓ:ℝ)+1) = ((ℓ+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]]
    conv_lhs => rw [← hfac]
    rw [Real.rpow_mul hLnn]
  have hz_nn : 0 ≤ (((ℓ:ℝ)+1)/((ℓ:ℝ)+3)) := by positivity
  have hLp1_le : L ^ (ℓ+1) ≤ q ^ (((ℓ:ℝ)+1)/((ℓ:ℝ)+3)) := by
    rw [hstep]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hLnn _) hLq' hz_nn
  have htS : q ^ (1/(2*(ℓ:ℝ))) * L ^ (ℓ+1) ≤ q ^ (1 - d) := by
    have h1 : q ^ (1/(2*(ℓ:ℝ))) * L ^ (ℓ+1) ≤
        q ^ (1/(2*(ℓ:ℝ))) * q ^ (((ℓ:ℝ)+1)/((ℓ:ℝ)+3)) :=
      mul_le_mul_of_nonneg_left hLp1_le (Real.rpow_nonneg (le_of_lt hqpos) _)
    rw [← Real.rpow_add hqpos] at h1
    have hexp : 1/(2*(ℓ:ℝ)) + ((ℓ:ℝ)+1)/((ℓ:ℝ)+3) = 1 - d := by
      rw [hd_def]; field_simp; ring
    rwa [hexp] at h1
  have hLM : L ^ ℓ * M ≤ ((ℓ:ℝ)-1) * L ^ (ℓ+1) := by
    have h1 : L ^ ℓ * M ≤ L ^ ℓ * (((ℓ:ℝ)-1) * L) :=
      mul_le_mul_of_nonneg_left hML (pow_nonneg hLnn ℓ)
    calc L ^ ℓ * M ≤ L ^ ℓ * (((ℓ:ℝ)-1) * L) := h1
      _ = ((ℓ:ℝ)-1) * L ^ (ℓ+1) := by rw [pow_succ]; ring
  have hLMnn : 0 ≤ L ^ ℓ * M := mul_nonneg (pow_nonneg hLnn ℓ) hM0
  have key : r * (L ^ ℓ * M) ≤ q ^ (1/(2*(ℓ:ℝ))) * (((ℓ:ℝ)-1) * L ^ (ℓ+1)) :=
    mul_le_mul hr hLM hLMnn (Real.rpow_nonneg (le_of_lt hqpos) _)
  have htS' : q ^ (1/(2*(ℓ:ℝ))) * (((ℓ:ℝ)-1) * L ^ (ℓ+1)) ≤ ((ℓ:ℝ)-1) * q ^ (1-d) := by
    have h1 : q ^ (1/(2*(ℓ:ℝ))) * (((ℓ:ℝ)-1) * L ^ (ℓ+1))
        = ((ℓ:ℝ)-1) * (q ^ (1/(2*(ℓ:ℝ))) * L ^ (ℓ+1)) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left htS hℓm1
  have hfin : A * (r * (L ^ ℓ * M)) ≤ A * (((ℓ:ℝ)-1) * q ^ (1-d)) := by
    calc A * (r * (L ^ ℓ * M)) ≤ A * (q ^ (1/(2*(ℓ:ℝ))) * (((ℓ:ℝ)-1) * L ^ (ℓ+1))) :=
          mul_le_mul_of_nonneg_left key hA_nn
      _ ≤ A * (((ℓ:ℝ)-1) * q ^ (1-d)) := mul_le_mul_of_nonneg_left htS' hA_nn
  have hq1d : q ^ (1-d) = q / q ^ d := by rw [Real.rpow_sub hqpos, Real.rpow_one]
  have hqdpos : 0 < q ^ d := Real.rpow_pos_of_pos hqpos d
  have hlast : A * (((ℓ:ℝ)-1) * q ^ (1-d)) ≤ K * q := by
    rw [hq1d]
    have h1 : A * (((ℓ:ℝ)-1) * (q / q ^ d)) = (A * ((ℓ:ℝ)-1) / q ^ d) * q := by
      field_simp
    rw [h1]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hqpos)
    rw [div_le_iff₀ hqdpos]
    exact hKW
  calc A * r * L ^ ℓ * M = A * (r * (L ^ ℓ * M)) := by ring
    _ ≤ A * (((ℓ:ℝ)-1) * q ^ (1-d)) := hfin
    _ ≤ K * q := hlast

lemma n4_num_window_bound (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (C₁ K : ℝ) (hC₁ : 0 < C₁) (hK : 0 < K) :
    ∃ P₀ : ℝ, ∀ (P N C₀ r : ℝ) (q : ℕ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
      1 / Real.log P ≤ C₀ → 1 ≤ q → (Real.log P) ^ (ℓ + 3) ≤ (q : ℝ) →
      r ≤ (q : ℝ) ^ ((1 : ℝ) / (2 * (ℓ : ℝ))) →
      (C₁ * pi0 P) ^ ℓ * ((ℓ + 1 : ℕ) : ℝ) ^ ℓ * r * (2 * C₀ * P ^ ℓ / (N * (q : ℝ))) ≤
        K * C₀ * pi0 P ^ (2 * ℓ) / N * (1 / Real.log N) := by
  obtain ⟨B₀, hB₀⟩ := rpow_core ℓ hℓ C₁ K hC₁ hK
  refine ⟨Real.exp (max B₀ 1), ?_⟩
  intro P N C₀ r q hP hN hNP hC0 hq1 hlogq hr
  have hP₀pos : 0 < Real.exp (max B₀ 1) := Real.exp_pos _
  have hlogP₀ : Real.log (Real.exp (max B₀ 1)) = max B₀ 1 := Real.log_exp _
  have hPpos : 0 < P := lt_of_lt_of_le hP₀pos hP
  have hlogP_ge : max B₀ 1 ≤ Real.log P := by
    rw [← hlogP₀]; exact Real.log_le_log hP₀pos hP
  have hB₀_le : B₀ ≤ Real.log P := le_trans (le_max_left _ _) hlogP_ge
  have hLpos : 0 < Real.log P :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hlogP_ge)
  have hNpos : 0 < N := by linarith
  have hM0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith : (1:ℝ) ≤ N)
  have hMpos : 0 < Real.log N := Real.log_pos (by linarith : (1:ℝ) < N)
  have hML : Real.log N ≤ ((ℓ:ℝ)-1) * Real.log P := by
    have hstep : Real.log N ≤ Real.log (P ^ (ℓ-1)) := Real.log_le_log hNpos hNP
    rw [Real.log_pow] at hstep
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ)] at hstep
    simpa only [Nat.cast_one] using hstep
  have hq1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqpos : 0 < (q:ℝ) := by linarith
  have hC0pos : 0 < C₀ := lt_of_lt_of_le (one_div_pos.mpr hLpos) hC0
  have hkey := hB₀ (Real.log P) (Real.log N) (q:ℝ) r hB₀_le hq1' hlogq hM0 hML hr
  rw [pi0]
  rw [mul_pow, div_pow, div_pow]
  field_simp
  ring_nf
  rw [pow_mul, pow_mul]
  simp only [Nat.add_comm 1 ℓ]
  have hb : 0 < (Real.log P)^ℓ := pow_pos hLpos ℓ
  have ha : 0 < (P^ℓ)^2 := by positivity
  have hstep := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hkey (le_of_lt hb)) (le_of_lt ha)
  nlinarith [hstep]

end Work.BMF
