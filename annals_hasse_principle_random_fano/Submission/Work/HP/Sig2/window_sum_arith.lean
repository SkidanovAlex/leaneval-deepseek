import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.window_sum_summand
import Submission.Work.HP.Sig2.window_arith_pow_bound

set_option linter.unusedVariables false

namespace Work.HP.Sig2

/-- Log-vs-linear bound: `1 + logb 2 (ρ (Δ+1)) ≤ (4ρ+4) log (2Δ)` for `ρ ≥ 1`, `Δ ≥ 1`. -/
lemma window_arith_log_bound (r : ℕ) (Kmink Δ : ℝ) (hKmink : 1 ≤ Kmink) (hΔ : 1 ≤ Δ) :
    1 + Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))
      ≤ (4 * ((2 : ℝ) ^ r * Kmink) + 4) * Real.log (2 * Δ) := by
  have hKpos : (0 : ℝ) < Kmink := lt_of_lt_of_le zero_lt_one hKmink
  set ρ : ℝ := (2 : ℝ) ^ r * Kmink with hρdef
  set L : ℝ := Real.log (2 * Δ) with hLdef
  have hρ1 : (1 : ℝ) ≤ ρ := by
    rw [hρdef]
    have h2r : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    nlinarith [h2r, hKmink]
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL0 : 0 ≤ L := by
    rw [hLdef]; exact Real.log_nonneg (by linarith)
  have hLhalf : (1 : ℝ) / 2 ≤ L := by
    have h2 : Real.log 2 ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hinv : (Real.log 2)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hlog2pos]
    linarith
  have hsplit : Real.logb 2 (ρ * (Δ + 1)) = Real.logb 2 ρ + Real.logb 2 (Δ + 1) :=
    Real.logb_mul (ne_of_gt hρ0) (by linarith : (Δ + 1 : ℝ) ≠ 0)
  have hb1 : Real.logb 2 ρ ≤ 4 * ρ * L := by
    have hbase : Real.log ρ / Real.log 2 ≤ 2 * ρ := by
      rw [div_eq_mul_inv]
      calc Real.log ρ * (Real.log 2)⁻¹ ≤ ρ * (Real.log 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (Real.log_le_self hρ0.le) (inv_nonneg.mpr hlog2pos.le)
        _ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hinv hρ0.le
        _ = 2 * ρ := by ring
    have hlogb : Real.logb 2 ρ ≤ 2 * ρ := by
      rw [← Real.log_div_log]; exact hbase
    have h2L : (2 : ℝ) ≤ 4 * L := by linarith
    calc Real.logb 2 ρ ≤ 2 * ρ := hlogb
      _ = ρ * 2 := by ring
      _ ≤ ρ * (4 * L) := mul_le_mul_of_nonneg_left h2L hρ0.le
      _ = 4 * ρ * L := by ring
  have hb2 : Real.logb 2 (Δ + 1) ≤ 2 * L := by
    have hlog : Real.log (Δ + 1) ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
    have hbase : Real.log (Δ + 1) / Real.log 2 ≤ L / Real.log 2 :=
      div_le_div_of_nonneg_right hlog hlog2pos.le
    have hlogb : Real.logb 2 (Δ + 1) ≤ L / Real.log 2 := by
      rw [← Real.log_div_log]; exact hbase
    have h2 : L / Real.log 2 ≤ 2 * L := by
      rw [div_eq_mul_inv]
      calc L * (Real.log 2)⁻¹ ≤ L * 2 := mul_le_mul_of_nonneg_left hinv hL0
        _ = 2 * L := by ring
    linarith
  have hb0 : (1 : ℝ) ≤ 2 * L := by linarith
  rw [hsplit]
  nlinarith [hb0, hb1, hb2]

theorem window_sum_arith (n r : ℕ) (hn : 2 ≤ n) (hr : 3 ≤ r) (hrn : r ≤ n + 1)
    (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (Cdya : ℝ) (hCdya : 0 < Cdya)
    (hdya : ∀ (L' : ℝ), 0 ≤ L' →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈L'⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈L'⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
        else 0))
      ≤ Cdya * 2 ^ (((n + 1) - 2) * L') * (1 + L') ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Δ : ℝ), 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
            ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
              (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
        else 0))
      ≤ K * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
  have hKpos : (0 : ℝ) < Kmink := lt_of_lt_of_le zero_lt_one hKmink
  have hρpos : (0 : ℝ) < (2 : ℝ) ^ r * Kmink := mul_pos (by positivity) hKpos
  have hρ1 : (1 : ℝ) ≤ (2 : ℝ) ^ r * Kmink := by
    have h2r : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    nlinarith [h2r, hKmink]
  refine ⟨Cdya * (2 * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (4 * ((2 : ℝ) ^ r * Kmink) + 4) ^ 2, ?_, ?_⟩
  · have ha : (0 : ℝ) < Cdya := hCdya
    have hb : (0 : ℝ) < (2 * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) :=
      pow_pos (by linarith) _
    have hc : (0 : ℝ) < (4 * ((2 : ℝ) ^ r * Kmink) + 4) ^ 2 := pow_pos (by linarith) 2
    exact mul_pos (mul_pos ha hb) hc
  · intro Δ hΔ
    set X : ℝ := (2 : ℝ) ^ r * Kmink * (Δ + 1) with hXdef
    have hXpos : 0 < X := by
      rw [hXdef]
      exact mul_pos (mul_pos (by positivity) hKpos) (by linarith)
    have hX1 : 1 ≤ X := by
      rw [hXdef]
      have h2 : (1 : ℝ) ≤ Δ + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((2 : ℝ) ^ r * Kmink) * (Δ + 1) :=
            mul_le_mul hρ1 h2 (by norm_num) (le_of_lt hρpos)
    have hLb : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX1
    have hdyainst := hdya (Real.logb 2 X) hLb
    have hsum_eq :
        (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈Real.logb 2 X⌉₊ + 1)),
          (if Monotone k ∧ (∑ j : Fin r, k j) ≤ ⌈Real.logb 2 X⌉₊ then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
              ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
                (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
          else 0))
        = (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈Real.logb 2 X⌉₊ + 1)),
          (if Monotone k ∧ (∑ j : Fin r, k j) ≤ ⌈Real.logb 2 X⌉₊ then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
          else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hc : Monotone k ∧ (∑ j : Fin r, k j) ≤ ⌈Real.logb 2 X⌉₊
      · rw [if_pos hc, if_pos hc]
        exact window_sum_summand n r (by omega) hr k
      · rw [if_neg hc, if_neg hc]
    have hmain : (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈Real.logb 2 X⌉₊ + 1)),
          (if Monotone k ∧ (∑ j : Fin r, k j) ≤ ⌈Real.logb 2 X⌉₊ then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
              ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
                (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
          else 0))
        ≤ Cdya * 2 ^ (((n + 1) - 2) * Real.logb 2 X) * (1 + Real.logb 2 X) ^ 2 :=
      le_trans (le_of_eq hsum_eq) hdyainst
    have hpow := window_arith_pow_bound n r hn Kmink Δ hKmink hΔ
    rw [← hXdef] at hpow
    have hcast : ((n + 1 - 2 : ℕ) : ℝ) = (n : ℝ) + 1 - 2 := by
      have h : n + 1 - 2 = n - 1 := by omega
      rw [h, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]; ring
    rw [hcast] at hpow
    have hlog := window_arith_log_bound r Kmink Δ hKmink hΔ
    rw [← hXdef] at hlog
    have hlog2 : (1 + Real.logb 2 X) ^ 2
        ≤ (4 * ((2 : ℝ) ^ r * Kmink) + 4) ^ 2 * Real.log (2 * Δ) ^ 2 := by
      have h1 : 0 ≤ 1 + Real.logb 2 X := by linarith
      have h2 : (1 + Real.logb 2 X) ^ 2 ≤ ((4 * ((2 : ℝ) ^ r * Kmink) + 4) * Real.log (2 * Δ)) ^ 2 :=
        pow_le_pow_left₀ h1 hlog 2
      simpa [mul_pow] using h2
    have hb0 : (0 : ℝ) ≤ (2 * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * Δ ^ (n - 1) := by
      apply mul_nonneg
      · exact pow_nonneg (by linarith) _
      · exact pow_nonneg (by linarith) _
    have hmul : 2 ^ (((n + 1) - 2) * Real.logb 2 X) * (1 + Real.logb 2 X) ^ 2
        ≤ ((2 * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * Δ ^ (n - 1)) *
          ((4 * ((2 : ℝ) ^ r * Kmink) + 4) ^ 2 * Real.log (2 * Δ) ^ 2) :=
      mul_le_mul hpow hlog2 (sq_nonneg _) hb0
    have hmin : 2 * min (r - 2) 1 = 2 := by
      have h : min (r - 2) 1 = 1 := by
        rw [Nat.min_eq_right]; omega
      rw [h]
    have hmain' : (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈Real.logb 2 X⌉₊ + 1)),
          (if Monotone k ∧ (∑ j : Fin r, k j) ≤ ⌈Real.logb 2 X⌉₊ then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
              ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
                (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
          else 0))
        ≤ Cdya * (2 ^ (((n + 1) - 2) * Real.logb 2 X) * (1 + Real.logb 2 X) ^ 2) := by
      calc _ ≤ Cdya * 2 ^ (((n + 1) - 2) * Real.logb 2 X) * (1 + Real.logb 2 X) ^ 2 := hmain
        _ = Cdya * (2 ^ (((n + 1) - 2) * Real.logb 2 X) * (1 + Real.logb 2 X) ^ 2) := by ring
    calc _ ≤ Cdya * (2 ^ (((n + 1) - 2) * Real.logb 2 X) * (1 + Real.logb 2 X) ^ 2) := hmain'
      _ ≤ Cdya * (((2 * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * Δ ^ (n - 1)) *
            ((4 * ((2 : ℝ) ^ r * Kmink) + 4) ^ 2 * Real.log (2 * Δ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hmul hCdya.le
      _ = (Cdya * (2 * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (4 * ((2 : ℝ) ^ r * Kmink) + 4) ^ 2)
            * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
            rw [hmin]; ring

end Work.HP.Sig2
