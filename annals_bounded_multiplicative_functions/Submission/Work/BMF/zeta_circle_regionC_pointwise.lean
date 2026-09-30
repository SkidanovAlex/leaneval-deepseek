import Mathlib
import Submission.Work.BMF.zeta_growth_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For `σ ≥ 1` and `|t| ≥ 3` one has `log ‖ζ(σ+it)‖ ≤ log(log|t| + 4)`: the Euler–Maclaurin
bound (`zeta_emN_bound`) with `N = ⌊|t|⌋₊` together with the harmonic-number estimate
`Σ_{n ≤ N} n^{-1} ≤ 1 + log N`. -/
theorem zeta_circle_regionC_pointwise {σ t τ : ℝ} (hσ : 1 ≤ σ) (ht : 3 ≤ |t|)
    (ht2 : |t| ≤ 2 * τ + 3) :
    Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log (Real.log (2 * τ + 3) + 4) := by
  have hσ0 : 0 < σ := by linarith
  have ht1 : 1 ≤ |t| := by linarith
  have habs3 : 0 < |t| := by linarith
  set N : ℕ := ⌊|t|⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]; exact (Nat.one_le_floor_iff (|t|)).mpr (by linarith : (1 : ℝ) ≤ |t|)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hb := zeta_emN_bound (σ := σ) (t := t) hσ0 ht1 N hN1
  have hterm1 : (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) ≤ 1 + Real.log |t| := by
    have hstep1 : (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ))
        ≤ ∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hb1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      calc ((n : ℕ) : ℝ) ^ (-σ) ≤ ((n : ℕ) : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
        _ = (((n : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
    have hstep2 : (∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℝ))⁻¹) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp
    have hstep3 : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
    have hstep4 : Real.log (N : ℝ) ≤ Real.log |t| := by
      apply Real.log_le_log hNpos
      exact Nat.floor_le (abs_nonneg t)
    linarith
  have hterm2 : (((N : ℕ) : ℝ) ^ (1 - σ)) / |t| ≤ 1 / 3 := by
    have hle1 : ((N : ℕ) : ℝ) ^ (1 - σ) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN1)
        (show (1 : ℝ) - σ ≤ (0 : ℝ) by linarith)
      rw [Real.rpow_zero] at h
      exact h
    calc ((N : ℕ) : ℝ) ^ (1 - σ) / |t| ≤ 1 / |t| :=
          div_le_div_of_nonneg_right hle1 (le_of_lt habs3)
      _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) ht
  have hterm3 : (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * ((N : ℕ) : ℝ) ^ (-σ) ≤ 8 / 3 := by
    have hle : ((N : ℕ) : ℝ) ^ (-σ) ≤ 1 / (N : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN1)
        (show -σ ≤ (-1 : ℝ) by linarith)
      rw [Real.rpow_neg_one] at h
      simpa [one_div] using h
    have hnorm : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ σ + |t| := by
      calc ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ‖((σ : ℂ))‖ + ‖((t : ℂ) * Complex.I)‖ := norm_add_le _ _
        _ = |σ| + |t| := by simp
        _ = σ + |t| := by rw [abs_of_nonneg (le_of_lt hσ0)]
    have hfloor : (|t| : ℝ) - 1 < (N : ℝ) := by
      have h := Nat.lt_floor_add_one |t|
      rw [hNdef]; linarith
    have hN2 : |t| / 2 ≤ (N : ℝ) := by linarith [hfloor, ht]
    calc (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * ((N : ℕ) : ℝ) ^ (-σ)
        ≤ ((σ + |t|) / σ) * (1 / (N : ℝ)) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right hnorm (le_of_lt hσ0)
          · exact hle
          · positivity
          · positivity
      _ = (1 + |t| / σ) / (N : ℝ) := by
          field_simp
      _ ≤ (1 + |t|) / (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
          have hdt : |t| / σ ≤ |t| := by
            rw [div_le_iff₀ hσ0]
            nlinarith [abs_nonneg t, hσ]
          linarith
      _ ≤ (1 + |t|) / (|t| / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hN2
      _ = 2 * (1 + |t|) / |t| := by field_simp
      _ ≤ 8 / 3 := by
          rw [div_le_iff₀ habs3]
          nlinarith [ht]
  have htotal : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Real.log |t| + 4 := by
    linarith [hb, hterm1, hterm2, hterm3]
  have hlogt4 : 0 < Real.log |t| + 4 := by
    have : 0 ≤ Real.log |t| := Real.log_nonneg ht1
    linarith
  have hstep : Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.log (Real.log |t| + 4) := by
    rcases eq_or_ne ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ 0 with hz | hz
    · rw [hz, Real.log_zero]
      exact Real.log_nonneg (by linarith [Real.log_nonneg ht1])
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)) htotal
  have hlogt : Real.log |t| ≤ Real.log (2 * τ + 3) := Real.log_le_log habs3 ht2
  calc Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.log (Real.log |t| + 4) := hstep
    _ ≤ Real.log (Real.log (2 * τ + 3) + 4) := by
        apply Real.log_le_log hlogt4
        linarith

end Work.BMF
