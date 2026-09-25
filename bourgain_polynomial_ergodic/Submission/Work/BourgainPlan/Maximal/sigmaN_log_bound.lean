import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.iwPN_le_exp

namespace Work.BourgainPlan.Maximal

/-- For `s > 0` and `B ≥ 0`, `N^s ≥ B` for all sufficiently large natural `N`.
(`C = ⌈B^{1/s}⌉`, and `(B^{1/s})^s = B`.) -/
lemma exists_rpow_ge {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B) :
    ∃ C : ℕ, ∀ N : ℕ, (C : ℝ) ≤ (N : ℝ) → B ≤ (N : ℝ) ^ s := by
  refine ⟨Nat.ceil (B ^ (1 / s)), fun N hN => ?_⟩
  have h1 : B ^ (1 / s) ≤ ((Nat.ceil (B ^ (1 / s)) : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (B ^ (1 / s)) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h3 : B ^ (1 / s) ≤ (N : ℝ) := le_trans h1 h2
  calc B = (B ^ (1 / s)) ^ s := by
        rw [← Real.rpow_mul hB, one_div, inv_mul_cancel₀ (ne_of_gt hs), Real.rpow_one]
    _ ≤ (N : ℝ) ^ s := Real.rpow_le_rpow (Real.rpow_nonneg hB _) h3 hs.le

/-- For `ρ > 0` and any `k : ℕ`, for all sufficiently large `N`,
`log (k+1) + k log (N+1) + k (N^{ρ/2} + 2) log N ≤ N^ρ`.  (Each summand is a fixed multiple of a polylogarithm in `N`, which is `o(N^ρ)`.) -/
theorem sigmaN_log_bound (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      Real.log ((k : ℝ) + 1) + (k : ℝ) * Real.log ((N : ℝ) + 1)
        + (k : ℝ) * ((N : ℝ) ^ (ρ / 2) + 2) * Real.log N ≤ (N : ℝ) ^ ρ := by
  have hs : 0 < ρ / 2 := by linarith
  have hK0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hc0 : 0 ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  -- the constant `p = log (k+1) + k` and the two thresholds
  set p : ℝ := Real.log ((k : ℝ) + 1) + (k : ℝ) with hp_def
  have hp0 : 0 ≤ p := by rw [hp_def]; linarith
  have hpK : (k : ℝ) ≤ p := by rw [hp_def]; linarith
  obtain ⟨C₁, hC₁3, hC₁⟩ :=
    Work.BourgainPlan.IonescuWainger.exists_log_le_rpow (4 * p + 4) (ρ / 2) (by linarith) hs
  obtain ⟨C₂, hC₂⟩ := exists_rpow_ge (s := ρ / 2) (B := 5) hs (by norm_num)
  refine ⟨max (Nat.ceil C₁) C₂, fun N hN => ?_⟩
  have hN₂ : (C₂ : ℝ) ≤ (N : ℝ) := by
    have h : C₂ ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast h
  have hN₁ : C₁ ≤ (N : ℝ) := by
    have hcN : Nat.ceil C₁ ≤ N := le_trans (le_max_left _ _) hN
    have h2 : ((Nat.ceil C₁ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcN
    linarith [Nat.le_ceil C₁, h2]
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := le_trans hC₁3 hN₁
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (le_trans (le_of_lt Real.exp_one_lt_three) hN3)
    rwa [Real.log_exp] at h
  have hlog0 : 0 ≤ Real.log (N : ℝ) := le_trans zero_le_one hlog1
  set y : ℝ := (N : ℝ) ^ (ρ / 2) with hy_def
  have hy0 : 0 ≤ y := by rw [hy_def]; exact Real.rpow_nonneg hNpos.le _
  have h5y : 5 ≤ y := by rw [hy_def]; exact hC₂ N hN₂
  have hA : (4 * p + 4) * Real.log (N : ℝ) ≤ y := by rw [hy_def]; exact hC₁ N hN₁
  have hA4 : 4 * p + 4 ≤ y := by
    have h := mul_le_mul_of_nonneg_left hlog1 (by linarith : (0 : ℝ) ≤ 4 * p + 4)
    linarith [hA, h]
  -- `3 k log N ≤ y` and `k y log N ≤ y²/4`
  have h3K : 3 * (k : ℝ) ≤ 4 * p + 4 := by linarith
  have h4K : 4 * (k : ℝ) ≤ 4 * p + 4 := by linarith
  have h3Klog : 3 * (k : ℝ) * Real.log (N : ℝ) ≤ y := by
    have h := mul_le_mul_of_nonneg_right h3K hlog0
    linarith [h, hA]
  have h4Klog : 4 * (k : ℝ) * Real.log (N : ℝ) ≤ y := by
    have h := mul_le_mul_of_nonneg_right h4K hlog0
    linarith [h, hA]
  have key1 : (k : ℝ) * y * Real.log (N : ℝ) ≤ y ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_right h4Klog (by linarith : (0 : ℝ) ≤ y / 4)
    nlinarith [h]
  -- `log (N+1) ≤ 1 + log N`
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ 1 + Real.log (N : ℝ) := by
    have h2N : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
    have h := Real.log_le_log (by linarith) h2N
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h
    have hlog2 : Real.log 2 ≤ 1 := le_of_lt (by
      have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num)
      linarith)
    linarith
  -- `p + y ≤ y²/2`
  have hpy : p + y ≤ y ^ 2 / 2 := by nlinarith [hA4, h5y]
  have hstep1 : Real.log ((k : ℝ) + 1) + (k : ℝ) * Real.log ((N : ℝ) + 1)
        + (k : ℝ) * (y + 2) * Real.log (N : ℝ) ≤ p + y + y ^ 2 / 4 := by
    have h1 : (k : ℝ) * Real.log ((N : ℝ) + 1) ≤ (k : ℝ) * (1 + Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogN1 hK0
    have hexp : (k : ℝ) * (y + 2) * Real.log (N : ℝ)
        = (k : ℝ) * y * Real.log (N : ℝ) + 2 * ((k : ℝ) * Real.log (N : ℝ)) := by ring
    have hkp : Real.log ((k : ℝ) + 1) ≤ p := by rw [hp_def]; linarith
    nlinarith [h1, hexp, h3Klog, key1, hkp]
  have hy2 : y ^ 2 = (N : ℝ) ^ ρ := by
    have h2 : y * y = (N : ℝ) ^ ρ := by
      rw [hy_def, ← Real.rpow_add hNpos]
      rw [show ρ / 2 + ρ / 2 = ρ by ring]
    nlinarith [h2]
  rw [← hy2]
  linarith [hstep1, hpy, hy0]

end Work.BourgainPlan.Maximal
