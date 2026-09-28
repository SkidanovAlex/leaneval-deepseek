import Mathlib

open MeasureTheory

namespace Work.HP.BallConeK

/-- The `p`-integral identity `∫_A^B k / t^{k+1} dt = 1/A^k - 1/B^k` for `0 < A ≤ B`.
The antiderivative is `-t^{-k}`, whose derivative is `k/t^{k+1}`. -/
theorem integral_k_div_pow_aux (k : ℕ) (hk : 1 ≤ k) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∫ t in A..B, (k : ℝ) / t ^ (k + 1) = 1 / A ^ k - 1 / B ^ k := by
  have hne : (-((k + 1 : ℕ) : ℤ)) ≠ -1 := by omega
  have hnotmem : (0 : ℝ) ∉ Set.uIcc A B := by
    rw [Set.uIcc_of_le hAB]
    intro h
    rw [Set.mem_Icc] at h
    exact absurd h.1 (not_le.mpr hA)
  have hz := integral_zpow (a := A) (b := B) (n := (-((k + 1 : ℕ) : ℤ)))
    (Or.inr ⟨hne, hnotmem⟩)
  have h_eq : (fun t : ℝ => (k : ℝ) / t ^ (k + 1))
      = fun t : ℝ => (k : ℝ) * t ^ (-((k + 1 : ℕ) : ℤ)) := by
    funext t
    rw [div_eq_mul_inv, zpow_neg, zpow_natCast]
  rw [h_eq, intervalIntegral.integral_const_mul, hz]
  have h1 : (-((k + 1 : ℕ) : ℤ) + 1 : ℤ) = -((k : ℕ) : ℤ) := by omega
  have h2 : (↑(-((k + 1 : ℕ) : ℤ)) + 1 : ℝ) = -((k : ℕ) : ℝ) := by push_cast; ring
  rw [h1, h2, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  rw [one_div, one_div]
  field_simp
  ring

/-- Weighted-error integral bound: if `|e t| ≤ C₀ t^{r-1} Y / d` on `[Y,T]` with `1 ≤ k`,
`k+1 < r`, `0 < Y ≤ T`, then the weighted error integral against `k/t^{k+1}` is bounded by
`C₀ (k+1) T^{r-k-1} Y / d`. -/
theorem weightedErrorIntegral (k r : ℕ) {Y T C₀ d : ℝ}
    (hk : 1 ≤ k) (hkr : k + 1 < r) (hY : 0 < Y) (hYT : Y ≤ T) (hd : 0 < d) (hC₀ : 0 ≤ C₀)
    (e : ℝ → ℝ) (he : ∀ t ∈ Set.Icc Y T, |e t| ≤ C₀ * t ^ (r - 1) * Y / d)
    (hi : IntervalIntegrable (fun t => (k : ℝ) / t ^ (k + 1) * (e t - e Y)) volume Y T) :
    |∫ t in Y..T, (k : ℝ) / t ^ (k + 1) * (e t - e Y)|
      ≤ (C₀ * (k + 1)) * (T ^ (r - k - 1) * Y / d) := by
  have hr1 : 1 ≤ r := by omega
  have hrk1 : k ≤ r := by omega
  have hTpos : 0 < T := lt_of_lt_of_le hY hYT
  -- Pointwise domination of the integrand by the two model summands.
  have hpt : ∀ t ∈ Set.Icc Y T, |(k : ℝ) / t ^ (k + 1) * (e t - e Y)|
      ≤ (k : ℝ) * (C₀ * Y / d) * t ^ (r - k - 2)
        + (C₀ * Y ^ r / d) * ((k : ℝ) / t ^ (k + 1)) := by
    intro t ht
    have htY : 0 < t := lt_of_lt_of_le hY ht.1
    have ht0 : t ≠ 0 := ne_of_gt htY
    have hkp : 0 ≤ (k : ℝ) / t ^ (k + 1) := by positivity
    have h1 : |e t| ≤ C₀ * t ^ (r - 1) * Y / d := he t ht
    have h2 : |e Y| ≤ C₀ * Y ^ (r - 1) * Y / d := he Y ⟨le_refl Y, hYT⟩
    have htri : |e t - e Y| ≤ |e t| + |e Y| := by
      simpa using abs_sub_le (e t) 0 (e Y)
    have hn : k + 1 + (r - k - 2) = r - 1 := by omega
    have htpow : t ^ (r - 1) = t ^ (k + 1) * t ^ (r - k - 2) := by rw [← hn, pow_add]
    have hYpow : Y ^ (r - 1) * Y = Y ^ r := by rw [← pow_succ, Nat.sub_add_cancel hr1]
    have hYpow2 : C₀ * Y ^ (r - 1) * Y = C₀ * Y ^ r := by rw [mul_assoc, hYpow]
    calc |(k : ℝ) / t ^ (k + 1) * (e t - e Y)|
        = ((k : ℝ) / t ^ (k + 1)) * |e t - e Y| := by rw [abs_mul, abs_of_nonneg hkp]
      _ ≤ ((k : ℝ) / t ^ (k + 1))
            * (C₀ * t ^ (r - 1) * Y / d + C₀ * Y ^ (r - 1) * Y / d) :=
          mul_le_mul_of_nonneg_left (by linarith) hkp
      _ = (k : ℝ) * (C₀ * Y / d) * t ^ (r - k - 2)
            + (C₀ * Y ^ r / d) * ((k : ℝ) / t ^ (k + 1)) := by
          rw [mul_add, htpow, hYpow2]
          field_simp
  -- Integrability of the two model summands.
  have hInt1 : IntervalIntegrable
      (fun t : ℝ => (k : ℝ) * (C₀ * Y / d) * t ^ (r - k - 2)) volume Y T :=
    (continuous_const.mul (continuous_id.pow (r - k - 2))).intervalIntegrable Y T
  have hInt2 : IntervalIntegrable
      (fun t : ℝ => (C₀ * Y ^ r / d) * ((k : ℝ) / t ^ (k + 1))) volume Y T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.const_mul
    apply ContinuousOn.div continuousOn_const (continuousOn_id.pow (k + 1))
    intro x hx
    rw [Set.uIcc_of_le hYT] at hx
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hY hx.1))
  have hInt : IntervalIntegrable
      (fun t : ℝ => (k : ℝ) * (C₀ * Y / d) * t ^ (r - k - 2)
        + (C₀ * Y ^ r / d) * ((k : ℝ) / t ^ (k + 1))) volume Y T :=
    hInt1.add hInt2
  -- Bounds for the two model integrals.
  have hA1 : ∫ t in Y..T, (k : ℝ) * (C₀ * Y / d) * t ^ (r - k - 2)
      ≤ (k : ℝ) * (C₀ * Y / d) * T ^ (r - k - 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    rw [show r - k - 2 + 1 = r - k - 1 by omega]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine le_trans (div_le_self ?_ ?_) ?_
    · have := pow_le_pow_left₀ (le_of_lt hY) hYT (r - k - 1)
      linarith
    · have : (0 : ℝ) ≤ ((r - k - 2 : ℕ) : ℝ) := by positivity
      linarith
    · linarith [show (0 : ℝ) ≤ Y ^ (r - k - 1) by positivity]
  have hA2 : ∫ t in Y..T, (C₀ * Y ^ r / d) * ((k : ℝ) / t ^ (k + 1))
      ≤ C₀ * (T ^ (r - k - 1) * Y) / d := by
    rw [intervalIntegral.integral_const_mul, integral_k_div_pow_aux k hk hY hYT]
    have hb : 1 / Y ^ k - 1 / T ^ k ≤ 1 / Y ^ k := by
      have : (0 : ℝ) ≤ 1 / T ^ k := by positivity
      linarith
    have hstep1 : (C₀ * Y ^ r / d) * (1 / Y ^ k - 1 / T ^ k)
        ≤ (C₀ * Y ^ r / d) * (1 / Y ^ k) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have hYpow3 : Y ^ r * (1 / Y ^ k) = Y ^ (r - k) := by
      rw [one_div, ← pow_sub₀ Y (ne_of_gt hY) hrk1]
    have hYrk : Y ^ (r - k) = Y ^ (r - k - 1) * Y := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hkey : Y ^ r * (1 / Y ^ k) ≤ T ^ (r - k - 1) * Y := by
      rw [hYpow3, hYrk]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt hY) hYT _) (le_of_lt hY)
    have hstep2 : (C₀ * Y ^ r / d) * (1 / Y ^ k) ≤ C₀ * (T ^ (r - k - 1) * Y) / d := by
      rw [show (C₀ * Y ^ r / d) * (1 / Y ^ k) = C₀ * (Y ^ r * (1 / Y ^ k)) / d by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hC₀) (le_of_lt hd)
    exact le_trans hstep1 hstep2
  have hfinal : (∫ t in Y..T, (k : ℝ) * (C₀ * Y / d) * t ^ (r - k - 2))
        + (∫ t in Y..T, (C₀ * Y ^ r / d) * ((k : ℝ) / t ^ (k + 1)))
      ≤ (C₀ * (k + 1)) * (T ^ (r - k - 1) * Y / d) := by
    have heq : (C₀ * (k + 1)) * (T ^ (r - k - 1) * Y / d)
        = (k : ℝ) * (C₀ * Y / d) * T ^ (r - k - 1) + C₀ * (T ^ (r - k - 1) * Y) / d := by
      ring
    rw [heq]
    linarith [hA1, hA2]
  calc |∫ t in Y..T, (k : ℝ) / t ^ (k + 1) * (e t - e Y)|
      ≤ ∫ t in Y..T, |(k : ℝ) / t ^ (k + 1) * (e t - e Y)| := by
        simpa only [Real.norm_eq_abs]
          using intervalIntegral.norm_integral_le_integral_norm (f := fun t =>
            (k : ℝ) / t ^ (k + 1) * (e t - e Y)) hYT
    _ ≤ ∫ t in Y..T, ((k : ℝ) * (C₀ * Y / d) * t ^ (r - k - 2)
          + (C₀ * Y ^ r / d) * ((k : ℝ) / t ^ (k + 1))) :=
        intervalIntegral.integral_mono_on hYT
          (by simpa only [Real.norm_eq_abs] using hi.norm) hInt hpt
    _ = (∫ t in Y..T, (k : ℝ) * (C₀ * Y / d) * t ^ (r - k - 2))
          + (∫ t in Y..T, (C₀ * Y ^ r / d) * ((k : ℝ) / t ^ (k + 1))) :=
        intervalIntegral.integral_add hInt1 hInt2
    _ ≤ (C₀ * (k + 1)) * (T ^ (r - k - 1) * Y / d) := hfinal

end Work.HP.BallConeK
