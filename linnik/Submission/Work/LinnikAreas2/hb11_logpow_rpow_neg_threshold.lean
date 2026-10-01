import Mathlib

set_option linter.unusedVariables false

namespace Work.LinnikAreas2

/-- For any real exponent `C` and any negative real exponent `s < 0`, the quantity
`(log q)^C * q^s` is eventually dominated by `K / log q`: the negative power of `q`
beats any power of the logarithm.  (The hypothesis `0 ≤ C` is not needed.) -/
theorem hb11_logpow_rpow_neg_threshold (C s : ℝ) (hC : 0 ≤ C) (hs : s < 0) :
    ∃ K : ℝ, 0 < K ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      (Real.log (q:ℝ))^C * (q:ℝ)^s ≤ K / Real.log (q:ℝ) := by
  set a := -s with ha
  have hapos : 0 < a := by rw [ha]; linarith
  have hs_eq : s = -a := by rw [ha]; ring
  -- `(log x)^(C+1) = o(x^a)` as `x → ∞`
  have hO : (fun x : ℝ => Real.log x ^ (C+1)) =o[Filter.atTop] (fun x : ℝ => x^a) :=
    isLittleO_log_rpow_rpow_atTop (C+1) hapos
  have htR : Filter.Tendsto (fun x : ℝ => Real.log x ^ (C+1) / x^a) Filter.atTop (nhds 0) :=
    hO.tendsto_div_nhds_zero
  -- restrict the real limit to natural arguments
  have ht : Filter.Tendsto (fun q : ℕ => Real.log (q:ℝ) ^ (C+1) / (q:ℝ)^a)
      Filter.atTop (nhds 0) :=
    htR.comp tendsto_natCast_atTop_atTop
  have hratio : ∀ᶠ q : ℕ in Filter.atTop, Real.log (q:ℝ) ^ (C+1) / (q:ℝ)^a < 1 :=
    ht.eventually (Iio_mem_nhds zero_lt_one)
  -- for large `q`, `(log q)^C * q^s ≤ 1 / log q`
  have hev : ∀ᶠ q : ℕ in Filter.atTop,
      (Real.log (q:ℝ))^C * (q:ℝ)^s ≤ 1 / Real.log (q:ℝ) := by
    filter_upwards [hratio, Filter.eventually_ge_atTop 2] with q hq hq2
    have hqge : (2:ℝ) ≤ q := by exact_mod_cast hq2
    have hqpos : (0:ℝ) < (q:ℝ) := by linarith
    have hlogpos : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith)
    have hqapos : 0 < (q:ℝ)^a := Real.rpow_pos_of_pos hqpos a
    have h1 : Real.log (q:ℝ)^(C+1) < (q:ℝ)^a := (div_lt_one hqapos).1 hq
    have hle1 : (Real.log (q:ℝ))^(C+1) * (q:ℝ)^s ≤ 1 := by
      have hqinv : (0:ℝ) < ((q:ℝ)^a)⁻¹ := inv_pos.mpr hqapos
      have h2 : Real.log (q:ℝ)^(C+1) * ((q:ℝ)^a)⁻¹ < (q:ℝ)^a * ((q:ℝ)^a)⁻¹ :=
        mul_lt_mul_of_pos_right h1 hqinv
      rw [mul_inv_cancel₀ hqapos.ne'] at h2
      calc (Real.log (q:ℝ))^(C+1) * (q:ℝ)^s
          = Real.log (q:ℝ)^(C+1) * (q:ℝ)^(-a) := by rw [hs_eq]
        _ = Real.log (q:ℝ)^(C+1) * ((q:ℝ)^a)⁻¹ := by rw [Real.rpow_neg hqpos.le a]
        _ ≤ 1 := le_of_lt h2
    have hmul : (Real.log (q:ℝ))^C * (q:ℝ)^s * Real.log (q:ℝ) ≤ 1 := by
      rw [show (Real.log (q:ℝ))^C * (q:ℝ)^s * Real.log (q:ℝ)
            = (Real.log (q:ℝ))^(C+1) * (q:ℝ)^s by
            rw [Real.rpow_add hlogpos C 1, Real.rpow_one]; ring]
      exact hle1
    exact (le_div_iff₀ hlogpos).2 hmul
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hev
  exact ⟨1, one_pos, Q, fun q hq => hQ q hq⟩

end Work.LinnikAreas2
