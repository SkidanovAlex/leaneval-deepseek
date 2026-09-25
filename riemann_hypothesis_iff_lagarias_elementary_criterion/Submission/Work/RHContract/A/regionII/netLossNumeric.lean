import Mathlib

/-!
# Region II: the net-loss numeric inequality

We prove that for `s ≥ 316.2`, `L ≥ 11.5`, `M ∈ [s-4, s-3]`, `B ∈ [1/(L+0.006329), 1/L]`
and `γ ∈ [0.9015/(L+0.0941), 1/((9/10)(L-0.105361))]`,

`(√B − (M/s)·√γ)^2 ≤ 0.0045 / L`.

The heuristic is that `M/s ≈ 1`, `√B ≈ 1/√L` and `√γ ≈ 1/√(0.9 L)`, so
`√B − (M/s)·√γ ≈ (1 − 1/√0.9)/√L`; squaring gives `≈ 0.00293/L`.  The extremal case is
`M/s` as small as possible (`s = 316.2`, `M = s-4`), `B = 1/L`, `γ` as small as possible and
`L = 11.5`, where the value is `≈ 0.004412/L < 0.0045/L`.

The two directions `√B − (M/s)√γ` and `(M/s)√γ − √B` are bounded separately by the corner
values of the rectangles in which `√B` and `(M/s)√γ` live, and each is shown to be
`≤ (67/1000)/√L`.  Since `(67/1000)^2 = 4489/10^6 < 4500/10^6 = 0.0045` the claim follows.
-/

namespace Work.RHContract.A.regionII

/-- Lower bound on `(1561/1581)·√(0.9015/(L+0.0941))`, used for the direction
`√B − (M/s)√γ`: the multiplier `1561/1581 = (316.2−4)/316.2` is the smallest possible value
of `M/s`, and `0.9015/(L+0.0941)` is the smallest possible value of `γ`. -/
lemma keyBoundA (L : ℝ) (hL : (115/10:ℝ) ≤ L) :
    (933/1000 : ℝ) / Real.sqrt L ≤ (1561/1581) * Real.sqrt (9015/10000 / (L + 941/10000)) := by
  have step1 : (9456/10000 : ℝ) / Real.sqrt L ≤ Real.sqrt (9015/10000 / (L + 941/10000)) := by
    have hLc : 0 < L + 941/10000 := by linarith
    have key : (9456/10000:ℝ)^2 / L ≤ 9015/10000 / (L + 941/10000) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hL]
    have hsqrt : Real.sqrt ((9456/10000:ℝ)^2 / L) ≤ Real.sqrt (9015/10000 / (L + 941/10000)) :=
      Real.sqrt_le_sqrt key
    rwa [Real.sqrt_div (sq_nonneg _) L, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9456/10000)] at hsqrt
  have h2 := mul_le_mul_of_nonneg_left step1 (by norm_num : (0:ℝ) ≤ 1561/1581)
  have h3 : (1561/1581 : ℝ) * (9456/10000 / Real.sqrt L) = ((1561/1581)*(9456/10000)) / Real.sqrt L := by ring
  have h4 : (933/1000 : ℝ) / Real.sqrt L ≤ ((1561/1581)*(9456/10000)) / Real.sqrt L := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg L)
    norm_num
  calc (933/1000 : ℝ) / Real.sqrt L
      ≤ ((1561/1581)*(9456/10000)) / Real.sqrt L := h4
    _ = (1561/1581) * (9456/10000 / Real.sqrt L) := h3.symm
    _ ≤ (1561/1581) * Real.sqrt (9015/10000 / (L + 941/10000)) := h2

/-- Upper bound on `1/√(0.9(L−0.105361)) − 1/√(L+0.006329)`, used for the direction
`(M/s)√γ − √B`.  The first factor is at most `(1059/1000)/√L` and the second at least
`(999/1000)/√L`, whence the difference is at most `(60/1000)/√L ≤ (67/1000)/√L`. -/
lemma keyBoundB (L : ℝ) (hL : (115/10:ℝ) ≤ L) :
    1 / Real.sqrt (9/10 * (L - 105361/1000000)) - 1/Real.sqrt (L + 6329/1000000)
      ≤ (67/1000)/Real.sqrt L := by
  have hT1 : 1 / Real.sqrt (9/10 * (L - 105361/1000000)) ≤ (1059/1000)/Real.sqrt L := by
    have hD : 0 < 9/10 * (L - 105361/1000000) := by
      apply mul_pos (by norm_num); linarith
    rw [one_div, ← Real.sqrt_inv]
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ L)]
    rw [inv_le_iff_one_le_mul₀ hD]
    field_simp
    nlinarith [hL]
  have hT2 : (999/1000)/Real.sqrt L ≤ 1/Real.sqrt (L + 6329/1000000) := by
    have hc : 0 < L + 6329/1000000 := by linarith
    rw [one_div, ← Real.sqrt_inv]
    rw [Real.le_sqrt (by positivity) (inv_nonneg.mpr hc.le)]
    rw [div_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ L)]
    rw [← one_div]
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < L) hc]
    norm_num
    nlinarith [hL]
  have key : 1 / Real.sqrt (9/10 * (L - 105361/1000000)) - 1/Real.sqrt (L + 6329/1000000)
      ≤ (1059/1000)/Real.sqrt L - (999/1000)/Real.sqrt L := by linarith
  have hsum : (1059/1000)/Real.sqrt L - (999/1000)/Real.sqrt L = (60/1000)/Real.sqrt L := by ring
  rw [hsum] at key
  have : (60/1000 : ℝ)/Real.sqrt L ≤ (67/1000)/Real.sqrt L := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg L); norm_num
  linarith

theorem netLossNumeric (s L B γ M : ℝ)
    (hs : (316.2 : ℝ) ≤ s) (hL : (115 / 10 : ℝ) ≤ L)
    (hMlo : s - 4 ≤ M) (hMhi : M ≤ s - 3)
    (hBlo : 1 / (L + 6329 / 1000000) ≤ B) (hBhi : B ≤ 1 / L)
    (hglo : (9015 : ℝ) / 10000 / (L + 941 / 10000) ≤ γ)
    (hghi : γ ≤ 1 / ((9 / 10 : ℝ) * (L - 105361 / 1000000))) :
    (Real.sqrt B - M / s * Real.sqrt γ) ^ 2 ≤ (45 : ℝ) / 10000 / L := by
  have hs_pos : 0 < s := by linarith [hs]
  have hL_pos : 0 < L := by linarith [hL]
  -- √B lives in `[1/√(L+0.006329), 1/√L]`
  have hsqrtB_upper : Real.sqrt B ≤ 1/Real.sqrt L := by
    rw [one_div, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    simpa [one_div] using hBhi
  have hsqrtB_lower : 1/Real.sqrt (L + 6329/1000000) ≤ Real.sqrt B := by
    rw [one_div, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    simpa [one_div] using hBlo
  -- √γ lives in `[√(0.9015/(L+0.0941)), 1/√(0.9(L−0.105361))]`
  have hsqrtγ_lower : Real.sqrt (9015/10000/(L+941/10000)) ≤ Real.sqrt γ :=
    Real.sqrt_le_sqrt hglo
  have hsqrtγ_upper : Real.sqrt γ ≤ 1/Real.sqrt (9/10 * (L - 105361/1000000)) := by
    have h : Real.sqrt γ ≤ Real.sqrt ((9/10 * (L - 105361/1000000))⁻¹) :=
      Real.sqrt_le_sqrt (by simpa [one_div] using hghi)
    rw [Real.sqrt_inv] at h
    simpa [one_div] using h
  -- `M/s ∈ [1561/1581, 1]`
  have hr_lo : (1561/1581 : ℝ) ≤ M/s := by
    rw [le_div_iff₀ hs_pos]; nlinarith [hs, hMlo]
  have hr_hi : M/s ≤ 1 := by
    rw [div_le_one hs_pos]; linarith [hMhi]
  -- the two corner estimates
  have hxy : Real.sqrt B - M/s*Real.sqrt γ ≤ (67/1000)/Real.sqrt L := by
    have h1 : (1561/1581) * Real.sqrt (9015/10000/(L+941/10000)) ≤ M/s*Real.sqrt γ :=
      mul_le_mul hr_lo hsqrtγ_lower (Real.sqrt_nonneg _) (le_trans (by norm_num) hr_lo)
    have h2 := keyBoundA L hL
    have h3 : Real.sqrt B - M/s*Real.sqrt γ
        ≤ 1/Real.sqrt L - (1561/1581)*Real.sqrt (9015/10000/(L+941/10000)) := by
      linarith [hsqrtB_upper, h1]
    have h4 : (1:ℝ)/Real.sqrt L - (1561/1581)*Real.sqrt (9015/10000/(L+941/10000))
        ≤ 1/Real.sqrt L - (933/1000)/Real.sqrt L := by linarith [h2]
    have h5 : (1:ℝ)/Real.sqrt L - (933/1000)/Real.sqrt L = (67/1000)/Real.sqrt L := by ring
    linarith [h3, h4, h5]
  have hyx : M/s*Real.sqrt γ - Real.sqrt B ≤ (67/1000)/Real.sqrt L := by
    have h1 : M/s*Real.sqrt γ ≤ Real.sqrt γ := by
      have := mul_le_mul_of_nonneg_right hr_hi (Real.sqrt_nonneg γ); simpa using this
    have h4 := keyBoundB L hL
    linarith [h1, hsqrtγ_upper, hsqrtB_lower, h4]
  have hsq : (Real.sqrt B - M/s*Real.sqrt γ)^2 ≤ ((67/1000)/Real.sqrt L)^2 :=
    sq_le_sq' (by linarith [hyx]) hxy
  calc (Real.sqrt B - M / s * Real.sqrt γ)^2
      ≤ ((67/1000)/Real.sqrt L)^2 := hsq
    _ ≤ 45/10000/L := by
        rw [div_pow, Real.sq_sqrt (le_of_lt hL_pos)]
        rw [div_le_div_iff₀ hL_pos hL_pos]
        nlinarith [hL_pos]

end Work.RHContract.A.regionII
