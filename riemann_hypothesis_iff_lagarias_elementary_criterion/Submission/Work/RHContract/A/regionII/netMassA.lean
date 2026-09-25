import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs

namespace Work.RHContract.A.regionII

open scoped BigOperators

set_option maxHeartbeats 1000000

noncomputable section

/-- Arithmetic core for `netMassA`.  Writing
`α' = 26421/100000 − (49013/100000)/11.5 − (196189/100000)/17.782` and
`c₀ = 1488/10000 − (483906/1000000)/11.5`, we have `(α' s − 1)(s−4)/s² ≥ c₀`
for every `s ≥ 316.2`.  The quadratic `(α'−c₀)s² − (4α'+1)s + 4` is increasing on
`[316.2, ∞)` and positive at `316.2`. -/
lemma netMassA_arith {s : ℝ} (hs : (316.2 : ℝ) ≤ s) :
    (1488/10000 - 483906/1000000/11.5 : ℝ)
      ≤ ((26421/100000 - 49013/100000/11.5 - 196189/100000/17.782) * s - 1)
          * (s - 4) / s ^ 2 := by
  have hs0 : (0 : ℝ) < s := by linarith
  set a' : ℝ := 26421/100000 - 49013/100000/11.5 - 196189/100000/17.782 with ha'
  set c0 : ℝ := 1488/10000 - 483906/1000000/11.5 with hc0
  have h1 : 0 < a' - c0 := by rw [ha', hc0]; norm_num
  have h2 : 0 ≤ (a' - c0) * (2 * 316.2) - (4 * a' + 1) := by rw [ha', hc0]; norm_num
  have h3 : 0 ≤ (a' - c0) * 316.2 ^ 2 - (4 * a' + 1) * 316.2 + 4 := by
    rw [ha', hc0]; norm_num
  have hmain : (0 : ℝ) ≤ (a' - c0) * s ^ 2 - (4 * a' + 1) * s + 4 := by
    have hid2 : (a' - c0) * s ^ 2 - (4 * a' + 1) * s + 4
        = ((a' - c0) * 316.2 ^ 2 - (4 * a' + 1) * 316.2 + 4)
          + (s - 316.2) * ((a' - c0) * (s + 316.2) - (4 * a' + 1)) := by ring
    have hbr : 0 ≤ (a' - c0) * (s + 316.2) - (4 * a' + 1) := by
      have hm := mul_le_mul_of_nonneg_left
        (show (2 * 316.2 : ℝ) ≤ s + 316.2 by linarith) (le_of_lt h1)
      linarith [hm, h2]
    have hprod : 0 ≤ (s - 316.2) * ((a' - c0) * (s + 316.2) - (4 * a' + 1)) :=
      mul_nonneg (by linarith) hbr
    rw [hid2]
    exact add_nonneg h3 hprod
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < s ^ 2)]
  nlinarith [hmain]

theorem netMassA (s L : ℝ) (hs : (316.2 : ℝ) ≤ s) (hL : (11.5 : ℝ) ≤ L) :
    netNuA L ≤ netMasslb s L * (s - 4) / s ^ 2 := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hLne : L ≠ 0 := ne_of_gt hL0
  -- Decompose the difference as a constant-in-`L` part plus a monotone correction.
  have hid : netMasslb s L * (s - 4) / s ^ 2 - netNuA L
      = (netMasslb s (11.5) * (s - 4) / s ^ 2 - netNuA (11.5))
        + (1/11.5 - 1/L) * (49013/100000 * (s - 4) / s - 483906/1000000) := by
    simp only [netMasslb, netNuA]
    field_simp
    ring
  -- The constant part is nonnegative.
  have hpart1 : 0 ≤ netMasslb s (11.5) * (s - 4) / s ^ 2 - netNuA (11.5) := by
    simp only [netMasslb, netNuA]
    rw [sub_nonneg]
    have hs17 : (17.782 : ℝ) ≤ Real.sqrt s := by
      have h : (17.782 : ℝ) ^ 2 ≤ s := by nlinarith [hs]
      have h2 := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 17.782)] at h2
    have hrootpos : (0 : ℝ) < Real.sqrt s := by linarith
    have hsq : Real.sqrt s ≤ s / 17.782 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 17.782)]
      have hss : s = Real.sqrt s * Real.sqrt s := by
        rw [← pow_two, Real.sq_sqrt (le_of_lt hs0)]
      nlinarith [hs17, hss, hrootpos]
    have hC : 196189/100000 * Real.sqrt s ≤ 196189/100000 * (s/17.782) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    have hstep : (26421/100000 - 49013/100000/11.5 - 196189/100000/17.782) * s - 1
        ≤ 26421/100000 * s - 49013/100000 * s / 11.5 - 1
            - 196189/100000 * Real.sqrt s := by
      have hA : (26421/100000 - 49013/100000/11.5 - 196189/100000/17.782) * s - 1
          = 26421/100000 * s - 49013/100000 * s / 11.5 - 1
            - (196189/100000/17.782) * s := by ring
      have hC' : (196189/100000/17.782) * s = 196189/100000 * (s/17.782) := by ring
      rw [hA, hC']
      linarith [hC]
    have hkey : (1488/10000 - 483906/1000000/11.5 : ℝ)
        ≤ (26421/100000 * s - 49013/100000 * s / 11.5 - 1
            - 196189/100000 * Real.sqrt s) * (s - 4) / s ^ 2 := by
      calc (1488/10000 - 483906/1000000/11.5 : ℝ)
          ≤ ((26421/100000 - 49013/100000/11.5 - 196189/100000/17.782) * s - 1)
              * (s - 4) / s ^ 2 := netMassA_arith hs
        _ ≤ (26421/100000 * s - 49013/100000 * s / 11.5 - 1
              - 196189/100000 * Real.sqrt s) * (s - 4) / s ^ 2 := by
            apply div_le_div_of_nonneg_right _ (sq_nonneg s)
            exact mul_le_mul_of_nonneg_right hstep (by linarith)
    exact hkey
  -- The correction is nonnegative.
  have hpart2 :
      0 ≤ (1/11.5 - 1/L) * (49013/100000 * (s - 4) / s - 483906/1000000) := by
    apply mul_nonneg
    · rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by norm_num) hL
    · rw [sub_nonneg, le_div_iff₀ hs0]
      nlinarith [hs]
  have hS : 0 ≤ netMasslb s L * (s - 4) / s ^ 2 - netNuA L := by
    rw [hid]; linarith [hpart1, hpart2]
  linarith

end

end Work.RHContract.A.regionII
