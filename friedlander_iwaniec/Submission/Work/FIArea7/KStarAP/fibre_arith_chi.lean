import Mathlib

namespace Work.FIArea7.KStarAP

/-- Elementary arithmetic inequality used to compare the two sides: for `τ > 0` and
`K, L ≥ 0`, we have `√τ * (1 + 2KL/τ) ≤ 2(K+1) * (√τ + L/√τ)`. -/
private lemma sqrt_mul_one_add_le (τ K L : ℝ) (hτ : 0 < τ) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    Real.sqrt τ * (1 + 2*K*L/τ) ≤ 2*(K+1)*(Real.sqrt τ + L/Real.sqrt τ) := by
  have hr : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h1 : (Real.sqrt τ) * (Real.sqrt τ) = τ := Real.mul_self_sqrt hτ.le
  rw [← mul_le_mul_iff_left₀ hr]
  have eL : Real.sqrt τ * (1 + 2*K*L/τ) * Real.sqrt τ = τ + 2*K*L := by
    field_simp
    ring_nf
    nlinarith [h1]
  have eR : 2*(K+1)*(Real.sqrt τ + L/Real.sqrt τ) * Real.sqrt τ = 2*(K+1)*(τ + L) := by
    field_simp
    ring_nf
    nlinarith [h1]
  rw [eL, eR]
  nlinarith [hK, hL, mul_nonneg hK hτ.le]

lemma fibre_arith_chi (C0 : ℝ) (hC0 : 0 < C0) (d : ℕ) (hd : 1 ≤ d) (k : ℤ)
    (τ q M L W W'' G : ℝ) (hτ : 0 < τ) (hq : 0 ≤ q) (hM : 0 < M) (hL : 0 ≤ L)
    (hW : 0 ≤ W) (hG : 0 < G) (hW'' : 0 < W'') (hle : W ≤ W'') :
    C0 * (W / G) * Real.sqrt (τ * q / M) * (2 * Real.log (2 + τ * q))
        * (2 * (d : ℝ) * G / W'' * (1 + 2 * |(k : ℝ)| * L / τ))
      ≤ 8 * C0 * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (q / M)
          * (Real.sqrt τ + L / Real.sqrt τ) * Real.log (2 + τ * q) := by
  have hK : 0 ≤ |(k : ℝ)| := abs_nonneg _
  have hτq : 0 ≤ τ * q := mul_nonneg hτ.le hq
  have hlog : 0 ≤ Real.log (2 + τ * q) := Real.log_nonneg (by linarith)
  have hsq : Real.sqrt (τ * q / M) = Real.sqrt τ * Real.sqrt (q / M) := by
    have h : τ * q / M = τ * (q / M) := by ring
    rw [h, Real.sqrt_mul (le_of_lt hτ)]
  rw [hsq]
  have eq1 : C0 * (W / G) * (Real.sqrt τ * Real.sqrt (q / M)) * (2 * Real.log (2 + τ * q))
        * (2 * (d : ℝ) * G / W'' * (1 + 2 * |(k : ℝ)| * L / τ))
      = (4 * C0 * (d : ℝ) * Real.sqrt (q / M) * Real.log (2 + τ * q))
          * ((W / W'') * Real.sqrt τ * (1 + 2 * |(k : ℝ)| * L / τ)) := by
    field_simp
    ring
  have eq2 : 8 * C0 * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (q / M)
          * (Real.sqrt τ + L / Real.sqrt τ) * Real.log (2 + τ * q)
      = (4 * C0 * (d : ℝ) * Real.sqrt (q / M) * Real.log (2 + τ * q))
          * (2 * (|(k : ℝ)| + 1) * (Real.sqrt τ + L / Real.sqrt τ)) := by
    ring
  rw [eq1, eq2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hP : (W / W'') ≤ 1 := (div_le_one hW'').mpr hle
  have hXnn : 0 ≤ Real.sqrt τ * (1 + 2 * |(k : ℝ)| * L / τ) := by positivity
  calc (W / W'') * Real.sqrt τ * (1 + 2 * |(k : ℝ)| * L / τ)
      = (W / W'') * (Real.sqrt τ * (1 + 2 * |(k : ℝ)| * L / τ)) := by ring
    _ ≤ 1 * (Real.sqrt τ * (1 + 2 * |(k : ℝ)| * L / τ)) :=
          mul_le_mul_of_nonneg_right hP hXnn
    _ = Real.sqrt τ * (1 + 2 * |(k : ℝ)| * L / τ) := by ring
    _ ≤ 2 * (|(k : ℝ)| + 1) * (Real.sqrt τ + L / Real.sqrt τ) :=
          sqrt_mul_one_add_le τ _ L hτ hK hL

end Work.FIArea7.KStarAP
