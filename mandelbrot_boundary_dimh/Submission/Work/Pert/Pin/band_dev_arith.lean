import Mathlib

namespace Work.Pert.Pin

/-- The two numerical hypotheses `hdevcov`, `hdevR` of `Work.Pert.Pin.band_goodP_sqrt_im`, as a
standalone real-arithmetic lemma (`E = 1/M²`, `M = s²`, `R ≥ K₀/(2s)`, `K₀ = 40000·Camp·Cseed·Cdev`).
Elementary estimates: `3Xdev + 1 + Tb ≤ 5s`, `Cdev·80/M + 4E ≤ 400·Cdev/s + 20/s³`, `s ≥ 1000`,
`Cdev ≤ s`; for the second conjunct `Cseed·2·420·Cdev/s = 840·Cseed·Cdev/s ≤ (5000/3)·Cseed·Cdev/s =
K₀/(24·Camp·s) ≤ R/(12·Camp)` using `840 ≤ 5000/3`. -/
theorem band_dev_arith {M s Xdev Tb Cdev Cseed Camp K₀ R E : ℝ}
    (hspos : 0 < s) (hs1 : 1 ≤ s) (hs1000 : 1000 ≤ s) (hMpos : 0 < M) (hM : M = s * s)
    (hX : Xdev ≤ s) (hTb : Tb = s) (hCd0 : 0 ≤ Cdev) (hCd1 : 1 ≤ Cdev) (hCd : Cdev ≤ s)
    (hCseedpos : 0 < Cseed) (hCamp1 : 1 ≤ Camp)
    (hK₀ : K₀ = 40000 * (Camp * Cseed * Cdev)) (hR : K₀ / (2 * s) ≤ R) (hE : E = 1 / M ^ 2) :
    (3 / 2) * Xdev + (Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb) < M / 32 ∧
      Cseed * (2 * ((Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb)) / (M * M))
        ≤ R / (12 * Camp * M * M) := by
  subst hM
  rw [hE]
  have hsspos : (0:ℝ) < s*s := mul_pos hspos hspos
  have hssnn : (0:ℝ) ≤ s*s := le_of_lt hsspos
  have hCdevpos : (0:ℝ) < Cdev := lt_of_lt_of_le zero_lt_one hCd1
  have hCamp0 : (0:ℝ) < Camp := lt_of_lt_of_le zero_lt_one hCamp1
  -- `3Xdev + 1 + Tb ≤ 5s`
  have hQle : 3*Xdev + 1 + Tb ≤ 5*s := by
    rw [hTb]; nlinarith [hX, hs1]
  -- the first factor is nonnegative
  have hPnn : (0:ℝ) ≤ Cdev*80/(s*s) + 4*(1/(s*s)^2) := by
    apply add_nonneg
    · exact div_nonneg (by positivity) hssnn
    · positivity
  -- `(Cdev*80/M + 4E) * (3Xdev + 1 + Tb) ≤ 400*Cdev/s + 20/s^3`
  have hκ1 : (Cdev*80/(s*s) + 4*(1/(s*s)^2))*(3*Xdev+1+Tb) ≤ 400*Cdev/s + 20/s^3 := by
    have hstep1 := mul_le_mul_of_nonneg_left hQle hPnn
    have hstep2 : (Cdev*80/(s*s) + 4*(1/(s*s)^2))*(5*s) = 400*Cdev/s + 20/s^3 := by
      field_simp
      ring
    linarith [hstep1, hstep2.le, hstep2.ge]
  -- the sharper estimate `… ≤ 420*Cdev/s`
  have hκ2 : (Cdev*80/(s*s) + 4*(1/(s*s)^2))*(3*Xdev+1+Tb) ≤ 420*Cdev/s := by
    have h2 : 20/s^3 ≤ 20/s := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < s^3) hspos]
      nlinarith [hs1000, hspos, sq_nonneg s]
    have h3 : 20/s ≤ 20*Cdev/s := by
      rw [div_le_div_iff₀ hspos hspos]; nlinarith [hCd1, hspos]
    have hA : 20/s^3 ≤ 20*Cdev/s := le_trans h2 h3
    have heq : (400:ℝ)*Cdev/s + 20*Cdev/s = 420*Cdev/s := by ring
    have h1 : 400*Cdev/s + 20/s^3 ≤ 420*Cdev/s := by linarith [hA, heq.le, heq.ge]
    exact le_trans hκ1 h1
  refine ⟨?_, ?_⟩
  · -- first conjunct
    have h1 : 400*Cdev/s + 20/s^3 ≤ 400 + 20 := by
      have h1a : 400*Cdev/s ≤ 400 := by
        rw [div_le_iff₀ hspos]; linarith [hCd]
      have h1b : 20/s^3 ≤ 20 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < s^3)]
        nlinarith [hs1000, hspos]
      linarith [h1a, h1b]
    have h2 : (3/2)*Xdev ≤ (3/2)*s := by linarith [hX]
    nlinarith [hκ1, h1, h2, hs1000, hspos, sq_nonneg s]
  · -- second conjunct
    have hstep : Cseed*(2*((Cdev*80/(s*s) + 4*(1/(s*s)^2))*(3*Xdev+1+Tb)))
        ≤ 840*Cseed*Cdev/s := by
      have h1 : 2*((Cdev*80/(s*s) + 4*(1/(s*s)^2))*(3*Xdev+1+Tb)) ≤ 2*(420*Cdev/s) := by
        linarith [hκ2]
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hCseedpos)
      have h3 : Cseed*(2*(420*Cdev/s)) = 840*Cseed*Cdev/s := by ring
      linarith [h2, h3.le, h3.ge]
    have hRHS : 840*Cseed*Cdev/s ≤ R/(12*Camp) := by
      have h1 : K₀/(24*Camp*s) ≤ R/(12*Camp) := by
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 24*Camp*s) (by positivity : (0:ℝ) < 12*Camp)]
        have hR2 : K₀ ≤ R*(2*s) := by
          have hh := (div_le_iff₀ (by positivity : (0:ℝ) < 2*s)).mp hR
          linarith [hh]
        nlinarith [hR2, hCamp0, hspos]
      have h2 : K₀/(24*Camp*s) = 5000*Cseed*Cdev/(3*s) := by
        rw [hK₀]; field_simp; ring
      have h3 : 840*Cseed*Cdev/s ≤ 5000*Cseed*Cdev/(3*s) := by
        rw [div_le_div_iff₀ hspos (by positivity : (0:ℝ) < 3*s)]
        have hpos : (0:ℝ) ≤ Cseed*Cdev*s := by positivity
        have e1 : 840*Cseed*Cdev*(3*s) = 2520*(Cseed*Cdev*s) := by ring
        have e2 : 5000*Cseed*Cdev*s = 5000*(Cseed*Cdev*s) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right (by norm_num : (2520:ℝ) ≤ 5000) hpos
      linarith [h1, h2.le, h2.ge, h3]
    have hmain : Cseed*(2*((Cdev*80/(s*s) + 4*(1/(s*s)^2))*(3*Xdev+1+Tb))) ≤ R/(12*Camp) :=
      le_trans hstep hRHS
    rw [show Cseed*(2*((Cdev*80/(s*s) + 4*(1/(s*s)^2))*(3*Xdev+1+Tb))/((s*s)*(s*s)))
          = Cseed*(2*((Cdev*80/(s*s) + 4*(1/(s*s)^2))*(3*Xdev+1+Tb)))/((s*s)*(s*s)) by ring]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (s*s)*(s*s))
      (by positivity : (0:ℝ) < 12*Camp*(s*s)*(s*s))]
    have h2 : Cseed*(2*((Cdev*80/(s*s) + 4*(1/(s*s)^2))*(3*Xdev+1+Tb))) * (12*Camp*(s*s)*(s*s))
        ≤ (R/(12*Camp)) * (12*Camp*(s*s)*(s*s)) :=
      mul_le_mul_of_nonneg_right hmain (by positivity)
    have h3 : (R/(12*Camp))*(12*Camp*(s*s)*(s*s)) = R*((s*s)*(s*s)) := by field_simp
    linarith [h2, h3.le, h3.ge]

end Work.Pert.Pin
