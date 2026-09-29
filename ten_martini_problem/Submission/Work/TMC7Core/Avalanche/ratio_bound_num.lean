import Mathlib

/-!
# `ratio_bound_num`

Numerical core for the avalanche-step norm estimate.
-/

set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false

namespace Work.TMC7Core.Avalanche

/-- `217/(225μ) ≤ 1/μ - 2/(μ²-1)²` for `μ ≥ 4`, i.e. the lower endpoint for `lam²`. -/
private lemma beta_lower (μ : ℝ) (hμ : 4 ≤ μ) :
    217 / (225 * μ) ≤ 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
  have hμpos : (0:ℝ) < μ := by linarith
  have hq : (0:ℝ) < μ^2 - 1 := by nlinarith
  have hkey : 225*μ ≤ 4*(μ^2-1)^2 := by
    have hfac : 4*(μ^2-1)^2 - 225*μ = (μ-4)*(4*μ^3+16*μ^2+56*μ-1) := by ring
    have h1 : (0:ℝ) ≤ μ - 4 := by linarith
    have h2 : (0:ℝ) ≤ 4*μ^3+16*μ^2+56*μ-1 := by
      nlinarith [hμ, sq_nonneg (μ-4), pow_nonneg (by linarith : (0:ℝ) ≤ μ) 3]
    nlinarith [hfac, mul_nonneg h1 h2]
  have h1 : 2/(μ^2-1)^2 ≤ 8/(225*μ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey]
  have h2 : 1/μ - 2/(μ^2-1)^2 ≥ 1/μ - 8/(225*μ) := by linarith
  have h3 : (1:ℝ)/μ - 8/(225*μ) = 217/(225*μ) := by field_simp <;> ring
  linarith [h1, h2, h3]

/-- Upper numerical bound: `(1 + 51/(25μ))² + (25/16)·225μ/(217(μ²-1)) ≤ 1 + 25/μ`. -/
private lemma up_num (μ : ℝ) (hμ : 4 ≤ μ) :
    (1 + 51/(25*μ))^2 + (25/16) * ((225*μ)/(217*(μ^2-1))) ≤ 1 + 25/μ := by
  have hμpos : (0:ℝ) < μ := by linarith
  have hq : (0:ℝ) < μ^2 - 1 := by nlinarith
  field_simp
  nlinarith [hμ, sq_nonneg (μ-4)]

/-- Lower numerical bound: `(1 + 4/μ³)/(1 - 51/(25μ))² ≤ 1 + 25/μ`. -/
private lemma lo_num (μ : ℝ) (hμ : 4 ≤ μ) :
    (1 + 4/μ^3)/(1 - 51/(25*μ))^2 ≤ 1 + 25/μ := by
  have hμpos : (0:ℝ) < μ := by linarith
  have hd2 : (0:ℝ) < 25*μ - 51 := by nlinarith
  have hden : (1:ℝ) - 51/(25*μ) = (25*μ-51)/(25*μ) := by field_simp
  rw [hden, div_pow]
  rw [show (1:ℝ) + 25/μ = (μ+25)/μ by field_simp]
  rw [div_le_div_iff₀ (by positivity) hμpos]
  field_simp
  nlinarith [hμ, sq_nonneg (μ-4)]

lemma ratio_bound_num (μ s lam rho A B A' B' : ℝ) (hμ : 4 ≤ μ)
    (hs : 1 ≤ s) (hs2 : μ ^ 2 - 1 ≤ s ^ 2)
    (hlam0 : 0 ≤ lam) (hrho : 0 ≤ rho)
    (hL : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 ≤ lam ^ 2)
    (hlr : lam ^ 2 + rho ^ 2 = 1) (hA : 0 < A) (hB0 : 0 ≤ B)
    (hB'0 : 0 ≤ B')
    (hu : B ≤ (2 / (μ * Real.sqrt μ)) * A)
    (hA'le : A' ≤ s * (lam * A + rho * B)) (hA'ge : s * (lam * A - rho * B) ≤ A')
    (hB'le : B' ≤ s⁻¹ * (rho * A + lam * B)) :
    |Real.log ((A' ^ 2 + B' ^ 2) / (s ^ 2 * lam ^ 2 * (A ^ 2 + B ^ 2)))| ≤ 30 / μ := by
  have hμpos : (0:ℝ) < μ := by linarith
  have hq : (0:ℝ) < μ^2 - 1 := by nlinarith
  have hs_pos : (0:ℝ) < s := by linarith
  have hs2pos : (0:ℝ) < s^2 := by positivity
  have hlam2_ge : 217/(225*μ) ≤ lam^2 := le_trans (beta_lower μ hμ) hL
  have hlam2pos : (0:ℝ) < lam^2 := lt_of_lt_of_le (by positivity) hlam2_ge
  have hlam_pos : (0:ℝ) < lam := by nlinarith only [hlam0, hlam2pos]
  have hlam_le_one : lam ≤ 1 := by
    have h : lam^2 ≤ 1 := by nlinarith only [sq_nonneg rho, hlr]
    nlinarith only [hlam0, h]
  have hrho_le_one : rho ≤ 1 := by
    have h : rho^2 ≤ 1 := by nlinarith only [sq_nonneg lam, hlr]
    nlinarith only [hrho, h]
  set x : ℝ := B / A with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hB_eq : B = x * A := by rw [hxdef]; field_simp
  have hx_le : x ≤ 2/(μ*Real.sqrt μ) := by rw [hxdef, div_le_iff₀ hA]; exact hu
  have heta : (2/(μ*Real.sqrt μ))^2 = 4/μ^3 := by
    rw [div_pow, mul_pow]
    have : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt (le_of_lt hμpos)
    rw [this]; ring
  have hx2 : x^2 ≤ 4/μ^3 := by
    have h := pow_le_pow_left₀ hx0 hx_le 2
    rw [heta] at h; exact h
  have hμ3 : (64:ℝ) ≤ μ^3 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hμ 3
    norm_num at this ⊢; exact this
  have hx_quarter : x ≤ 1/4 := by
    have h1 : x^2 ≤ (1/4)^2 := by
      calc x^2 ≤ 4/μ^3 := hx2
        _ ≤ (1/4)^2 := by rw [div_le_iff₀ (by positivity : (0:ℝ) < μ^3)]; nlinarith only [hμ3]
    nlinarith only [hx0, h1]
  have hμsq : (16:ℝ) ≤ μ^2 := by nlinarith only [hμ]
  have hx_lt_lam : x < lam := by
    have h1 : 4/μ^3 < 217/(225*μ) := by
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < μ^3) (by positivity : (0:ℝ) < 225*μ)]
      nlinarith only [hμsq, hμpos]
    have h2 : x^2 < lam^2 := lt_of_le_of_lt hx2 (lt_of_lt_of_le h1 hlam2_ge)
    have h3 : |x| < |lam| := sq_lt_sq.mp h2
    rwa [abs_of_nonneg hx0, abs_of_nonneg hlam0] at h3
  have hA2B2 : A^2 + B^2 = A^2*(1+x^2) := by rw [hB_eq]; ring
  have hxlam_pos : 0 < lam - rho*x := by
    have h : rho*x ≤ x := by nlinarith only [hrho, hrho_le_one, hx0]
    linarith [hx_lt_lam, h]
  have hlamA_ge : 0 < s*(lam*A - rho*B) := by
    have he : lam*A - rho*B = A*(lam - rho*x) := by rw [hB_eq]; ring
    rw [he]; exact mul_pos hs_pos (mul_pos hA hxlam_pos)
  have hA'_pos : 0 < A' := lt_of_lt_of_le hlamA_ge hA'ge
  have hA2B2pos : 0 < A^2 + B^2 := by nlinarith only [pow_pos hA 2, sq_nonneg B]
  have hDpos : 0 < s^2 * lam^2 * (A^2 + B^2) := mul_pos (mul_pos hs2pos hlam2pos) hA2B2pos
  have h1overlam : 1/lam^2 ≤ 225*μ/217 := by
    have h := (inv_le_inv₀ hlam2pos (by positivity : (0:ℝ) < 217/(225*μ))).mpr hlam2_ge
    rw [inv_div] at h
    simpa only [one_div] using h
  have hxlam_nn : 0 ≤ x/lam := div_nonneg hx0 hlam_pos.le
  have ht_le : x/lam ≤ 51/(25*μ) := by
    have h1 : (x/lam)^2 ≤ (51/(25*μ))^2 := by
      have hstep : x^2/lam^2 ≤ (4/μ^3)*(225*μ/217) := by
        calc x^2/lam^2 = x^2 * (1/lam^2) := by ring
          _ ≤ (4/μ^3) * (225*μ/217) :=
              mul_le_mul hx2 h1overlam (by positivity) (by positivity)
      have hstep2 : (4/μ^3)*(225*μ/217) ≤ (51/(25*μ))^2 := by
        rw [show (4/μ^3)*(225*μ/217) = 900/(217*μ^2) by field_simp <;> ring]
        rw [show (51/(25*μ))^2 = 2601/(625*μ^2) by field_simp <;> ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [sq_nonneg μ]
      have he : (x/lam)^2 = x^2/lam^2 := by ring
      rw [he]; linarith [hstep, hstep2]
    have hrhs_nn : 0 ≤ 51/(25*μ) := by positivity
    have h := sq_le_sq.mp h1
    rwa [abs_of_nonneg hxlam_nn, abs_of_nonneg hrhs_nn] at h
  have hnum_low : s^2*A^2*(lam - rho*x)^2 ≤ A'^2 + B'^2 := by
    have h1 : (s*(lam*A - rho*B))^2 ≤ A'^2 := pow_le_pow_left₀ (le_of_lt hlamA_ge) hA'ge 2
    have he : s*(lam*A - rho*B) = s*A*(lam - rho*x) := by rw [hB_eq]; ring
    rw [he] at h1
    nlinarith only [h1, sq_nonneg B']
  have hRat_low_aux : (lam - rho*x)^2/(lam^2*(1+x^2)) ≤ (A'^2+B'^2)/(s^2*lam^2*(A^2+B^2)) := by
    rw [hA2B2]
    have hd1 : (0:ℝ) < lam^2*(1+x^2) := mul_pos hlam2pos (by nlinarith only [hx0])
    have hd2 : (0:ℝ) < s^2*lam^2*(A^2*(1+x^2)) :=
      mul_pos (mul_pos hs2pos hlam2pos) (mul_pos (pow_pos hA 2) (by nlinarith only [hx0]))
    rw [div_le_div_iff₀ hd1 hd2]
    have h := mul_le_mul_of_nonneg_right hnum_low (le_of_lt hd1)
    nlinarith only [h]
  have h1mxpos : (0:ℝ) < 1 - x/lam := by rw [sub_pos, div_lt_one hlam_pos]; exact hx_lt_lam
  have h1mqpos : (0:ℝ) < 1 - 51/(25*μ) := by
    rw [sub_pos, div_lt_one (by positivity : (0:ℝ) < 25*μ)]; nlinarith only [hμ]
  have hbase_low : (1 - x/lam)^2/(1+x^2) ≤ (A'^2+B'^2)/(s^2*lam^2*(A^2+B^2)) := by
    have heq : (1 - x/lam)^2/(1+x^2) = (lam - x)^2/(lam^2*(1+x^2)) := by field_simp <;> ring
    rw [heq]
    calc (lam - x)^2/(lam^2*(1+x^2))
        ≤ (lam - rho*x)^2/(lam^2*(1+x^2)) := by
          apply div_le_div_of_nonneg_right _ (by nlinarith only [hlam2pos, hx0])
          exact pow_le_pow_left₀ (by linarith [hx_lt_lam]) (by nlinarith only [hrho_le_one, hx0]) 2
      _ ≤ (A'^2+B'^2)/(s^2*lam^2*(A^2+B^2)) := hRat_low_aux
  have hbase_low_pos : 0 < (1 - x/lam)^2/(1+x^2) :=
    div_pos (pow_pos h1mxpos 2) (by nlinarith only [hx0])
  have hden_le : ((1-x/lam)^2)⁻¹ ≤ ((1 - 51/(25*μ))^2)⁻¹ := by
    have ha : (0:ℝ) < (1-x/lam)^2 := pow_pos h1mxpos 2
    have hb : (0:ℝ) < (1 - 51/(25*μ))^2 := pow_pos h1mqpos 2
    refine (inv_le_inv₀ ha hb).mpr ?_
    apply pow_le_pow_left₀ h1mqpos.le _ 2
    linarith [ht_le]
  have hinvbase : ((1 - x/lam)^2/(1+x^2))⁻¹ ≤ (1+4/μ^3)/(1 - 51/(25*μ))^2 := by
    calc ((1 - x/lam)^2/(1+x^2))⁻¹
        = (1+x^2) * ((1-x/lam)^2)⁻¹ := by rw [inv_div]; ring
      _ ≤ (1+4/μ^3) * ((1-51/(25*μ))^2)⁻¹ := by
          apply mul_le_mul (by linarith [hx2]) hden_le
          · exact inv_nonneg.mpr (pow_nonneg h1mxpos.le 2)
          · positivity
      _ = (1+4/μ^3)/(1 - 51/(25*μ))^2 := by rw [inv_eq_one_div]; ring
  have hRat_inv : ((A'^2+B'^2)/(s^2*lam^2*(A^2+B^2)))⁻¹ ≤ 1 + 25/μ := by
    have h1 : ((A'^2+B'^2)/(s^2*lam^2*(A^2+B^2)))⁻¹ ≤ ((1 - x/lam)^2/(1+x^2))⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hbase_low_pos hbase_low
    exact le_trans h1 (le_trans hinvbase (lo_num μ hμ))
  have hnum_up : A'^2 + B'^2 ≤ s^2*(lam*A + rho*B)^2 + (s⁻¹)^2*(rho*A + lam*B)^2 := by
    have h1 : A'^2 ≤ (s*(lam*A + rho*B))^2 := pow_le_pow_left₀ (le_of_lt hA'_pos) hA'le 2
    have h2 : (s*(lam*A+rho*B))^2 = s^2*(lam*A+rho*B)^2 := by ring
    have h3 : B'^2 ≤ (s⁻¹*(rho*A+lam*B))^2 := pow_le_pow_left₀ hB'0 hB'le 2
    have h4 : (s⁻¹*(rho*A+lam*B))^2 = (s⁻¹)^2*(rho*A+lam*B)^2 := by ring
    rw [h2] at h1; rw [h4] at h3
    nlinarith only [h1, h3]
  have hq2 : (1:ℝ) ≤ μ^2 - 1 := by nlinarith only [hμ]
  have hs4 : μ^2 - 1 ≤ s^4 := by
    have h1 : (μ^2-1)^2 ≤ (s^2)^2 := pow_le_pow_left₀ hq.le hs2 2
    have h2 : (s^2)^2 = s^4 := by ring
    rw [h2] at h1
    nlinarith only [h1, hq2]
  have hT2_le : ((1+lam*x)^2/(lam^2*(1+x^2)))/(μ^2-1) ≤ (25/16) * ((225*μ)/(217*(μ^2-1))) := by
    have h1 : (1+lam*x)^2/(lam^2*(1+x^2)) ≤ (25/16)*(225*μ/217) := by
      have hnum : (1+lam*x)^2 ≤ 25/16 := by
        have hlx : (0:ℝ) ≤ lam*x := mul_nonneg hlam0 hx0
        have hlx2 : lam*x ≤ 1/4 := by nlinarith only [hlam_le_one, hx_quarter, hlam0, hx0]
        nlinarith only [hlx, hlx2]
      calc (1+lam*x)^2/(lam^2*(1+x^2))
          ≤ (1+lam*x)^2/lam^2 :=
            div_le_div_of_nonneg_left (by positivity) hlam2pos (by nlinarith only [hlam2pos, hx0])
        _ ≤ (25/16)/lam^2 := div_le_div_of_nonneg_right hnum hlam2pos.le
        _ = (25/16)*(1/lam^2) := by ring
        _ ≤ (25/16)*(225*μ/217) := mul_le_mul_of_nonneg_left h1overlam (by norm_num)
    calc ((1+lam*x)^2/(lam^2*(1+x^2)))/(μ^2-1)
        ≤ ((25/16)*(225*μ/217))/(μ^2-1) := div_le_div_of_nonneg_right h1 hq.le
      _ = (25/16)*((225*μ)/(217*(μ^2-1))) := by field_simp <;> ring
  have hT1_le : (lam+rho*x)^2/(lam^2*(1+x^2)) ≤ (1 + 51/(25*μ))^2 := by
    have hlr_nn : (0:ℝ) ≤ lam + rho*x := by nlinarith only [hlam_pos, hrho, hx0]
    calc (lam+rho*x)^2/(lam^2*(1+x^2))
        ≤ (lam+x)^2/(lam^2*(1+x^2)) := by
          apply div_le_div_of_nonneg_right _ (by nlinarith only [hlam2pos, hx0])
          apply pow_le_pow_left₀ hlr_nn _ 2
          nlinarith only [hrho_le_one, hx0]
      _ ≤ (lam+x)^2/lam^2 :=
          div_le_div_of_nonneg_left (by positivity) hlam2pos (by nlinarith only [hlam2pos, hx0])
      _ = (1 + x/lam)^2 := by field_simp <;> ring
      _ ≤ (1 + 51/(25*μ))^2 := by
          apply pow_le_pow_left₀ _ _ 2
          · linarith [hxlam_nn]
          · linarith [ht_le]
  have hRat_up : (A'^2+B'^2)/(s^2*lam^2*(A^2+B^2)) ≤ 1 + 25/μ := by
    have hsplit : (s^2*(lam*A+rho*B)^2 + (s⁻¹)^2*(rho*A+lam*B)^2)/(s^2*lam^2*(A^2+B^2))
        = (lam+rho*x)^2/(lam^2*(1+x^2)) + (rho+lam*x)^2/(s^4*lam^2*(1+x^2)) := by
      rw [hA2B2, hB_eq]
      field_simp <;> ring
    have hd_s4 : 0 < s^4*lam^2*(1+x^2) :=
      mul_pos (mul_pos (pow_pos hs_pos 4) hlam2pos) (by nlinarith only [hx0])
    have hd_mu : 0 < (μ^2-1)*lam^2*(1+x^2) := mul_pos (mul_pos hq hlam2pos) (by nlinarith only [hx0])
    have hfrac : (rho+lam*x)^2/(s^4*lam^2*(1+x^2)) ≤ ((1+lam*x)^2/(lam^2*(1+x^2)))/(μ^2-1) := by
      rw [show ((1+lam*x)^2/(lam^2*(1+x^2)))/(μ^2-1)
            = (1+lam*x)^2/((μ^2-1)*lam^2*(1+x^2)) by field_simp <;> ring]
      rw [div_le_div_iff₀ hd_s4 hd_mu]
      have hnum2 : (rho+lam*x)^2 ≤ (1+lam*x)^2 := by
        apply pow_le_pow_left₀ _ _ 2
        · nlinarith only [hrho, hlam0, hx0]
        · nlinarith only [hrho_le_one]
      have hcross := mul_le_mul hnum2 hs4 hq.le (pow_nonneg (by nlinarith only [hlam0, hx0]) 2)
      have h2 := mul_le_mul_of_nonneg_right hcross (by positivity : (0:ℝ) ≤ lam^2*(1+x^2))
      nlinarith only [h2]
    calc (A'^2+B'^2)/(s^2*lam^2*(A^2+B^2))
        ≤ (s^2*(lam*A+rho*B)^2 + (s⁻¹)^2*(rho*A+lam*B)^2)/(s^2*lam^2*(A^2+B^2)) :=
          div_le_div_of_nonneg_right hnum_up hDpos.le
      _ = (lam+rho*x)^2/(lam^2*(1+x^2)) + (rho+lam*x)^2/(s^4*lam^2*(1+x^2)) := hsplit
      _ ≤ (lam+rho*x)^2/(lam^2*(1+x^2)) + ((1+lam*x)^2/(lam^2*(1+x^2)))/(μ^2-1) :=
          add_le_add (le_refl _) hfrac
      _ ≤ 1 + 25/μ := by
          have hup := up_num μ hμ
          linarith [hT1_le, hT2_le, hup]
  have hR_pos : 0 < (A'^2+B'^2)/(s^2*lam^2*(A^2+B^2)) :=
    div_pos (by nlinarith only [hA'_pos, sq_nonneg B']) hDpos
  set R : ℝ := (A'^2+B'^2)/(s^2*lam^2*(A^2+B^2)) with hRdef
  have hlog1 : Real.log (1 + 25/μ) ≤ 25/μ := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 25/μ by positivity)
    linarith
  have hlog_up : Real.log R ≤ 25/μ := le_trans (Real.log_le_log hR_pos hRat_up) hlog1
  have hlog_lo : -(25/μ) ≤ Real.log R := by
    have h1 : Real.log (R⁻¹) ≤ Real.log (1 + 25/μ) := Real.log_le_log (inv_pos.mpr hR_pos) hRat_inv
    have h3 : Real.log (R⁻¹) ≤ 25/μ := le_trans h1 hlog1
    have h5 : -(25/μ) ≤ -(Real.log (R⁻¹)) := neg_le_neg h3
    have h4 : Real.log R = -(Real.log (R⁻¹)) := by rw [Real.log_inv R]; ring
    rw [h4]; exact h5
  have h25 : (25:ℝ)/μ ≤ 30/μ := by
    apply div_le_div_of_nonneg_right _ hμpos.le; norm_num
  rw [abs_le]
  exact ⟨le_trans (neg_le_neg h25) hlog_lo, le_trans hlog_up h25⟩

end Work.TMC7Core.Avalanche
