import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Submission.Commons.Analysis.Real.exists_cos_sin_of_sq_add_sq_eq_one
import Submission.Commons.Analysis.Integral.circle_avg_inv_sqrt_mono_amplitude

open MeasureTheory Set Real
open scoped InnerProductSpace

namespace Commons.Analysis.Integral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖cos θ • e + sin θ • f‖ = 1` for an orthonormal pair `e, f`. -/
private lemma norm_cos_sin (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e,f⟫_ℝ = 0) (θ : ℝ) :
    ‖Real.cos θ • e + Real.sin θ • f‖ = 1 := by
  have h : ‖Real.cos θ • e + Real.sin θ • f‖^2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hef, mul_zero,
        norm_smul, norm_smul, he, hf, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [mul_one, mul_one, sq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (Real.cos θ • e + Real.sin θ • f), h]

private lemma inner_A_w (A e f : E) (θ : ℝ) :
    ⟪A, Real.cos θ • e + Real.sin θ • f⟫_ℝ
      = Real.cos θ * ⟪A,e⟫_ℝ + Real.sin θ * ⟪A,f⟫_ℝ := by
  rw [inner_add_right, inner_smul_right, inner_smul_right]

private lemma norm_sq_expand (A e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e,f⟫_ℝ = 0) (d θ : ℝ) :
    ‖A + d • (Real.cos θ • e + Real.sin θ • f)‖ ^ 2
      = ‖A‖^2 + d^2 + 2*d*(Real.cos θ * ⟪A,e⟫_ℝ + Real.sin θ * ⟪A,f⟫_ℝ) := by
  rw [norm_add_sq_real, inner_smul_right, inner_A_w, norm_smul, norm_cos_sin e f he hf hef θ]
  rw [mul_one, Real.norm_eq_abs, sq_abs]
  ring

/-- `‖v‖⁻¹ = (‖v‖²)^(-1/2)`. -/
private lemma inv_norm_eq_rpow (v : E) : (‖v‖)⁻¹ = (‖v‖^2)^(-(1:ℝ)/2) := by
  have hsq : (0:ℝ) ≤ ‖v‖^2 := by positivity
  have h1 : (‖v‖^2)^(-(1:ℝ)/2) = ((‖v‖^2)^((1:ℝ)/2))⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hsq]
  rw [h1, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg v)]

/-- The integral over a full period of a `2π`-periodic function is invariant under a shift. -/
private lemma integral_shift_eq {g : ℝ → ℝ} (hg : Function.Periodic g (2*Real.pi)) (φ : ℝ) :
    ∫ x in (0)..(2*Real.pi), g (x - φ) = ∫ x in (0)..(2*Real.pi), g x := by
  rw [intervalIntegral.integral_comp_sub_right]
  rw [show (0:ℝ)-φ = -φ by ring, show (2*Real.pi)-φ = -φ + 2*Real.pi by ring]
  rw [hg.intervalIntegral_add_eq (-φ) 0]
  rw [show (0:ℝ) + 2*Real.pi = 2*Real.pi by ring]

/-- Bessel: `⟪A,e⟫² + ⟪A,f⟫² ≤ ‖A‖²` for an orthonormal pair. -/
private lemma bessel (A e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e,f⟫_ℝ = 0) :
    ⟪A,e⟫_ℝ^2 + ⟪A,f⟫_ℝ^2 ≤ ‖A‖^2 := by
  set p := ⟪A,e⟫_ℝ with hp
  set q := ⟪A,f⟫_ℝ with hq
  have hpu : ⟪A, p • e + q • f⟫_ℝ = p^2+q^2 := by
    rw [inner_add_right, inner_smul_right, inner_smul_right, hp, hq]; ring
  have hnu : ‖p • e + q • f‖^2 = p^2+q^2 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hef, mul_zero,
        norm_smul, norm_smul, he, hf, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one,
        sq_abs, sq_abs]
    ring
  have hexp : ‖A - (p • e + q • f)‖^2 = ‖A‖^2 - (p^2+q^2) := by
    rw [show A - (p•e+q•f) = A + (-(p•e+q•f)) by abel]
    rw [norm_add_sq_real, inner_neg_right, norm_neg, hpu, hnu]
    ring
  have h3 : (0:ℝ) ≤ ‖A - (p • e + q • f)‖^2 := by positivity
  rw [hexp] at h3
  linarith

theorem circle_avg_inv_sub_le_phiFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f A : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) {d : ℝ}
    (hd : 0 ≤ d) (hA : 0 < ‖A‖) (hne : d ≠ ‖A‖) :
    (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (‖A + d • (Real.cos theta • e + Real.sin theta • f)‖)⁻¹
      ≤ (1 + (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
          (((1 + (d / ‖A‖) ^ 2 + 2 * (d / ‖A‖) * Real.cos theta) ^ (-(1:ℝ)/2)) - 1)) / ‖A‖ := by
  have hef' : ⟪e,f⟫_ℝ = 0 := hef
  set a : ℝ := ‖A‖ with ha_eq
  set p : ℝ := ⟪A,e⟫_ℝ with hp_eq
  set q : ℝ := ⟪A,f⟫_ℝ with hq_eq
  set b : ℝ := Real.sqrt (p^2+q^2) with hb_eq
  have ha_pos : 0 < a := by rw [ha_eq]; exact hA
  have hne' : d ≠ a := by rw [ha_eq]; exact hne
  have hb_nonneg : 0 ≤ b := Real.sqrt_nonneg _
  have hba : b ≤ a := by
    rw [hb_eq]
    have hle : p^2+q^2 ≤ a^2 := by
      rw [hp_eq, hq_eq, ha_eq]
      exact bessel A e f he hf hef'
    calc Real.sqrt (p^2+q^2) ≤ Real.sqrt (a^2) := Real.sqrt_le_sqrt hle
      _ = a := Real.sqrt_sq ha_pos.le
  -- phase: `p cos θ + q sin θ = b cos (θ - φ)`
  have hphase : ∃ φ : ℝ, ∀ θ : ℝ, p*Real.cos θ + q*Real.sin θ = b*Real.cos (θ-φ) := by
    by_cases hb : b = 0
    · refine ⟨0, fun θ => ?_⟩
      have hp0 : p = 0 ∧ q = 0 := by
        have hb2 : b^2 = 0 := by rw [hb]; ring
        have hp2q2 : p^2+q^2 = 0 := by
          rw [hb_eq] at hb2
          rwa [Real.sq_sqrt (by positivity : (0:ℝ) ≤ p^2+q^2)] at hb2
        constructor <;> nlinarith [sq_nonneg p, sq_nonneg q]
      rw [hp0.1, hp0.2, hb]
      ring
    · have hbpos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb)
      have hb2 : b^2 = p^2+q^2 := by rw [hb_eq]; exact Real.sq_sqrt (by positivity)
      have h1 : (p/b)^2 + (q/b)^2 = 1 := by
        have hne0 : p^2+q^2 ≠ 0 := by rw [← hb2]; positivity
        rw [div_pow, div_pow, ← add_div, hb2, div_self hne0]
      obtain ⟨φ, hc, hs⟩ := Commons.Analysis.Real.exists_cos_sin_of_sq_add_sq_eq_one h1
      refine ⟨φ, fun θ => ?_⟩
      rw [Real.cos_sub, hc, hs]
      field_simp
  obtain ⟨φ, hφ⟩ := hphase
  -- LHS reduction to the amplitude-`b` circle average
  have hL : (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (‖A + d • (Real.cos theta • e + Real.sin theta • f)‖)⁻¹
      = (1 / (2 * Real.pi)) * ∫ u in (0)..(2 * Real.pi),
            (a^2 + d^2 + 2*d*b*Real.cos u)^(-(1:ℝ)/2) := by
    congr 1
    have h1 : ∫ theta in (0)..(2 * Real.pi),
          (‖A + d • (Real.cos theta • e + Real.sin theta • f)‖)⁻¹
        = ∫ theta in (0)..(2 * Real.pi),
            (a^2 + d^2 + 2*d*(p*Real.cos theta+q*Real.sin theta))^(-(1:ℝ)/2) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [inv_norm_eq_rpow, norm_sq_expand A e f he hf hef' d θ]
      rw [ha_eq, hp_eq, hq_eq]; congr 1; ring
    have h2 : ∫ theta in (0)..(2 * Real.pi),
            (a^2 + d^2 + 2*d*(p*Real.cos theta+q*Real.sin theta))^(-(1:ℝ)/2)
        = ∫ theta in (0)..(2 * Real.pi),
            (a^2 + d^2 + 2*d*b*Real.cos (theta-φ))^(-(1:ℝ)/2) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [hφ θ]; congr 1; ring
    have h3 : ∫ theta in (0)..(2 * Real.pi),
            (a^2 + d^2 + 2*d*b*Real.cos (theta-φ))^(-(1:ℝ)/2)
        = ∫ u in (0)..(2 * Real.pi),
            (a^2 + d^2 + 2*d*b*Real.cos u)^(-(1:ℝ)/2) := by
      have hG : Function.Periodic (fun u : ℝ => (a^2 + d^2 + 2*d*b*Real.cos u)^(-(1:ℝ)/2)) (2*Real.pi) := by
        intro u; simp only [Real.cos_add_two_pi]
      simpa only using integral_shift_eq hG φ
    rw [h1, h2, h3]
  -- RHS reduction to the amplitude-`a` circle average
  have hA0pos : ∀ θ : ℝ, 0 < 1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ := by
    intro θ
    have hr : 0 ≤ d / a := div_nonneg hd ha_pos.le
    have h1 : -(2 * (d / a)) ≤ 2 * (d / a) * Real.cos θ := by
      have := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) (by linarith : (0:ℝ) ≤ 2 * (d / a))
      nlinarith [this]
    have hne2 : d / a ≠ 1 := by
      intro h
      have hh : d = a := by rw [div_eq_iff ha_pos.ne'] at h; simpa using h
      exact hne' hh
    nlinarith [h1, sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hne2))]
  have hkey : ∀ θ : ℝ, (1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ) ^ (-(1:ℝ)/2)
      = a * (a^2 + d^2 + 2*d*a*Real.cos θ) ^ (-(1:ℝ)/2) := by
    intro θ
    have hMpos : 0 < a^2 + d^2 + 2*d*a*Real.cos θ := by
      have hAeq : a^2 + d^2 + 2*d*a*Real.cos θ
          = a^2 * (1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ) := by
        field_simp
      rw [hAeq]
      exact mul_pos (by positivity) (hA0pos θ)
    rw [show 1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ
          = (a^2 + d^2 + 2*d*a*Real.cos θ) / a^2 by field_simp]
    rw [Real.div_rpow (le_of_lt hMpos) (by positivity : (0:ℝ) ≤ a^2)]
    rw [show (a^2) ^ (-(1:ℝ)/2) = a⁻¹ by
          rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (by positivity : (0:ℝ) ≤ a^2)]
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ha_pos.le]]
    rw [div_inv_eq_mul]
    ring
  have hR : (1 + (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
          (((1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos theta) ^ (-(1:ℝ)/2)) - 1)) / a
      = (1 / (2 * Real.pi)) * ∫ u in (0)..(2 * Real.pi),
            (a^2 + d^2 + 2*d*a*Real.cos u)^(-(1:ℝ)/2) := by
    have hcontA0 : Continuous (fun θ : ℝ => 1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ) := by
      fun_prop
    have hfcont : Continuous (fun θ : ℝ => (1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ) ^ (-(1:ℝ)/2)) :=
      hcontA0.rpow_const (fun θ => Or.inl (ne_of_gt (hA0pos θ)))
    have hfint : IntervalIntegrable (fun θ : ℝ => (1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ) ^ (-(1:ℝ)/2)) volume 0 (2*Real.pi) :=
      hfcont.intervalIntegrable 0 (2*Real.pi)
    have hsplit : ∫ θ in (0)..(2*Real.pi),
          ((1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ) ^ (-(1:ℝ)/2) - 1)
        = a * (∫ θ in (0)..(2*Real.pi), (a^2 + d^2 + 2*d*a*Real.cos θ) ^ (-(1:ℝ)/2)) - 2*Real.pi := by
      rw [intervalIntegral.integral_sub hfint intervalIntegrable_const]
      have hfeq : (∫ θ in (0)..(2*Real.pi), (1 + (d / a) ^ 2 + 2 * (d / a) * Real.cos θ) ^ (-(1:ℝ)/2))
          = ∫ θ in (0)..(2*Real.pi), a * (a^2 + d^2 + 2*d*a*Real.cos θ) ^ (-(1:ℝ)/2) := by
        apply intervalIntegral.integral_congr; intro θ _; exact hkey θ
      rw [hfeq, intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, mul_one]
    rw [hsplit]
    field_simp
    ring
  rw [hL, hR]
  exact circle_avg_inv_sqrt_mono_amplitude ha_pos hd hne' hb_nonneg hba

end Commons.Analysis.Integral