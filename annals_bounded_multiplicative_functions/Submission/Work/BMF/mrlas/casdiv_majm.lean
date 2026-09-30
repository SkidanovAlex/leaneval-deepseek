import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_Kbound
import Submission.Work.BMF.halasz_abel
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.mrlas.halasz_intM
import Submission.Work.BMF.LSeries_norm_le_exp_Wsup
import Submission.Work.BMF.mrlas.Kser_eq_neg_LSeries_mul_Psi
import Submission.Work.BMF.mrlas.Wsup_le_Zrcp
import Submission.Work.BMF.mrlas.Psi_norm_sq_continuous
import Submission.Work.BMF.window_weighted_integral_bound
import Submission.Work.BMF.casdiv.Kser_line_aemeasurable
import Submission.Work.BMF.mrlas.casdiv_psi1_l2
import Submission.Work.BMF.mrlas.casdiv_psi2_l2
import Submission.Work.BMF.mrlas.casdiv_middle_lint_bound
import Submission.Work.BMF.mrlas.casdiv_tail_lint_bound
import Submission.Work.BMF.mrlas.casdiv_kf_planch
import Submission.Work.BMF.mrlas.casdiv_wsup_step
import Submission.Work.BMF.mrlas.casdiv_zrcp_ratio
import Submission.Work.BMF.mrlas.casdiv_zrcp_log
import Submission.Work.BMF.mrlas.casdiv_dyadic_sum_meas
import Submission.Work.BMF.mrlas.Wsup_measurable
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ramaré's Proposition `casdiv` (specialised to `r ≡ 1`)

The assembly of `Work.BMF.mrlas.casdiv_majm` from the pieces proved in sibling modules:
step 2 (`casdiv_Mf_bound`, Abel's identity plus the Halász `K`-bound), the
Cauchy–Schwarz/Plancherel step (`casdiv_kf_planch`), the Plancherel bound at a single scale
(`casdiv_J_le`, from the weighted `L²` bounds for the log-derivative `Ψ` of the Euler product), the
per-scale bound (`casdiv_pscale`), the dyadic summation (`casdiv_dyadic_sum`) together with its two
inputs `casdiv_wsup_step` (almost-monotonicity of `Wsup` in the exponent) and `casdiv_zrcp_ratio`
(Mertens), and finally `casdiv_zrcp_log`, which removes the absolute constant error term.
-/

namespace Work.BMF.mrlas

open Finset Real MeasureTheory
open scoped BigOperators ENNReal



open Finset Real MeasureTheory
open scoped BigOperators

/-! ## Step 2: Abel's identity plus the Halász `K`-bound -/

/-- `∫_1^x ‖Mf f t‖/t dt ≤ x ∫_1^x ‖Mf f t‖/t² dt` for `1 ≤ x` and `1`-bounded `f`. -/
lemma casdiv_integral_Mf_div_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ / t) ≤
      x * ∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ / t ^ 2 := by
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖Work.BMF.Mf f t‖ ≤ t := fun t ht =>
    le_trans (Work.BMF.Mf_norm_le f hb t) (Nat.floor_le ht)
  have hI1 : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Mf f t‖ / t) volume 1 x := by
    refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => (1 : ℝ)) intervalIntegrable_const ?_ ?_
    · exact ((intM_measurable_Mf f).norm.div measurable_id).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_uIoc] with t ht
      have ht' : t ∈ Set.Ioc (1 : ℝ) x := by rwa [Set.uIoc_of_le hx] at ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht'.1
      simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) ht0.le)]
      rw [div_le_one ht0]
      exact hnorm t ht0.le
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x :=
    (ContinuousOn.inv₀ continuousOn_id (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).intervalIntegrable
  have hI2 : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Mf f t‖ / t ^ 2) volume 1 x := by
    refine IntervalIntegrable.mono_fun' (g := fun t : ℝ => t⁻¹) hinv ?_ ?_
    · exact ((intM_measurable_Mf f).norm.div (measurable_id.pow_const 2)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_uIoc] with t ht
      have ht' : t ∈ Set.Ioc (1 : ℝ) x := by rwa [Set.uIoc_of_le hx] at ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht'.1
      have hle : ‖Work.BMF.Mf f t‖ ≤ t := hnorm t ht0.le
      have h2 : 0 < t ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) h2.le)]
      rw [div_le_iff₀ h2, inv_mul_eq_div, show t ^ 2 / t = t by field_simp]
      exact hle
  have hI3 : IntervalIntegrable (fun t : ℝ => x * (‖Work.BMF.Mf f t‖ / t ^ 2)) volume 1 x :=
    hI2.const_mul x
  have hmono : (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ / t)
      ≤ ∫ t in (1 : ℝ)..x, x * (‖Work.BMF.Mf f t‖ / t ^ 2) := by
    refine intervalIntegral.integral_mono_on hx hI1 hI3 ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
    have hxx : t ≤ x := ht.2
    have hkey : (1:ℝ)/t ≤ x / t ^ 2 := by
      rw [div_le_div_iff₀ ht0 (by positivity)]; nlinarith
    calc ‖Work.BMF.Mf f t‖ / t = ‖Work.BMF.Mf f t‖ * (1 / t) := by ring
      _ ≤ ‖Work.BMF.Mf f t‖ * (x / t ^ 2) := mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
      _ = x * (‖Work.BMF.Mf f t‖ / t ^ 2) := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- **Step 2.** Abel's identity together with the Halász `K`-bound:
`‖Mf f x‖ ≤ (2x/log x) ∫_1^x ‖Mf f t‖/t² dt + C x/log x` for `x ≥ 3`. -/
theorem casdiv_Mf_bound : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x : ℝ, 3 ≤ x →
        ‖Work.BMF.Mf f x‖ ≤ (2 * x / Real.log x) *
            (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ / t ^ 2)
          + C * x / Real.log x := by
  obtain ⟨C₁, hC₁, hK⟩ := Work.BMF.halasz_Kbound
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro f hf1 hmul hb x hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hx2 : (2:ℝ) ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hKb := hK f hf1 hmul hb x hx2
  have habel := Work.BMF.halasz_abel f x hx1
  have hint : ‖∫ t in (1:ℝ)..x, Work.BMF.Mf f t / (t : ℂ)‖
      ≤ ∫ t in (1:ℝ)..x, ‖Work.BMF.Mf f t‖ / t := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx1) ?_
    refine le_of_eq ?_
    apply intervalIntegral.integral_congr
    intro t ht
    change ‖Work.BMF.Mf f t / (t:ℂ)‖ = ‖Work.BMF.Mf f t‖ / t
    rw [Set.uIcc_of_le hx1] at ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
  have hid : Work.BMF.Mf f x * (Real.log x : ℂ)
      = Work.BMF.Kf f x + ∫ t in (1:ℝ)..x, Work.BMF.Mf f t / (t : ℂ) := by
    rw [← habel]; ring
  have hnorm : ‖Work.BMF.Mf f x * (Real.log x : ℂ)‖ = ‖Work.BMF.Mf f x‖ * Real.log x := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog.le]
  have hkey : ‖Work.BMF.Mf f x‖ * Real.log x
      ≤ 2 * (x * (∫ t in (1:ℝ)..x, ‖Work.BMF.Mf f t‖ / t ^ 2)) + C₁ * x := by
    rw [← hnorm, hid]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add hKb hint) ?_
    have := casdiv_integral_Mf_div_le f hb hx1
    linarith
  rw [show (2 * x / Real.log x) * (∫ t in (1:ℝ)..x, ‖Work.BMF.Mf f t‖ / t ^ 2)
        + (C₁+1) * x / Real.log x
      = ((2 * (x * (∫ t in (1:ℝ)..x, ‖Work.BMF.Mf f t‖ / t ^ 2)) + C₁ * x) + x)
          / Real.log x by
        field_simp; ring]
  rw [le_div_iff₀ hlog]
  linarith [hkey]



/-! ## Weighted `L²` bounds for the log-derivative of the Euler product -/

/-- Unit-window `L²` bound for `Ψ = Ψ₁ + Ψ₂` on the line `Re s = 1+α`: for `0 < α ≤ 1` and any
`c`, `∫_c^{c+1} ‖Ψ f (1+α+iτ)‖² dτ ≤ C/α`.  (Consequence of the corresponding bounds
`casdiv_psi1_l2` for `Ψ₁` and `casdiv_psi2_l2` for `Ψ₂`, since `Ψ = Ψ₁ + Ψ₂`.) -/
theorem casdiv_psi_window : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ c : ℝ,
        (∫ τ in c..(c+1), ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
          ≤ C / α := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := casdiv_psi1_l2
  obtain ⟨C₂, hC₂pos, hC₂⟩ := casdiv_psi2_l2
  refine ⟨2 * C₁ + 2 * C₂, by positivity, ?_⟩
  intro f hf1 hb α hα hα1 c
  have ha1' : (1 : ℝ) < 1 + α := by linarith
  have hcontPsi : Continuous
      (fun τ : ℝ => ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) :=
    (Work.BMF.mrlas.Psi_nsc_Psi_continuous f hf1 hb (1 + α) ha1').norm.pow 2
  obtain ⟨hcontP1, hcontP2⟩ := Work.BMF.mrlas.Psi_norm_sq_continuous f hf1 hb (1 + α) ha1'
  have h1 := hC₁ f hb α hα hα1 c
  have h2 := hC₂ f hf1 hb α hα hα1 c
  have hsplit : ∀ τ : ℝ,
      ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
        ≤ 2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
          + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 := by
    intro τ
    have hPsi : Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
        = Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
          + Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) := by
      rw [Work.BMF.Psi2]; ring
    rw [hPsi]
    have hsq : (‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
          + ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) ^ 2
        ≤ 2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
          + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
        - ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖)]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2) hsq
  have hint : IntervalIntegrable
      (fun τ : ℝ => ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      volume c (c + 1) := hcontPsi.intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun τ : ℝ => 2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
        + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      volume c (c + 1) :=
    ((hcontP1.const_mul 2).add (hcontP2.const_mul 2)).intervalIntegrable _ _
  have hmono : (∫ τ in c..(c+1), ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      ≤ ∫ τ in c..(c+1), (2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
          + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on (by linarith : c ≤ c + 1) hint hint2 ?_
    intro τ _
    exact hsplit τ
  have hsum : (∫ τ in c..(c+1), (2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
        + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2))
      = 2 * (∫ τ in c..(c+1), ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
        + 2 * (∫ τ in c..(c+1), ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
    rw [intervalIntegral.integral_add ((hcontP1.const_mul 2).intervalIntegrable _ _)
      ((hcontP2.const_mul 2).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hfinal : (∫ τ in c..(c+1),
        2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
          + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      ≤ 2 * (C₁ / α) + 2 * (C₂ / α) := by linarith
  have hkey : 2 * (C₁ / α) + 2 * (C₂ / α) = (2 * C₁ + 2 * C₂) / α := by field_simp
  linarith [hmono, hsum ▸ hfinal, hkey.le, hkey.ge]

/-- **Weighted `L²` bounds for `Ψ` in lintegral form** (middle range and the two tails). -/
theorem casdiv_psi_lbounds_self :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ T : ℝ, 1 ≤ T →
        (∫⁻ τ in Set.Icc (-T) T,
            ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
              ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)) ≤ ENNReal.ofReal (C / α) ∧
        (∫⁻ τ in Set.Ioi T,
            ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
              ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)) +
        (∫⁻ τ in Set.Iio (-T),
            ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
              ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)) ≤ ENNReal.ofReal (C / (α * T)) := by
  obtain ⟨Cp, hCppos, hpw⟩ := casdiv_psi_window
  obtain ⟨Cm, hCmpos, hmid⟩ := Work.BMF.mrlas.casdiv_middle_lint_bound
  obtain ⟨Ct, hCtpos, htail⟩ := casdiv_tail_lint_bound
  refine ⟨max Cm Ct * Cp, mul_pos (lt_max_of_lt_left hCmpos) hCppos, ?_⟩
  intro f hf1 hb α hα hα1 T hT
  have ha1 : (1 : ℝ) ≤ 1 + α := by linarith
  have ha1' : (1 : ℝ) < 1 + α := by linarith
  set F : ℝ → ℝ := fun τ =>
    ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 with hFdef
  have hFc : Continuous F := by
    rw [hFdef]
    exact (Work.BMF.mrlas.Psi_nsc_Psi_continuous f hf1 hb (1 + α) ha1').norm.pow 2
  have hFnn : ∀ τ, 0 ≤ F τ := by intro τ; rw [hFdef]; positivity
  have hwin : ∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ Cp / α := by
    intro c; rw [hFdef]; exact hpw f hf1 hb α hα hα1 c
  have hden : ∀ τ : ℝ,
      ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 = (1 + α) ^ 2 + τ ^ 2 := by
    intro τ
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  constructor
  · have hcong : (∫⁻ τ in Set.Icc (-T) T,
          ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2))
        = ∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2)) := by
      apply lintegral_congr
      intro τ
      rw [hFdef, hden]
    rw [hcong]
    refine le_trans (hmid F hFc hFnn (Cp / α) (1 + α) T ha1 hT hwin) ?_
    apply ENNReal.ofReal_le_ofReal
    rw [show Cm * (Cp / α) = Cm * Cp / α by ring]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Cm Ct) hCppos.le) hα.le
  · have hcongT : (∫⁻ τ in Set.Ioi T,
          ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2))
        = ∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2)) := by
      apply lintegral_congr
      intro τ
      rw [hFdef, hden]
    have hcongI : (∫⁻ τ in Set.Iio (-T),
          ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2))
        = ∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2)) := by
      apply lintegral_congr
      intro τ
      rw [hFdef, hden]
    rw [hcongT, hcongI]
    refine le_trans (htail F hFc hFnn (Cp / α) (1 + α) T ha1 hT hwin) ?_
    apply ENNReal.ofReal_le_ofReal
    have hstep : Ct * (Cp / α) / T ≤ max Cm Ct * Cp / (α * T) := by
      rw [← mul_div_assoc, div_div]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right Cm Ct) hCppos.le) (by positivity)
    exact hstep

/-! ## The Plancherel bound at a single scale -/

/-- `e^{y}^2 = e^{2y}`. -/
private lemma casdiv_exp_sq (y : ℝ) : Real.exp y ^ 2 = Real.exp (2 * y) := by
  rw [sq, ← Real.exp_add]; congr 1; ring

/-- `‖Kser‖²/‖s‖² ≤ b² ‖Ψ‖²/‖s‖²` on `Re s = a > 1` whenever `‖LSeries f s‖ ≤ b`. -/
private lemma casdiv_Kser_div_le (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hb : ∀ n, ‖f n‖ ≤ 1)
    {a b τ : ℝ} (ha : 1 < a)
    (hLb : ‖LSeries f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ b) :
    ‖Work.BMF.Kser f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 ≤
      b ^ 2 * (‖Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
  have hker : Work.BMF.Kser f ((a : ℂ) + (τ : ℂ) * Complex.I)
      = -(LSeries f ((a : ℂ) + (τ : ℂ) * Complex.I)) *
        Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I) :=
    Work.BMF.mrlas.Kser_eq_neg_LSeries_mul_Psi f hf1 hmul hb (by simp; linarith)
  calc ‖Work.BMF.Kser f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
      = ‖LSeries f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 *
          (‖Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
        rw [hker, norm_mul, norm_neg]
        ring
    _ ≤ b ^ 2 * (‖Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
          ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) hLb 2

/-- **Plancherel bound for `Kser` at the scale `z`.**  For `f` multiplicative with `f 1 = 1` and
`‖f n‖ ≤ 1`, and `e ≤ z ≤ x`, `T ≥ 2`,

`∫_ℝ ‖Kser f (1+α+iτ)‖²/‖1+α+iτ‖² dτ ≤ C (log z · e^{2 Wsup f x α (T+1)} + e^{2 Zrcp z} log z / T)`

with `α = 1/log z`.  The near range `|τ| ≤ T` uses the pointwise Euler-product bound
`‖LSeries f s‖ ≤ C e^{Wsup f x α (T+1)}` (`LSeries_norm_le_exp_Wsup`) and the middle-range weighted
`L²` bound for `Ψ`; the far range `|τ| > T` uses the Euler-product bound at the scale `z` (where
`Wsup f z α (|τ|+1) ≤ Zrcp z` trivially) and the tail weighted `L²` bound for `Ψ`. -/
theorem casdiv_J_le : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x z T : ℝ, Real.exp 1 ≤ z → z ≤ x → 2 ≤ T →
        (∫ τ : ℝ,
            ‖Work.BMF.Kser f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
        ≤ C * (Real.log z * Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) +
               Real.exp (2 * Work.BMF.Zrcp z) * Real.log z / T) := by
  obtain ⟨CL, hCLpos, hCL⟩ := Work.BMF.LSeries_norm_le_exp_Wsup
  obtain ⟨CP, hCPpos, hCP⟩ := casdiv_psi_lbounds_self
  refine ⟨CL ^ 2 * CP + 1, by positivity, ?_⟩
  intro f hf1 hmul hb x z T hz hzx hT
  have hz0 : 0 < z := lt_of_lt_of_le (Real.exp_pos 1) hz
  have hz2 : 2 ≤ z := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  have hL1 : 1 ≤ Real.log z := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hz
  have hLpos : 0 < Real.log z := by linarith
  have hαpos : 0 < 1 / Real.log z := by positivity
  have hα1 : 1 / Real.log z ≤ 1 := by rw [div_le_one hLpos]; linarith
  have hexpα : Real.exp (1 / (1 / Real.log z)) = z := by
    rw [one_div_one_div, Real.exp_log hz0]
  have hx2 : 2 ≤ x := le_trans hz2 hzx
  have hT1 : 1 ≤ T := by linarith
  have ha1 : (1 : ℝ) < 1 + 1 / Real.log z := by linarith
  set hfun : ℝ → ℝ := fun τ =>
      ‖Work.BMF.Kser f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
      ‖((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 with hhfun
  set Gfun : ℝ → ℝ := fun τ =>
      ‖Work.BMF.Psi f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
      ‖((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 with hGfun
  set X : ℝ := Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) with hX
  set Z : ℝ := Real.exp (2 * Work.BMF.Zrcp z) with hZ
  set Kmid : ℝ := CL ^ 2 * X with hKmid
  set Ktail : ℝ := CL ^ 2 * Z with hKtail
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hKmid0 : 0 < Kmid := by rw [hKmid]; positivity
  have hKtail0 : 0 < Ktail := by rw [hKtail]; positivity
  -- the `LSeries` bounds
  have hLmid : ∀ τ : ℝ, |τ| ≤ T →
      ‖LSeries f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        CL * Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) := by
    intro τ hτ
    have hre : ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I).re
        = 1 + 1 / Real.log z := by simp
    have him : |((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I).im| ≤ T + 1 := by
      have h2 : ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
      rw [h2]; linarith
    exact hCL f hf1 hmul hb x (1 / Real.log z) T hx2 hαpos (by rw [hexpα]; exact hzx) hre him
  have hLtail : ∀ τ : ℝ, T < |τ| →
      ‖LSeries f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ CL * Real.exp (Work.BMF.Zrcp z) := by
    intro τ _
    have h1 : ‖LSeries f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ CL * Real.exp (Work.BMF.Wsup f z (1 / Real.log z) (|τ| + 1)) := by
      refine hCL f hf1 hmul hb z (1 / Real.log z) |τ| hz2 hαpos (le_of_eq hexpα) (by simp) ?_
      have h2 : ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
      rw [h2]
      linarith [abs_nonneg τ]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (Wsup_le_Zrcp f hb z (|τ| + 1) (1 / Real.log z) hαpos.le)) hCLpos.le)
  -- pointwise comparisons
  have hptmid : ∀ τ : ℝ, |τ| ≤ T → hfun τ ≤ Kmid * Gfun τ := by
    intro τ hτ
    have h1 : hfun τ
        ≤ (CL * Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))) ^ 2 * Gfun τ := by
      simp only [hhfun, hGfun]
      exact casdiv_Kser_div_le f hf1 hmul hb (a := 1 + 1 / Real.log z)
        (b := CL * Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1)))
        (by linarith) (hLmid τ hτ)
    have h2 : (CL * Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))) ^ 2 = Kmid := by
      rw [hKmid, hX, mul_pow, casdiv_exp_sq]
    rwa [h2] at h1
  have hpttail : ∀ τ : ℝ, T < |τ| → hfun τ ≤ Ktail * Gfun τ := by
    intro τ hτ
    have h1 : hfun τ ≤ (CL * Real.exp (Work.BMF.Zrcp z)) ^ 2 * Gfun τ := by
      simp only [hhfun, hGfun]
      exact casdiv_Kser_div_le f hf1 hmul hb (a := 1 + 1 / Real.log z)
        (b := CL * Real.exp (Work.BMF.Zrcp z)) (by linarith) (hLtail τ hτ)
    have h2 : (CL * Real.exp (Work.BMF.Zrcp z)) ^ 2 = Ktail := by
      rw [hKtail, hZ, mul_pow, casdiv_exp_sq]
    rwa [h2] at h1
  -- continuity and measurability
  have hGcont : Continuous Gfun := by
    rw [hGfun]
    have h1 : Continuous (fun τ : ℝ =>
        ‖Work.BMF.Psi f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) :=
      (Work.BMF.mrlas.Psi_nsc_Psi_continuous f hf1 hb (1 + 1 / Real.log z) ha1).norm.pow 2
    have h2 : Continuous (fun τ : ℝ =>
        ‖((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by fun_prop
    exact h1.div h2 (fun τ => by
      have hne : ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        have hp : 0 < (Real.log z)⁻¹ := inv_pos.mpr hLpos
        linarith
      exact ne_of_gt (pow_pos (norm_pos_iff.mpr hne) 2))
  have hGmeas : Measurable (fun τ : ℝ => ENNReal.ofReal (Gfun τ)) :=
    ENNReal.measurable_ofReal.comp hGcont.measurable
  have hA : AEStronglyMeasurable hfun volume := by
    have h1 : AEMeasurable (fun τ : ℝ =>
        Work.BMF.Kser f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)) volume :=
      Work.BMF.casdiv.Kser_line_aemeasurable f (1 + 1 / Real.log z) ha1
    have h2 : AEMeasurable (fun τ : ℝ =>
        ‖((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) volume := by
      have hc : Continuous (fun τ : ℝ =>
          ‖((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by fun_prop
      exact hc.aemeasurable
    rw [hhfun]
    exact ((h1.norm.pow_const 2).div h2).aestronglyMeasurable
  have hstep3 : (∫ τ : ℝ, hfun τ) = (∫⁻ τ : ℝ, ENNReal.ofReal (hfun τ)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun τ => div_nonneg (sq_nonneg _) (sq_nonneg _))) hA
  have hsplit : (∫⁻ τ : ℝ, ENNReal.ofReal (hfun τ)) =
      (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)) +
      (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)) :=
    (lintegral_add_compl _ measurableSet_Icc).symm
  -- the middle piece
  have hmidpt : ∀ᵐ τ ∂(volume.restrict (Set.Icc (-T) T)),
      ENNReal.ofReal (hfun τ) ≤ ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [← ENNReal.ofReal_mul hKmid0.le]
    exact ENNReal.ofReal_le_ofReal (hptmid τ (abs_le.mpr ⟨hτ.1, hτ.2⟩))
  have hIntMid : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)).toReal
      ≤ Kmid * (CP / (1 / Real.log z)) := by
    have hchild : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ))
        ≤ ENNReal.ofReal (CP / (1 / Real.log z)) := by
      rw [hGfun]
      exact (hCP f hf1 hb (1 / Real.log z) hαpos hα1 T hT1).1
    have hle : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)) ≤
        (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ)) :=
      lintegral_mono_ae hmidpt
    have heq : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ)) =
        ENNReal.ofReal Kmid * (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ)) :=
      lintegral_const_mul _ hGmeas
    have hbne : (∫⁻ τ in Set.Icc (-T) T,
        ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ)) ≠ ⊤ := by
      rw [heq]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hchild)
    calc (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)).toReal
        ≤ (∫⁻ τ in Set.Icc (-T) T,
            ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ)).toReal :=
          ENNReal.toReal_mono hbne hle
      _ = (ENNReal.ofReal Kmid *
            (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ))).toReal := by rw [heq]
      _ = Kmid * (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKmid0.le]
      _ ≤ Kmid * (CP / (1 / Real.log z)) := by
          apply mul_le_mul_of_nonneg_left _ hKmid0.le
          calc (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ)).toReal
              ≤ (ENNReal.ofReal (CP / (1 / Real.log z))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hchild
            _ = CP / (1 / Real.log z) := ENNReal.toReal_ofReal (by positivity)
  -- the two tails
  have hcset : (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
    ext τ
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      rcases lt_or_ge τ (-T) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (lt_of_not_ge (fun h2 => h ⟨h1, h2⟩))
    · rintro (h1 | h1) ⟨h2, h3⟩
      · exact absurd h2 (not_le.mpr h1)
      · exact absurd h3 (not_le.mpr h1)
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro τ h1 h2
    simp only [Set.mem_Iio] at h1
    simp only [Set.mem_Ioi] at h2
    linarith
  have hunion : (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)) =
      (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (hfun τ)) +
      (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (hfun τ)) := by
    rw [hcset, lintegral_union measurableSet_Ioi hdisj]
  have htailNeg : (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (hfun τ)) ≤
      ENNReal.ofReal Ktail * (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) := by
    have hpt : ∀ᵐ τ ∂(volume.restrict (Set.Iio (-T))),
        ENNReal.ofReal (hfun τ) ≤ ENNReal.ofReal Ktail * ENNReal.ofReal (Gfun τ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iio] with τ hτ
      rw [← ENNReal.ofReal_mul hKtail0.le]
      exact ENNReal.ofReal_le_ofReal (hpttail τ (by
        simp only [Set.mem_Iio] at hτ
        rw [abs_of_neg (by linarith : τ < 0)]
        linarith))
    exact (lintegral_mono_ae hpt).trans_eq (lintegral_const_mul _ hGmeas)
  have htailPos : (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (hfun τ)) ≤
      ENNReal.ofReal Ktail * (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ)) := by
    have hpt : ∀ᵐ τ ∂(volume.restrict (Set.Ioi T)),
        ENNReal.ofReal (hfun τ) ≤ ENNReal.ofReal Ktail * ENNReal.ofReal (Gfun τ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with τ hτ
      rw [← ENNReal.ofReal_mul hKtail0.le]
      exact ENNReal.ofReal_le_ofReal (hpttail τ (by
        simp only [Set.mem_Ioi] at hτ
        rw [abs_of_pos (by linarith : 0 < τ)]
        linarith))
    exact (lintegral_mono_ae hpt).trans_eq (lintegral_const_mul _ hGmeas)
  have hIntTail : (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)).toReal
      ≤ Ktail * (CP / (1 / Real.log z * T)) := by
    have hchild' : (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
        (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ))
        ≤ ENNReal.ofReal (CP / (1 / Real.log z * T)) := by
      rw [hGfun]
      rw [add_comm]
      exact (hCP f hf1 hb (1 / Real.log z) hαpos hα1 T hT1).2
    have hsum := add_le_add htailNeg htailPos
    rw [← mul_add] at hsum
    have hbne : ENNReal.ofReal Ktail *
        ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
         (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hchild')
    calc (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)).toReal
        = ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (hfun τ)) +
            (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (hfun τ))).toReal := by rw [hunion]
      _ ≤ (ENNReal.ofReal Ktail *
            ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
             (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ)))).toReal :=
          ENNReal.toReal_mono hbne hsum
      _ = Ktail * ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
            (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ))).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKtail0.le]
      _ ≤ Ktail * (CP / (1 / Real.log z * T)) := by
          apply mul_le_mul_of_nonneg_left _ hKtail0.le
          calc ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
                (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ))).toReal
              ≤ (ENNReal.ofReal (CP / (1 / Real.log z * T))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hchild'
            _ = CP / (1 / Real.log z * T) := ENNReal.toReal_ofReal (by positivity)
  -- assemble
  have hfin : (∫ τ : ℝ, hfun τ)
      ≤ Kmid * (CP / (1 / Real.log z)) + Ktail * (CP / (1 / Real.log z * T)) := by
    rw [hstep3, hsplit]
    calc ((∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)) +
          (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ))).toReal
        ≤ (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)).toReal +
          (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)).toReal := ENNReal.toReal_add_le
      _ ≤ Kmid * (CP / (1 / Real.log z)) + Ktail * (CP / (1 / Real.log z * T)) :=
          add_le_add hIntMid hIntTail
  refine hfin.trans ?_
  have hkey : Kmid * (CP / (1 / Real.log z)) + Ktail * (CP / (1 / Real.log z * T))
      = (CL ^ 2 * CP) * (Real.log z * X + Z * Real.log z / T) := by
    rw [hKmid, hKtail]
    field_simp
  rw [hkey]
  have hsum0 : 0 ≤ Real.log z * X + Z * Real.log z / T := by
    have h1 : 0 ≤ Real.log z * X := mul_nonneg hLpos.le hX0
    have h2 : 0 ≤ Z * Real.log z / T := by positivity
    linarith
  calc (CL ^ 2 * CP) * (Real.log z * X + Z * Real.log z / T)
      ≤ (CL ^ 2 * CP + 1) * (Real.log z * X + Z * Real.log z / T) := by
        apply mul_le_mul_of_nonneg_right _ hsum0
        linarith
    _ = (CL ^ 2 * CP + 1) *
          (Real.log z * Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) +
           Real.exp (2 * Work.BMF.Zrcp z) * Real.log z / T) := by
        rw [hX, hZ]
/-! ## The per-scale bound -/

/-- **Per-scale bound.**  For `f` multiplicative with `f 1 = 1`, `‖f n‖ ≤ 1`, `e ≤ z ≤ x` and
`T ≥ 2`,
`∫_{√z}^{z} ‖Mf f t‖/t² dt ≤ C (e^{Wsup f x (1/log z)(T+1)} + e^{Zrcp z}/√T + 1/log z)`. -/
theorem casdiv_pscale : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x z T : ℝ, Real.exp 1 ≤ z → z ≤ x → 2 ≤ T →
        (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ / t ^ 2) ≤
          C * (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) +
               Real.exp (Work.BMF.Zrcp z) / Real.sqrt T + 1 / Real.log z) := by
  obtain ⟨CM, hCMpos, hIntM⟩ := Work.BMF.mrlas.halasz_intM
  obtain ⟨CK, hCKpos, hCS⟩ := casdiv_kf_planch
  obtain ⟨CJ, hCJpos, hJb⟩ := casdiv_J_le
  refine ⟨4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1, by positivity, ?_⟩
  intro f hf1 hmul hb x z T hz hzx hT
  have hz_gt1 : (1 : ℝ) < z := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) hz
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz_gt1
  have hz2 : (2 : ℝ) ≤ z := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  have hlogpos : 0 < Real.log z := Real.log_pos hz_gt1
  have hsqz1 : (1 : ℝ) ≤ Real.sqrt z := Real.one_le_sqrt.mpr hz1
  have hsqzz : Real.sqrt z ≤ z := by
    have h : z ≤ z ^ 2 := by nlinarith
    calc Real.sqrt z ≤ Real.sqrt (z ^ 2) := Real.sqrt_le_sqrt h
      _ = z := Real.sqrt_sq (by linarith)
  have hbracket : 0 ≤ Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) +
      Real.exp (Work.BMF.Zrcp z) / Real.sqrt T + 1 / Real.log z := by
    have h1 := Real.exp_pos (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
    have h2 : 0 ≤ Real.exp (Work.BMF.Zrcp z) / Real.sqrt T := by positivity
    have h3 : 0 ≤ 1 / Real.log z := by positivity
    linarith
  rcases le_or_gt z 3 with hzle | hzgt
  · -- regime `z ≤ 3`
    have hlog3 : Real.log z ≤ Real.log 3 := Real.log_le_log (by linarith) hzle
    have hpt : ∀ t ∈ Set.Icc (Real.sqrt z) z, ‖Work.BMF.Mf f t‖ / t ^ 2 ≤ 1 / t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by linarith) ht.1
      rw [div_le_iff₀ (show (0 : ℝ) < t ^ 2 by positivity)]
      have heq : (1 / t) * t ^ 2 = t := by field_simp
      rw [heq]
      exact Work.BMF.Mf_norm_le_x f hb t ht0.le
    have hI1 : IntervalIntegrable (fun t : ℝ => ‖Work.BMF.Mf f t‖ / t ^ 2) volume (Real.sqrt z) z :=
      (Work.BMF.mrlas.intM_intervalIntegrable_norm_Mf_div_sq f hb hz1).mono_set (by
        rw [Set.uIcc_of_le hsqzz, Set.uIcc_of_le hz1]
        exact Set.Icc_subset_Icc_left hsqz1)
    have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (Real.sqrt z) z := by
      simpa only [one_div] using intervalIntegral.intervalIntegrable_inv
        (f := fun t : ℝ => t) (μ := volume) (a := Real.sqrt z) (b := z)
        (by intro t ht
            rw [Set.uIcc_of_le hsqzz] at ht
            exact ne_of_gt (lt_of_lt_of_le (by linarith) ht.1)) continuousOn_id
    have hlogs : Real.log (Real.sqrt z) = Real.log z / 2 := Real.log_sqrt (by linarith)
    have hcalc : (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ / t ^ 2) ≤ Real.log z / 2 := by
      calc (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ / t ^ 2)
          ≤ ∫ t in Real.sqrt z..z, 1 / t :=
            intervalIntegral.integral_mono_on hsqzz hI1 hI2 hpt
        _ = Real.log (z / Real.sqrt z) := integral_one_div_of_pos (by linarith) (by linarith)
        _ = Real.log (Real.sqrt z) := by
            congr 1
            rw [div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))]
            rw [← sq, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ z)]
        _ = Real.log z / 2 := hlogs
    refine le_trans hcalc ?_
    have hlogz2 : Real.log z / 2 ≤ (Real.log 3 ^ 2 / 2) * (1 / Real.log z) := by
      rw [mul_one_div, le_div_iff₀ hlogpos]
      have hsq : Real.log z * Real.log z ≤ Real.log 3 * Real.log 3 :=
        mul_le_mul hlog3 hlog3 hlogpos.le (Real.log_nonneg (by norm_num))
      nlinarith [hsq]
    have h1 : (Real.log 3 ^ 2 / 2) * (1 / Real.log z)
        ≤ (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1) * (1 / Real.log z) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith [hCKpos, hCMpos, Real.sqrt_nonneg CJ, sq_nonneg (Real.log 3)]
    have h2 : (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1) * (1 / Real.log z)
        ≤ (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1)
          * (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) +
              Real.exp (Work.BMF.Zrcp z) / Real.sqrt T + 1 / Real.log z) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h3 : (0 : ℝ) ≤ Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) :=
        (Real.exp_pos _).le
      have h4 : (0 : ℝ) ≤ Real.exp (Work.BMF.Zrcp z) / Real.sqrt T := by positivity
      linarith [h3, h4]
    linarith [hlogz2, h1, h2]
  · -- regime `3 < z`
    have hz3' : (3 : ℝ) ≤ z := le_of_lt hzgt
    set J : ℝ := ∫ τ : ℝ,
        ‖Work.BMF.Kser f ((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖((((1 + 1 / Real.log z : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 with hJdef
    have hJ := hJb f hf1 hmul hb x z T hz hzx hT
    have hCSb := hCS f hb z hz3'
    have hJnn : 0 ≤ J := by
      rw [hJdef]
      refine integral_nonneg_of_ae ?_
      filter_upwards with τ
      positivity
    have hExpW : Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
        = (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hExpZ : Real.exp (2 * Work.BMF.Zrcp z) = (Real.exp (Work.BMF.Zrcp z)) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hratio : Real.exp (2 * Work.BMF.Zrcp z) / T
        = (Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) ^ 2 := by
      rw [hExpZ, div_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ T)]
    have hTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
    have hsqu : Real.sqrt (Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
          + Real.exp (2 * Work.BMF.Zrcp z) / T)
        ≤ Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
          + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T := by
      have ha : 0 ≤ Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1)) :=
        (Real.exp_pos _).le
      have hb' : 0 ≤ Real.exp (Work.BMF.Zrcp z) / Real.sqrt T := by positivity
      have h2 : Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
            + Real.exp (2 * Work.BMF.Zrcp z) / T
          = (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))) ^ 2
            + (Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) ^ 2 := by
        rw [hExpW, hratio]
      rw [h2]
      have h3 : (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))) ^ 2
            + (Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) ^ 2
          ≤ (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) ^ 2 := by
        nlinarith [mul_nonneg ha hb']
      calc Real.sqrt ((Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))) ^ 2
              + (Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) ^ 2)
          ≤ Real.sqrt ((Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) ^ 2) := Real.sqrt_le_sqrt h3
        _ = Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T := Real.sqrt_sq (by positivity)
    have hsqrt : Real.sqrt (J * Real.log z)
        ≤ Real.sqrt CJ * (Real.log z *
            (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)) := by
      have hstep : J * Real.log z ≤ (Real.sqrt CJ * Real.log z) ^ 2 *
          (Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
            + Real.exp (2 * Work.BMF.Zrcp z) / T) := by
        calc J * Real.log z
            ≤ (CJ * (Real.log z * Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (2 * Work.BMF.Zrcp z) * Real.log z / T)) * Real.log z :=
              mul_le_mul_of_nonneg_right hJ (by positivity)
          _ = (Real.sqrt CJ * Real.log z) ^ 2 *
              (Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (2 * Work.BMF.Zrcp z) / T) := by
              rw [mul_pow, Real.sq_sqrt hCJpos.le]
              ring
      calc Real.sqrt (J * Real.log z)
          ≤ Real.sqrt ((Real.sqrt CJ * Real.log z) ^ 2 *
              (Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (2 * Work.BMF.Zrcp z) / T)) := Real.sqrt_le_sqrt hstep
        _ = Real.sqrt ((Real.sqrt CJ * Real.log z) ^ 2)
              * Real.sqrt (Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (2 * Work.BMF.Zrcp z) / T) := Real.sqrt_mul (by positivity) _
        _ = (Real.sqrt CJ * Real.log z)
              * Real.sqrt (Real.exp (2 * Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (2 * Work.BMF.Zrcp z) / T) := by
              rw [Real.sqrt_sq (by positivity)]
        _ ≤ (Real.sqrt CJ * Real.log z)
              * (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) :=
              mul_le_mul_of_nonneg_left hsqu (by positivity)
        _ = Real.sqrt CJ * (Real.log z *
              (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)) := by ring
    have hKbound : (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ / t ^ 2)
        ≤ CK * Real.sqrt CJ * Real.log z *
            (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) := by
      calc (∫ t in (1 : ℝ)..z, ‖Work.BMF.Kf f t‖ / t ^ 2)
          ≤ CK * Real.sqrt (J * Real.log z) := hCSb
        _ ≤ CK * (Real.sqrt CJ * (Real.log z *
              (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T))) :=
              mul_le_mul_of_nonneg_left hsqrt hCKpos.le
        _ = CK * Real.sqrt CJ * Real.log z *
              (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) := by ring
    have hIntMb := hIntM f hb z hz1
    have hL4 : (∫ t in (1 : ℝ)..z, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
        ≤ 2 * (CK * Real.sqrt CJ * Real.log z *
            (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)) + CM := by
      linarith [hIntMb, hKbound]
    have hL2 : (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ / t ^ 2)
        ≤ (2 / Real.log z) * (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) := by
      have hpt : ∀ t ∈ Set.Icc (Real.sqrt z) z,
          ‖Work.BMF.Mf f t‖ / t ^ 2
            ≤ (2 / Real.log z) * (‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by linarith) ht.1
        have hlogt : Real.log z / 2 ≤ Real.log t := by
          rw [← Real.log_sqrt (by linarith : (0 : ℝ) ≤ z)]
          exact Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) ht.1
        have hlogt0 : 0 < Real.log t := by linarith
        have hdiv : 1 / Real.log t ≤ 2 / Real.log z := by
          rw [div_le_div_iff₀ hlogt0 hlogpos]
          linarith
        calc ‖Work.BMF.Mf f t‖ / t ^ 2
            = (‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) * (1 / Real.log t) := by
              field_simp
          _ ≤ (‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) * (2 / Real.log z) :=
              mul_le_mul_of_nonneg_left hdiv (by positivity)
          _ = (2 / Real.log z) * (‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) := by ring
      refine le_trans (intervalIntegral.integral_mono_on hsqzz ?_ ?_ hpt) ?_
      · exact (Work.BMF.mrlas.intM_intervalIntegrable_norm_Mf_div_sq f hb hz1).mono_set (by
          rw [Set.uIcc_of_le hsqzz, Set.uIcc_of_le hz1]
          exact Set.Icc_subset_Icc_left hsqz1)
      · exact ((Work.BMF.mrlas.intM_intervalIntegrable_norm_Mf_log_div_sq f hb hz1).mono_set (by
          rw [Set.uIcc_of_le hsqzz, Set.uIcc_of_le hz1]
          exact Set.Icc_subset_Icc_left hsqz1)).const_mul _
      · rw [intervalIntegral.integral_const_mul]
    have hL3 : (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
        ≤ (∫ t in (1 : ℝ)..z, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2) := by
      refine intervalIntegral.integral_mono_interval hsqz1 hsqzz (le_refl z) ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict
          (μ := volume) measurableSet_Ioc] with t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
        have h1 : 0 ≤ Real.log t := Real.log_nonneg ht1
        have h2 : 0 < t ^ 2 := by positivity
        exact div_nonneg (mul_nonneg (norm_nonneg _) h1) h2.le
      · exact Work.BMF.mrlas.intM_intervalIntegrable_norm_Mf_log_div_sq f hb hz1
    have hfinal : (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ / t ^ 2)
        ≤ 4 * CK * Real.sqrt CJ *
            (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)
          + 2 * CM / Real.log z := by
      have hmono : (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
          ≤ 2 * (CK * Real.sqrt CJ * Real.log z *
              (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)) + CM := le_trans hL3 hL4
      have hstep1 : (2 / Real.log z)
            * (∫ t in Real.sqrt z..z, ‖Work.BMF.Mf f t‖ * Real.log t / t ^ 2)
          ≤ (2 / Real.log z) * (2 * (CK * Real.sqrt CJ * Real.log z *
              (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)) + CM) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
      have hstep2 : (2 / Real.log z) * (2 * (CK * Real.sqrt CJ * Real.log z *
            (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)) + CM)
          = 4 * CK * Real.sqrt CJ *
              (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
                + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)
            + 2 * CM / Real.log z := by
        field_simp
        ring
      linarith [hL2, hstep1, hstep2]
    refine le_trans hfinal ?_
    have hkey : 4 * CK * Real.sqrt CJ *
          (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
            + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) + 2 * CM / Real.log z
        ≤ (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1)
          * (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
            + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T + 1 / Real.log z) := by
      have hA : 0 ≤ 4 * CK * Real.sqrt CJ := by positivity
      have hB : 0 ≤ 2 * CM := by positivity
      have h1 : 4 * CK * Real.sqrt CJ *
            (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)
          ≤ (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1)
            * (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith [hB, sq_nonneg (Real.log 3)]
      have h2 : 2 * CM / Real.log z
          ≤ (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1) * (1 / Real.log z) := by
        rw [div_eq_mul_one_div]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith [hA, sq_nonneg (Real.log 3)]
      have h3 : (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1)
            * (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T)
          + (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1) * (1 / Real.log z)
          = (4 * CK * Real.sqrt CJ + 2 * CM + Real.log 3 ^ 2 / 2 + 1)
            * (Real.exp (Work.BMF.Wsup f x (1 / Real.log z) (T + 1))
              + Real.exp (Work.BMF.Zrcp z) / Real.sqrt T + 1 / Real.log z) := by
        ring
      linarith [h1, h2, h3]
    exact hkey
/-! ## Ramaré's `casdiv` -/

/-- **Ramaré's Proposition `casdiv`, specialised to `r ≡ 1`.** For `f : ℕ → ℂ` multiplicative with
`f 1 = 1`, `‖f n‖ ≤ 1`, and `x ≥ 3`, `T ≥ 2`:
`‖Σ_{n ≤ x} f n‖ ≤ C (x/log x) [ ∫_{1/(2 log x)}^{1} exp(Wsup f x α (T+1)) dα/α + e^Z/√T + e^Z/log x ]`
with `Z = Zrcp x = Σ_{p ≤ x} 1/p` and `C` an absolute constant (Ramaré, arXiv:1709.01315,
Prop. `casdiv`, `r ≡ 1`; his `hypsupdiv` holds by Mertens: `Zrcp x - Zrcp y ≥ log (log x / log y) - O(1)`
is `casdiv_zrcp_ratio`, and `casdiv_zrcp_log` supplies the lower bound `e^{Zrcp x} ≥ c log x` which
absorbs the absolute error term of step 2).

The proof follows Ramaré's nine steps: 2. `casdiv_Mf_bound` (Abel + Halász `K`-bound);
3.–5. `casdiv_kf_planch` (Cauchy–Schwarz + Plancherel); 6. `casdiv_J_le` (the Plancherel integral at a
single scale, from the weighted `L²` bounds `casdiv_psi_lbounds` for the log-derivative of the Euler
product); 7. `casdiv_pscale` (the per-scale bound); 8. `casdiv_dyadic_sum` (dyadic summation, with
the inputs `casdiv_wsup_step` and `casdiv_zrcp_ratio`); 9. the present assembly. -/
theorem casdiv_majm :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Work.BMF.Mf f x‖ ≤ C * (x / Real.log x) *
          ((∫ α in (1 / (2 * Real.log x))..1,
              Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) +
           Real.exp (Work.BMF.Zrcp x) / Real.sqrt T +
           Real.exp (Work.BMF.Zrcp x) / Real.log x) := by
  obtain ⟨C₁, hC₁pos, hps⟩ := casdiv_pscale
  obtain ⟨C₂, hC₂pos, hst⟩ := casdiv_wsup_step
  obtain ⟨C₀M, hC₀Mpos, hMer⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  have hM : ∀ t : ℝ, 11 ≤ t → |Work.BMF.Zrcp t - Real.log (Real.log t)| ≤ C₀M := by
    intro t ht
    simpa only [Work.BMF.Zrcp] using hMer t ht
  obtain ⟨C₃, hC₃pos, hrat⟩ := casdiv_zrcp_ratio C₀M hC₀Mpos hM
  obtain ⟨C₅, hC₅pos, hlogb⟩ := casdiv_zrcp_log C₀M hC₀Mpos hM
  obtain ⟨C₄, hC₄pos, hdy⟩ := casdiv_dyadic_sum_meas C₁ C₂ C₃ hC₁pos hC₂pos hC₃pos
  obtain ⟨CM', hCM'pos, hMfb⟩ := casdiv_Mf_bound
  refine ⟨max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1, by positivity, ?_⟩
  intro f hf1 hmul hb x T hx hT
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hMmeas : Measurable (fun t : ℝ => ‖Work.BMF.Mf f t‖) :=
    (intM_measurable_Mf f).norm
  have hWmeas : Measurable (fun a : ℝ => Real.exp (Work.BMF.Wsup f x a (T + 1))) :=
    Real.continuous_exp.measurable.comp (Wsup_measurable f x (T + 1))
  have hWbd : ∃ c : ℝ, 0 ≤ c ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
      Real.exp (Work.BMF.Wsup f x a (T + 1)) ≤ c :=
    ⟨Real.exp (Work.BMF.Zrcp x), (Real.exp_pos _).le, fun a ha _ =>
      Real.exp_le_exp.mpr (Wsup_le_Zrcp f hb x (T + 1) a ha.le)⟩
  have hdyb := hdy (fun t : ℝ => ‖Work.BMF.Mf f t‖)
      (fun a : ℝ => Real.exp (Work.BMF.Wsup f x a (T + 1)))
      (fun y : ℝ => Real.exp (Work.BMF.Zrcp y)) x T hx hT hMmeas hWmeas
      (fun t _ => norm_nonneg _)
      (fun t ht => Work.BMF.Mf_norm_le_x f hb t ht)
      (fun a _ _ => (Real.exp_pos _).le)
      hWbd
      (Real.exp_pos _).le
      (fun z hz hzx => hps f hf1 hmul hb x z T hz hzx hT)
      (fun a b ha hab hba hb1 => hst f hb x (T + 1) a b hx2 ha hab hba hb1)
      (fun y hy hyx => hrat x y hy hyx)
  have hMb := hMfb f hf1 hmul hb x hx
  have hZlb := hlogb x hx
  set A : ℝ := ∫ α in (1 / (2 * Real.log x))..1, Real.exp (Work.BMF.Wsup f x α (T + 1)) / α
    with hA
  set Zx : ℝ := Real.exp (Work.BMF.Zrcp x) with hZx
  have hAnn : 0 ≤ A := by
    rw [hA]
    have hlogx3 : (1 : ℝ) ≤ Real.log x := by
      have h3 : (1 : ℝ) ≤ Real.log 3 := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      exact le_trans h3 (Real.log_le_log (by norm_num) hx)
    have h2lx : (0 : ℝ) < 2 * Real.log x := by linarith
    have hle : 1 / (2 * Real.log x) ≤ 1 := by
      rw [div_le_one h2lx]
      linarith
    refine intervalIntegral.integral_nonneg hle (fun t ht => ?_)
    have h1 : (0 : ℝ) < 1 / (2 * Real.log x) := by positivity
    exact div_nonneg (Real.exp_pos _).le (le_of_lt (lt_of_lt_of_le h1 ht.1))
  have hZnn : 0 ≤ Zx := by rw [hZx]; positivity
  have hTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  have hdyb' : (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ / t ^ 2) ≤ C₄ * (A + Zx / Real.sqrt T + 1) := by
    rw [hA, hZx]
    exact hdyb
  have h1 : 1 ≤ C₅ * Zx / Real.log x := by
    rw [hZx]
    exact hZlb
  have h2 : (2 * C₄ + CM') ≤ (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * (Zx / Real.log x) := by
    have hZxL : 0 ≤ Zx / Real.log x := div_nonneg hZnn hlogx.le
    have h4 : (2 * C₄ + CM') * C₅ ≤ max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1 := by
      have := le_max_right (2 * C₄) ((2 * C₄ + CM') * C₅)
      linarith
    calc (2 * C₄ + CM') = (2 * C₄ + CM') * 1 := by ring
      _ ≤ (2 * C₄ + CM') * (C₅ * (Zx / Real.log x)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith [hC₄pos, hCM'pos])
          rw [← mul_div_assoc]
          exact h1
      _ = ((2 * C₄ + CM') * C₅) * (Zx / Real.log x) := by ring
      _ ≤ (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * (Zx / Real.log x) :=
          mul_le_mul_of_nonneg_right h4 hZxL
  calc ‖Work.BMF.Mf f x‖
      ≤ (2 * x / Real.log x) * (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ / t ^ 2)
          + CM' * x / Real.log x := hMb
    _ ≤ (2 * x / Real.log x) * (C₄ * (A + Zx / Real.sqrt T + 1)) + CM' * x / Real.log x := by
        have hnn : 0 ≤ 2 * x / Real.log x := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hdyb' hnn) le_rfl
    _ ≤ (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * (x / Real.log x)
          * (A + Zx / Real.sqrt T + Zx / Real.log x) := by
        have hxL : 0 < x / Real.log x := by positivity
        have hfac : (2 * x / Real.log x) * (C₄ * (A + Zx / Real.sqrt T + 1))
              + CM' * x / Real.log x
            = (x / Real.log x) * (2 * C₄ * (A + Zx / Real.sqrt T + 1) + CM') := by ring
        rw [hfac]
        have hassoc : (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * (x / Real.log x)
              * (A + Zx / Real.sqrt T + Zx / Real.log x)
            = (x / Real.log x) * ((max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1)
              * (A + Zx / Real.sqrt T + Zx / Real.log x)) := by ring
        rw [hassoc]
        refine mul_le_mul_of_nonneg_left ?_ hxL.le
        have hZxn : 0 ≤ Zx / Real.sqrt T := div_nonneg hZnn hTpos.le
        set Y : ℝ := A + Zx / Real.sqrt T with hYdef
        set W : ℝ := Zx / Real.log x with hWdef
        have hY0 : 0 ≤ Y := by rw [hYdef]; exact add_nonneg hAnn hZxn
        have hle1 : 2 * C₄ ≤ max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1 := by
          have := le_max_left (2 * C₄) ((2 * C₄ + CM') * C₅)
          linarith
        have e1 : 2 * C₄ * Y ≤ (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * Y :=
          mul_le_mul_of_nonneg_right hle1 hY0
        have e2 : 2 * C₄ + CM' ≤ (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * W := h2
        have hY1 : 2 * C₄ * (Y + 1) = 2 * C₄ * Y + 2 * C₄ := by ring
        have hexp : (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * (Y + W)
            = (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * Y
              + (max (2 * C₄) ((2 * C₄ + CM') * C₅) + 1) * W := by ring
        rw [hY1, hexp]
        linarith [e1, e2]

end Work.BMF.mrlas
