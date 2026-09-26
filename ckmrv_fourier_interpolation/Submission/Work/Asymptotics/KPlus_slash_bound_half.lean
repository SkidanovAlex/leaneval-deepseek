import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KPlus_slash_cusp_ball
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.KPlusFunnel.Atoms
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.ZAtomsThird.cusp_forms
import Submission.Work.Asymptotics.ZAtomsThird.first_order

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

open Work.Kernels

/-! ## Elementary norm helpers -/

private lemma nmul2 {a b : ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) hA

private lemma nmul3 {a b c : ℂ} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) : ‖a * b * c‖ ≤ A * B * C := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hA) hc (norm_nonneg _) (mul_nonneg hA hB)

private lemma nmul4 {a b c d : ℂ} {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) :
    ‖a * b * c * d‖ ≤ A * B * C * D := by
  have h3 := nmul3 (a := a) (b := b) (c := c) hA hB hC ha hb hc
  rw [norm_mul]
  exact mul_le_mul h3 hd (norm_nonneg _) (by positivity)

private lemma nmul5 {a b c d e : ℂ} {A B C D E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C)
    (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) : ‖a * b * c * d * e‖ ≤ A * B * C * D * E := by
  have h4 := nmul4 (a := a) (b := b) (c := c) (d := d) hA hB hC hD ha hb hc hd
  rw [norm_mul]
  exact mul_le_mul h4 he (norm_nonneg _) (by positivity)

/-- `3/π ≤ 3` and `6/π ≤ 6` and `9/π ≤ 9`. -/
private lemma three_div_pi_le : (3 : ℝ) / Real.pi ≤ 3 := by
  rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]

private lemma six_div_pi_le : (6 : ℝ) / Real.pi ≤ 6 := by
  rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]

private lemma nine_div_pi_le : (9 : ℝ) / Real.pi ≤ 9 := by
  rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]

/-! ## Pointwise bounds for the `τ`-atoms and the `z`-atoms -/

/-- At a point `a` with `Im a ≥ 1/3` the elementary `q`-estimates of `first_order` and
`cusp_forms` give explicit `(1 + ‖a‖)`-bounds for all the atoms appearing in `Ξ₈` and `Ξ₂₄`. -/
private lemma atom_bounds (C1 Cc : ℝ) (hC1 : 0 < C1) (hCc : 0 < Cc)
    (hE2 : ∀ a : UpperHalfPlane, 1 / 3 ≤ a.im → ‖E2Fun a - 1‖ ≤ C1 * ‖qParamFun a‖)
    (hE4 : ∀ a : UpperHalfPlane, 1 / 3 ≤ a.im → ‖E4Fun a - 1‖ ≤ C1 * ‖qParamFun a‖)
    (hE6 : ∀ a : UpperHalfPlane, 1 / 3 ≤ a.im → ‖E6Fun a - 1‖ ≤ C1 * ‖qParamFun a‖)
    (hσ : ∀ a : UpperHalfPlane, 1 / 3 ≤ a.im → ‖E4Fun a - E2Fun a ^ 2‖ ≤ Cc * ‖qParamFun a‖)
    (hε : ∀ a : UpperHalfPlane, 1 / 3 ≤ a.im → ‖E2Fun a * E6Fun a - E4Fun a ^ 2‖ ≤ Cc * ‖qParamFun a‖)
    (hη : ∀ a : UpperHalfPlane, 1 / 3 ≤ a.im → ‖E2Fun a * E4Fun a - E6Fun a‖ ≤ Cc * ‖qParamFun a‖)
    (a : UpperHalfPlane) (ha : 1 / 3 ≤ a.im) :
    ‖E2Fun a‖ ≤ 1 + C1 ∧ ‖E4Fun a‖ ≤ 1 + C1 ∧ ‖E6Fun a‖ ≤ 1 + C1 ∧
      ‖E2Fun a ^ 2 - 1‖ ≤ C1 * (2 + C1) * ‖qParamFun a‖ ∧
      ‖phi0 a‖ ≤ (4 + C1) * (1 + ‖(a : ℂ)‖) ∧
      ‖phi2 a‖ ≤ ((1 + C1) ^ 2 + 6 * (1 + C1)) * (1 + ‖(a : ℂ)‖) ∧
      ‖phi8 a‖ ≤ Cc * (11 + 2 * C1) * (1 + ‖(a : ℂ)‖) * ‖qParamFun a‖ := by
  have hqa0 : (0 : ℝ) ≤ ‖qParamFun a‖ := norm_nonneg _
  have hqa1 : ‖qParamFun a‖ ≤ 1 := le_trans (norm_qParam_le_third ha) (by norm_num)
  have hE2a := hE2 a ha
  have hE4a := hE4 a ha
  have hE6a := hE6 a ha
  have hσa := hσ a ha
  have hεa := hε a ha
  have hηa := hη a ha
  have hE2b : ‖E2Fun a‖ ≤ 1 + C1 := by
    have h := norm_add_le (E2Fun a - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    calc ‖E2Fun a‖ ≤ ‖E2Fun a - 1‖ + 1 := h
      _ ≤ C1 * ‖qParamFun a‖ + 1 := by linarith
      _ ≤ C1 + 1 := by nlinarith [hqa1, hqa0, hC1.le]
      _ = 1 + C1 := by ring
  have hE4b : ‖E4Fun a‖ ≤ 1 + C1 := by
    have h := norm_add_le (E4Fun a - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    calc ‖E4Fun a‖ ≤ ‖E4Fun a - 1‖ + 1 := h
      _ ≤ C1 * ‖qParamFun a‖ + 1 := by linarith
      _ ≤ C1 + 1 := by nlinarith [hqa1, hqa0, hC1.le]
      _ = 1 + C1 := by ring
  have hE6b : ‖E6Fun a‖ ≤ 1 + C1 := by
    have h := norm_add_le (E6Fun a - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    calc ‖E6Fun a‖ ≤ ‖E6Fun a - 1‖ + 1 := h
      _ ≤ C1 * ‖qParamFun a‖ + 1 := by linarith
      _ ≤ C1 + 1 := by nlinarith [hqa1, hqa0, hC1.le]
      _ = 1 + C1 := by ring
  have hE2sq : ‖E2Fun a ^ 2 - 1‖ ≤ C1 * (2 + C1) * ‖qParamFun a‖ := by
    have hfac : E2Fun a ^ 2 - 1 = (E2Fun a - 1) * (E2Fun a + 1) := by ring
    rw [hfac, norm_mul]
    have h1 : ‖E2Fun a + 1‖ ≤ 2 + C1 := by
      have h := norm_add_le (E2Fun a) (1 : ℂ)
      rw [norm_one] at h
      linarith [hE2b]
    calc ‖E2Fun a - 1‖ * ‖E2Fun a + 1‖ ≤ (C1 * ‖qParamFun a‖) * (2 + C1) :=
          mul_le_mul hE2a h1 (norm_nonneg _) (by positivity)
      _ = C1 * (2 + C1) * ‖qParamFun a‖ := by ring
  have h3pi : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    have h1 : ‖(3 : ℂ) * Complex.I‖ = 3 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    have h2 : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [norm_div, h1, h2]
  have h6pi : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    have h1 : ‖(6 : ℂ) * Complex.I‖ = 6 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    have h2 : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [norm_div, h1, h2]
  have hphi0a : ‖phi0 a‖ ≤ (4 + C1) * (1 + ‖(a : ℂ)‖) := by
    rw [show phi0 a = (a : ℂ) * E2Fun a - 3 * Complex.I / (Real.pi : ℂ) from rfl]
    calc ‖(a : ℂ) * E2Fun a - 3 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(a : ℂ) * E2Fun a‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ * (1 + C1) + 3 / Real.pi := by
          rw [h3pi]
          exact add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hE2b (norm_nonneg _))
            le_rfl
      _ ≤ (4 + C1) * (1 + ‖(a : ℂ)‖) := by
          nlinarith [norm_nonneg (a : ℂ), three_div_pi_le, hC1.le]
  have hphi2a : ‖phi2 a‖ ≤ ((1 + C1) ^ 2 + 6 * (1 + C1)) * (1 + ‖(a : ℂ)‖) := by
    rw [show phi2 a = (a : ℂ) * E2Fun a ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun a from rfl]
    calc ‖(a : ℂ) * E2Fun a ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun a‖
        ≤ ‖(a : ℂ) * E2Fun a ^ 2‖ + ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun a‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ * (1 + C1) ^ 2 + (6 / Real.pi) * (1 + C1) := by
          have hsq : ‖E2Fun a ^ 2‖ ≤ (1 + C1) ^ 2 := by
            rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE2b 2
          have h6 : ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun a‖ ≤ (6 / Real.pi) * (1 + C1) := by
            rw [norm_mul, h6pi]
            exact mul_le_mul_of_nonneg_left hE2b (by positivity)
          exact add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)) h6
      _ ≤ ((1 + C1) ^ 2 + 6 * (1 + C1)) * (1 + ‖(a : ℂ)‖) := by
          have h6 := six_div_pi_le
          have h6' : (6 / Real.pi) * (1 + C1) ≤ 6 * (1 + C1) :=
            mul_le_mul_of_nonneg_right h6 (by linarith)
          nlinarith [norm_nonneg (a : ℂ), h6', hC1.le]
  have hphi8a : ‖phi8 a‖ ≤ Cc * (11 + 2 * C1) * (1 + ‖(a : ℂ)‖) * ‖qParamFun a‖ := by
    rw [phi8_eq a]
    have hK00a : ‖phi0 a - 3 * Complex.I / (Real.pi : ℂ)‖ ≤ (10 + C1) * (1 + ‖(a : ℂ)‖) := by
      calc ‖phi0 a - 3 * Complex.I / (Real.pi : ℂ)‖
          ≤ ‖phi0 a‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
        _ ≤ (4 + C1) * (1 + ‖(a : ℂ)‖) + 3 / Real.pi := by rw [h3pi]; linarith
        _ ≤ (10 + C1) * (1 + ‖(a : ℂ)‖) := by
            nlinarith [norm_nonneg (a : ℂ), three_div_pi_le, hC1.le]
    calc ‖(phi0 a - 3 * Complex.I / (Real.pi : ℂ)) * (E2Fun a * E6Fun a - E4Fun a ^ 2)
            - (a : ℂ) * E4Fun a * (E2Fun a * E4Fun a - E6Fun a)‖
        ≤ ‖(phi0 a - 3 * Complex.I / (Real.pi : ℂ)) * (E2Fun a * E6Fun a - E4Fun a ^ 2)‖
            + ‖(a : ℂ) * E4Fun a * (E2Fun a * E4Fun a - E6Fun a)‖ := norm_sub_le _ _
      _ ≤ ((10 + C1) * (1 + ‖(a : ℂ)‖)) * (Cc * ‖qParamFun a‖)
            + (‖(a : ℂ)‖ * (1 + C1)) * (Cc * ‖qParamFun a‖) :=
          add_le_add
            (nmul2 (A := (10 + C1) * (1 + ‖(a : ℂ)‖)) (B := Cc * ‖qParamFun a‖)
              (by positivity) (by positivity) hK00a hεa)
            (nmul3 (A := ‖(a : ℂ)‖) (B := 1 + C1) (C := Cc * ‖qParamFun a‖)
              (norm_nonneg _) (by positivity) (by positivity) le_rfl hE4b hηa)
      _ ≤ Cc * (11 + 2 * C1) * (1 + ‖(a : ℂ)‖) * ‖qParamFun a‖ := by
          have hL : 0 ≤ Cc * ‖qParamFun a‖ := mul_nonneg hCc.le hqa0
          have hbr : (10 + C1) * (1 + ‖(a : ℂ)‖) + ‖(a : ℂ)‖ * (1 + C1)
              ≤ (11 + 2 * C1) * (1 + ‖(a : ℂ)‖) := by
            nlinarith [norm_nonneg (a : ℂ), hC1.le]
          have hmul := mul_le_mul_of_nonneg_right hbr hL
          calc (10 + C1) * (1 + ‖(a : ℂ)‖) * (Cc * ‖qParamFun a‖)
                + ‖(a : ℂ)‖ * (1 + C1) * (Cc * ‖qParamFun a‖)
              = ((10 + C1) * (1 + ‖(a : ℂ)‖) + ‖(a : ℂ)‖ * (1 + C1)) * (Cc * ‖qParamFun a‖) := by ring
            _ ≤ ((11 + 2 * C1) * (1 + ‖(a : ℂ)‖)) * (Cc * ‖qParamFun a‖) := hmul
            _ = Cc * (11 + 2 * C1) * (1 + ‖(a : ℂ)‖) * ‖qParamFun a‖ := by ring
  exact ⟨hE2b, hE4b, hE6b, hE2sq, hphi0a, hphi2a, hphi8a⟩

/-- `Ξ₈(τ,z)` is bounded by `C (1+‖τ‖) e^{-π Im z}` for `Im τ ≥ 1/2`, `Im z ≥ 1/3`. -/
theorem Xi8_bound_half :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), 1 / 2 ≤ τ.im → 1 / 3 ≤ z.im →
      ‖Xi8 τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨C1, hC1, hE2f, hE4f, hE6f, hDqf⟩ := ZAtomsThird.first_order
  obtain ⟨Cc, hCc, hσf, hεf, hηf, hRf⟩ := ZAtomsThird.cusp_forms
  obtain ⟨cΔ, hcΔ, hΔlowf⟩ := delta_lower_third
  obtain ⟨CΔu, hCΔu, hΔupf⟩ := delta_upper_third
  set B : ℝ := 1 + C1 with hB
  have hBpos : 0 < B := by rw [hB]; linarith
  set K0 : ℝ := 4 + C1 with hK0
  have hK0pos : 0 < K0 := by rw [hK0]; linarith
  set K8 : ℝ := Cc * (11 + 2 * C1) with hK8
  have hK8pos : 0 < K8 := by rw [hK8]; positivity
  set Cx : ℝ := CΔu * B ^ 2 * K8 / cΔ + B ^ 3 * Cc + 2 * B ^ 2 * Cc * K0 with hCx
  have hCxpos : 0 < Cx := by rw [hCx]; positivity
  refine ⟨Cx, hCxpos, ?_⟩
  intro τ z hτ hz
  have hτ3 : 1 / 3 ≤ τ.im := by linarith
  obtain ⟨hE2τ, hE4τ, hE6τ, hE2sqτ, hphi0τ, hphi2τ, hphi8τ⟩ :=
      atom_bounds C1 Cc hC1 hCc hE2f hE4f hE6f hσf hεf hηf τ hτ3
  obtain ⟨hE2z, hE4z, hE6z, hE2sqz, hphi0z, hphi2z, hphi8z⟩ :=
      atom_bounds C1 Cc hC1 hCc hE2f hE4f hE6f hσf hεf hηf z hz
  have hE4τB : ‖E4Fun τ‖ ≤ B := by rw [hB]; exact hE4τ
  have hE6τB : ‖E6Fun τ‖ ≤ B := by rw [hB]; exact hE6τ
  have hE4zB : ‖E4Fun z‖ ≤ B := by rw [hB]; exact hE4z
  have hK0τ : ‖phi0 τ‖ ≤ K0 * (1 + ‖(τ : ℂ)‖) := by rw [hK0]; exact hphi0τ
  have hK8τ : ‖phi8 τ‖ ≤ K8 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by rw [hK8]; exact hphi8τ
  have hqτ0 : 0 ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hqz0 : 0 ≤ ‖qParamFun z‖ := norm_nonneg _
  have hqτpos : 0 < ‖qParamFun τ‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hσz : ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cc * ‖qParamFun z‖ := hσf z hz
  have hεz : ‖E2Fun z * E6Fun z - E4Fun z ^ 2‖ ≤ Cc * ‖qParamFun z‖ := hεf z hz
  have hΔτlow : cΔ * ‖qParamFun τ‖ ≤ ‖DeltaFun τ‖ := hΔlowf τ hτ3
  have hΔzup : ‖DeltaFun z‖ ≤ CΔu * ‖qParamFun z‖ := hΔupf z hz
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  rw [Xi8_cancelled τ z hDt hDz]
  have h1 : ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
      ≤ CΔu * B ^ 2 * K8 / cΔ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have hdiv : ‖DeltaFun z / DeltaFun τ‖ ≤ CΔu * ‖qParamFun z‖ / (cΔ * ‖qParamFun τ‖) := by
      rw [norm_div]
      have hpos : 0 < cΔ * ‖qParamFun τ‖ := mul_pos hcΔ hqτpos
      calc ‖DeltaFun z‖ / ‖DeltaFun τ‖ ≤ (CΔu * ‖qParamFun z‖) / ‖DeltaFun τ‖ :=
            div_le_div_of_nonneg_right hΔzup (norm_nonneg _)
        _ ≤ (CΔu * ‖qParamFun z‖) / (cΔ * ‖qParamFun τ‖) :=
            div_le_div_of_nonneg_left (by positivity) hpos hΔτlow
    have h4τ : ‖E4Fun τ ^ 2‖ ≤ B * B := by
      rw [norm_pow, pow_two]
      exact mul_le_mul hE4τB hE4τB (norm_nonneg _) hBpos.le
    calc ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ‖
        ≤ (CΔu * ‖qParamFun z‖ / (cΔ * ‖qParamFun τ‖)) * (B * B)
            * (K8 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) :=
          nmul3 (A := CΔu * ‖qParamFun z‖ / (cΔ * ‖qParamFun τ‖)) (B := B * B)
            (C := K8 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
            (by positivity) (by positivity) (by positivity) hdiv h4τ hK8τ
      _ = CΔu * B ^ 2 * K8 / cΔ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
          field_simp
  have h2 : ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
      ≤ B ^ 3 * Cc * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    have h4z : ‖E4Fun z ^ 2‖ ≤ B * B := by
      rw [norm_pow, pow_two]
      exact mul_le_mul hE4zB hE4zB (norm_nonneg _) hBpos.le
    calc ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
        ≤ (1 + ‖(τ : ℂ)‖) * B * (B * B) * (Cc * ‖qParamFun z‖) :=
          nmul4 (A := 1 + ‖(τ : ℂ)‖) (B := B) (C := B * B) (D := Cc * ‖qParamFun z‖)
            (by positivity) (by positivity) (by positivity) (by positivity)
            (by linarith [norm_nonneg (τ : ℂ)]) hE6τB h4z hσz
      _ = B ^ 3 * Cc * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have h3 : ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
      ≤ 2 * B ^ 2 * Cc * K0 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    calc ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
        ≤ 2 * (K0 * (1 + ‖(τ : ℂ)‖)) * B * B * (Cc * ‖qParamFun z‖) :=
          nmul5 (A := 2) (B := K0 * (1 + ‖(τ : ℂ)‖)) (C := B) (D := B)
            (E := Cc * ‖qParamFun z‖)
            (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
            (by norm_num) hK0τ hE4τB hE4zB hεz
      _ = 2 * B ^ 2 * Cc * K0 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have htot : ‖DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
        - (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)
        - 2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
      ≤ Cx * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    rw [hCx]
    have e : (CΔu * B ^ 2 * K8 / cΔ + B ^ 3 * Cc + 2 * B ^ 2 * Cc * K0)
          * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
        = CΔu * B ^ 2 * K8 / cΔ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + B ^ 3 * Cc * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + 2 * B ^ 2 * Cc * K0 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
    rw [e]
    have a1 := norm_sub_le (DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
        - (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2))
        (2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2))
    have a2 := norm_sub_le (DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ)
        ((τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2))
    linarith [a1, a2, h1, h2, h3,
      norm_nonneg (DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ),
      norm_nonneg ((τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)),
      norm_nonneg (2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2))]
  refine le_trans htot ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCxpos.le (by positivity))
  rw [norm_qParamFun, Real.exp_le_exp]
  nlinarith [Real.pi_pos, z.im_pos]

/-- `Ξ₂₄(τ,z)` is bounded by `C (1+‖τ‖) e^{-π Im z}` for `Im τ ≥ 1/2`, `Im z ≥ 1/3`. -/
theorem Xi24_bound_half :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), 1 / 2 ≤ τ.im → 1 / 3 ≤ z.im →
      ‖Xi24 τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨C1, hC1, hE2f, hE4f, hE6f, hDqf⟩ := ZAtomsThird.first_order
  obtain ⟨Cc, hCc, hσf, hεf, hηf, hRf⟩ := ZAtomsThird.cusp_forms
  obtain ⟨cΔ, hcΔ, hΔlowf⟩ := delta_lower_third
  obtain ⟨CΔu, hCΔu, hΔupf⟩ := delta_upper_third
  obtain ⟨Cjz, hCjz, hjzf⟩ := jz_sigma_third
  set B : ℝ := 1 + C1 with hB
  have hBpos : 0 < B := by rw [hB]; linarith
  set K0 : ℝ := 4 + C1 with hK0
  have hK0pos : 0 < K0 := by rw [hK0]; linarith
  set K2 : ℝ := (1 + C1) ^ 2 + 6 * (1 + C1) with hK2
  have hK2pos : 0 < K2 := by rw [hK2]; positivity
  set K8 : ℝ := Cc * (11 + 2 * C1) with hK8
  have hK8pos : 0 < K8 := by rw [hK8]; positivity
  set C2sq : ℝ := C1 * (2 + C1) with hC2sq
  have hC2sqpos : 0 < C2sq := by rw [hC2sq]; positivity
  set Cx : ℝ := 6 * B * K8 * (Cc * B ^ 3 / cΔ + Cjz) + 1728 * K0 * B ^ 3 * (5 * Cc + 2 * C2sq)
      + 1728 * B ^ 3 * C2sq + 1728 * K2 * B ^ 2 * C1 + 1728 * K0 * CΔu * Cc * B ^ 2 / cΔ with hCx
  have hCxpos : 0 < Cx := by rw [hCx]; positivity
  refine ⟨Cx, hCxpos, ?_⟩
  intro τ z hτ hz
  have hτ3 : 1 / 3 ≤ τ.im := by linarith
  obtain ⟨hE2τ, hE4τ, hE6τ, hE2sqτ, hphi0τ, hphi2τ, hphi8τ⟩ :=
      atom_bounds C1 Cc hC1 hCc hE2f hE4f hE6f hσf hεf hηf τ hτ3
  obtain ⟨hE2z, hE4z, hE6z, hE2sqz, hphi0z, hphi2z, hphi8z⟩ :=
      atom_bounds C1 Cc hC1 hCc hE2f hE4f hE6f hσf hεf hηf z hz
  have hE4τB : ‖E4Fun τ‖ ≤ B := by rw [hB]; exact hE4τ
  have hE6τB : ‖E6Fun τ‖ ≤ B := by rw [hB]; exact hE6τ
  have hE4zB : ‖E4Fun z‖ ≤ B := by rw [hB]; exact hE4z
  have hK0τ : ‖phi0 τ‖ ≤ K0 * (1 + ‖(τ : ℂ)‖) := by rw [hK0]; exact hphi0τ
  have hK2τ : ‖phi2 τ‖ ≤ K2 * (1 + ‖(τ : ℂ)‖) := by rw [hK2]; exact hphi2τ
  have hK8τ : ‖phi8 τ‖ ≤ K8 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by rw [hK8]; exact hphi8τ
  have hC2sqz : ‖E2Fun z ^ 2 - 1‖ ≤ C2sq * ‖qParamFun z‖ := by rw [hC2sq]; exact hE2sqz
  have hqτ0 : 0 ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hqz0 : 0 ≤ ‖qParamFun z‖ := norm_nonneg _
  have hqτpos : 0 < ‖qParamFun τ‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hqzpos : 0 < ‖qParamFun z‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hqτ1 : ‖qParamFun τ‖ ≤ 1 := le_trans (norm_qParam_le_third hτ3) (by norm_num)
  have hσz : ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cc * ‖qParamFun z‖ := hσf z hz
  have hεz : ‖E2Fun z * E6Fun z - E4Fun z ^ 2‖ ≤ Cc * ‖qParamFun z‖ := hεf z hz
  have hRz : ‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
      ≤ Cc * ‖qParamFun z‖ ^ 2 := hRf z hz
  have hE4m1z : ‖E4Fun z - 1‖ ≤ C1 * ‖qParamFun z‖ := hE4f z hz
  have hΔτlow : cΔ * ‖qParamFun τ‖ ≤ ‖DeltaFun τ‖ := hΔlowf τ hτ3
  have hΔτup : ‖DeltaFun τ‖ ≤ CΔu * ‖qParamFun τ‖ := hΔupf τ hτ3
  have hΔzlow : cΔ * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ := hΔlowf z hz
  have hDt : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hE4zsq : ‖E4Fun z ^ 2‖ ≤ B * B := by
    rw [norm_pow, pow_two]; exact mul_le_mul hE4zB hE4zB (norm_nonneg _) hBpos.le
  have hjτ : ‖jInvariantFun τ‖ ≤ B ^ 3 / (cΔ * ‖qParamFun τ‖) := by
    rw [show jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ from rfl, norm_div, norm_pow]
    have hnum : ‖E4Fun τ‖ ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hE4τB 3
    have hpos : 0 < cΔ * ‖qParamFun τ‖ := mul_pos hcΔ hqτpos
    have hposd : 0 < ‖DeltaFun τ‖ := lt_of_lt_of_le hpos hΔτlow
    calc ‖E4Fun τ‖ ^ 3 / ‖DeltaFun τ‖ ≤ B ^ 3 / ‖DeltaFun τ‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ B ^ 3 / (cΔ * ‖qParamFun τ‖) :=
          div_le_div_of_nonneg_left (by positivity) hpos hΔτlow
  rw [Xi24_cancelled τ z hDt hDz]
  set tA : ℂ := 6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
      * (jInvariantFun τ - jInvariantFun z) with htA
  set tB : ℂ := 1728 * E4Fun τ * phi8 τ with htB
  set tC : ℂ := 1728 * phi0 τ * E4Fun τ ^ 3
      * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)) with htC
  set tD : ℂ := 1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1) with htD
  set tE : ℂ := 1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1) with htE
  set tF : ℂ := 1728 * phi0 τ * DeltaFun τ
      * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
      * E4Fun z ^ 2 / DeltaFun z with htF
  have hAB : ‖tA + tB‖
      ≤ (6 * B * K8 * (Cc * B ^ 3 / cΔ + Cjz)) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    rw [htA, htB]
    have heq : 6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2)
          * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun τ * phi8 τ
        = 6 * E4Fun τ * phi8 τ
          * ((E4Fun z - E2Fun z ^ 2) * (jInvariantFun τ - jInvariantFun z) + 288) := by ring
    rw [heq]
    have hinner : ‖(E4Fun z - E2Fun z ^ 2) * (jInvariantFun τ - jInvariantFun z) + 288‖
        ≤ Cc * ‖qParamFun z‖ * (B ^ 3 / (cΔ * ‖qParamFun τ‖)) + Cjz * ‖qParamFun z‖ := by
      have hsplit : (E4Fun z - E2Fun z ^ 2) * (jInvariantFun τ - jInvariantFun z) + 288
          = (E4Fun z - E2Fun z ^ 2) * jInvariantFun τ
            - (jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288) := by ring
      rw [hsplit]
      have h1 : ‖(E4Fun z - E2Fun z ^ 2) * jInvariantFun τ‖
          ≤ Cc * ‖qParamFun z‖ * (B ^ 3 / (cΔ * ‖qParamFun τ‖)) := by
        rw [norm_mul]
        exact mul_le_mul hσz hjτ (norm_nonneg _) (by positivity)
      have h2 : ‖jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288‖ ≤ Cjz * ‖qParamFun z‖ :=
        hjzf z hz
      calc ‖(E4Fun z - E2Fun z ^ 2) * jInvariantFun τ
              - (jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288)‖
          ≤ ‖(E4Fun z - E2Fun z ^ 2) * jInvariantFun τ‖
            + ‖jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288‖ := norm_sub_le _ _
        _ ≤ Cc * ‖qParamFun z‖ * (B ^ 3 / (cΔ * ‖qParamFun τ‖)) + Cjz * ‖qParamFun z‖ :=
            add_le_add h1 h2
    have hfac : 6 * B * (K8 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
          * (Cc * ‖qParamFun z‖ * (B ^ 3 / (cΔ * ‖qParamFun τ‖)) + Cjz * ‖qParamFun z‖)
        = 6 * B * K8 * (1 + ‖(τ : ℂ)‖)
          * (Cc * B ^ 3 / cΔ * ‖qParamFun z‖ + Cjz * ‖qParamFun z‖ * ‖qParamFun τ‖) := by
        field_simp
    calc ‖6 * E4Fun τ * phi8 τ
            * ((E4Fun z - E2Fun z ^ 2) * (jInvariantFun τ - jInvariantFun z) + 288)‖
        ≤ 6 * B * (K8 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
            * (Cc * ‖qParamFun z‖ * (B ^ 3 / (cΔ * ‖qParamFun τ‖)) + Cjz * ‖qParamFun z‖) :=
          nmul4 (A := 6) (B := B) (C := K8 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
            (D := Cc * ‖qParamFun z‖ * (B ^ 3 / (cΔ * ‖qParamFun τ‖)) + Cjz * ‖qParamFun z‖)
            (by norm_num) (by positivity) (by positivity) (by positivity)
            (by norm_num) hE4τB hK8τ hinner
      _ ≤ (6 * B * K8 * (Cc * B ^ 3 / cΔ + Cjz)) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
          rw [hfac]
          have h1 : Cjz * ‖qParamFun z‖ * ‖qParamFun τ‖ ≤ Cjz * ‖qParamFun z‖ := by
            calc Cjz * ‖qParamFun z‖ * ‖qParamFun τ‖ = Cjz * ‖qParamFun τ‖ * ‖qParamFun z‖ := by ring
              _ ≤ Cjz * 1 * ‖qParamFun z‖ := by
                  apply mul_le_mul_of_nonneg_right _ hqz0
                  exact mul_le_mul_of_nonneg_left hqτ1 hCjz.le
              _ = Cjz * ‖qParamFun z‖ := by ring
          have h2 : Cc * B ^ 3 / cΔ * ‖qParamFun z‖ + Cjz * ‖qParamFun z‖ * ‖qParamFun τ‖
              ≤ (Cc * B ^ 3 / cΔ + Cjz) * ‖qParamFun z‖ := by
            have he : (Cc * B ^ 3 / cΔ + Cjz) * ‖qParamFun z‖
                = Cc * B ^ 3 / cΔ * ‖qParamFun z‖ + Cjz * ‖qParamFun z‖ := by ring
            rw [he]
            linarith [h1]
          calc 6 * B * K8 * (1 + ‖(τ : ℂ)‖)
                * (Cc * B ^ 3 / cΔ * ‖qParamFun z‖ + Cjz * ‖qParamFun z‖ * ‖qParamFun τ‖)
              ≤ 6 * B * K8 * (1 + ‖(τ : ℂ)‖) * ((Cc * B ^ 3 / cΔ + Cjz) * ‖qParamFun z‖) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = (6 * B * K8 * (Cc * B ^ 3 / cΔ + Cjz)) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have hC : ‖tC‖
      ≤ (1728 * K0 * B ^ 3 * (5 * Cc + 2 * C2sq)) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    rw [htC]
    have hE4c : ‖E4Fun τ ^ 3‖ ≤ B ^ 3 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4τB 3
    have hbr : ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
        ≤ (5 * Cc + 2 * C2sq) * ‖qParamFun z‖ := by
      have h5 : ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ ≤ 5 * Cc * ‖qParamFun z‖ := by
        rw [norm_mul, Complex.norm_ofNat]
        calc (5 : ℝ) * ‖E4Fun z - E2Fun z ^ 2‖ ≤ 5 * (Cc * ‖qParamFun z‖) :=
              mul_le_mul_of_nonneg_left hσz (by norm_num)
          _ = 5 * Cc * ‖qParamFun z‖ := by ring
      have h2 : ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ ≤ 2 * C2sq * ‖qParamFun z‖ := by
        rw [norm_mul, Complex.norm_ofNat]
        calc (2 : ℝ) * ‖E2Fun z ^ 2 - 1‖ ≤ 2 * (C2sq * ‖qParamFun z‖) :=
              mul_le_mul_of_nonneg_left hC2sqz (by norm_num)
          _ = 2 * C2sq * ‖qParamFun z‖ := by ring
      calc ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
          ≤ ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ + ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ :=
            norm_sub_le _ _
        _ ≤ 5 * Cc * ‖qParamFun z‖ + 2 * C2sq * ‖qParamFun z‖ := add_le_add h5 h2
        _ = (5 * Cc + 2 * C2sq) * ‖qParamFun z‖ := by ring
    calc ‖1728 * phi0 τ * E4Fun τ ^ 3
            * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))‖
        ≤ 1728 * (K0 * (1 + ‖(τ : ℂ)‖)) * B ^ 3 * ((5 * Cc + 2 * C2sq) * ‖qParamFun z‖) :=
          nmul4 (A := 1728) (B := K0 * (1 + ‖(τ : ℂ)‖)) (C := B ^ 3)
            (D := (5 * Cc + 2 * C2sq) * ‖qParamFun z‖)
            (by norm_num) (by positivity) (by positivity) (by positivity)
            (by norm_num) hK0τ hE4c hbr
      _ = (1728 * K0 * B ^ 3 * (5 * Cc + 2 * C2sq)) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have hD : ‖tD‖ ≤ (1728 * B ^ 3 * C2sq) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    rw [htD]
    have hE4d : ‖E4Fun τ ^ 2‖ ≤ B * B := by
      rw [norm_pow, pow_two]; exact mul_le_mul hE4τB hE4τB (norm_nonneg _) hBpos.le
    calc ‖1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)‖
        ≤ 1728 * (1 + ‖(τ : ℂ)‖) * (B * B) * B * (C2sq * ‖qParamFun z‖) :=
          nmul5 (A := 1728) (B := 1 + ‖(τ : ℂ)‖) (C := B * B) (D := B)
            (E := C2sq * ‖qParamFun z‖)
            (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
            (by norm_num) (by linarith [norm_nonneg (τ : ℂ)]) hE4d hE6τB hC2sqz
      _ = (1728 * B ^ 3 * C2sq) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have hE : ‖tE‖ ≤ (1728 * K2 * B ^ 2 * C1) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    rw [htE]
    calc ‖1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)‖
        ≤ 1728 * (K2 * (1 + ‖(τ : ℂ)‖)) * B * B * (C1 * ‖qParamFun z‖) :=
          nmul5 (A := 1728) (B := K2 * (1 + ‖(τ : ℂ)‖)) (C := B) (D := B)
            (E := C1 * ‖qParamFun z‖)
            (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
            (by norm_num) hK2τ hE4τB hE6τB hE4m1z
      _ = (1728 * K2 * B ^ 2 * C1) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have hF : ‖tF‖ ≤ (1728 * K0 * CΔu * Cc * B ^ 2 / cΔ) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    rw [htF, norm_div]
    have hnum : ‖1728 * phi0 τ * DeltaFun τ
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2‖
        ≤ 1728 * (K0 * (1 + ‖(τ : ℂ)‖)) * (CΔu * ‖qParamFun τ‖) * (Cc * ‖qParamFun z‖ ^ 2)
          * (B * B) :=
          nmul5 (A := 1728) (B := K0 * (1 + ‖(τ : ℂ)‖)) (C := CΔu * ‖qParamFun τ‖)
            (D := Cc * ‖qParamFun z‖ ^ 2) (E := B * B)
            (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
            (by norm_num) hK0τ hΔτup hRz hE4zsq
    have hpos : 0 < cΔ * ‖qParamFun z‖ := mul_pos hcΔ hqzpos
    have hstep : ‖1728 * phi0 τ * DeltaFun τ
            * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2‖ / ‖DeltaFun z‖
        ≤ (1728 * (K0 * (1 + ‖(τ : ℂ)‖)) * (CΔu * ‖qParamFun τ‖) * (Cc * ‖qParamFun z‖ ^ 2)
            * (B * B)) / (cΔ * ‖qParamFun z‖) := by
      calc _ ≤ (1728 * (K0 * (1 + ‖(τ : ℂ)‖)) * (CΔu * ‖qParamFun τ‖)
            * (Cc * ‖qParamFun z‖ ^ 2) * (B * B)) / ‖DeltaFun z‖ :=
            div_le_div_of_nonneg_right hnum (norm_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hpos hΔzlow
    refine le_trans hstep ?_
    have heq : (1728 * (K0 * (1 + ‖(τ : ℂ)‖)) * (CΔu * ‖qParamFun τ‖)
            * (Cc * ‖qParamFun z‖ ^ 2) * (B * B)) / (cΔ * ‖qParamFun z‖)
        = (1728 * K0 * CΔu * Cc * B ^ 2 / cΔ) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖
          * ‖qParamFun z‖ := by
      field_simp
    rw [heq]
    have h1 : (1728 * K0 * CΔu * Cc * B ^ 2 / cΔ) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖
        ≤ (1728 * K0 * CΔu * Cc * B ^ 2 / cΔ) * (1 + ‖(τ : ℂ)‖) * 1 :=
      mul_le_mul_of_nonneg_left hqτ1 (by positivity)
    calc (1728 * K0 * CΔu * Cc * B ^ 2 / cΔ) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖
          * ‖qParamFun z‖
        ≤ ((1728 * K0 * CΔu * Cc * B ^ 2 / cΔ) * (1 + ‖(τ : ℂ)‖) * 1) * ‖qParamFun z‖ :=
          mul_le_mul_of_nonneg_right h1 hqz0
      _ = (1728 * K0 * CΔu * Cc * B ^ 2 / cΔ) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
  have htot : ‖tA + tB + tC + tD + tE - tF‖ ≤ Cx * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by
    rw [hCx]
    have e : (6 * B * K8 * (Cc * B ^ 3 / cΔ + Cjz) + 1728 * K0 * B ^ 3 * (5 * Cc + 2 * C2sq)
          + 1728 * B ^ 3 * C2sq + 1728 * K2 * B ^ 2 * C1 + 1728 * K0 * CΔu * Cc * B ^ 2 / cΔ)
          * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
        = (6 * B * K8 * (Cc * B ^ 3 / cΔ + Cjz)) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + (1728 * K0 * B ^ 3 * (5 * Cc + 2 * C2sq)) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + (1728 * B ^ 3 * C2sq) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + (1728 * K2 * B ^ 2 * C1) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖
          + (1728 * K0 * CΔu * Cc * B ^ 2 / cΔ) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun z‖ := by ring
    rw [e]
    have a1 := norm_add_le (tA + tB + tC + tD) tE
    have a2 := norm_add_le (tA + tB + tC) tD
    have a3 := norm_add_le (tA + tB) tC
    linarith [norm_sub_le (tA + tB + tC + tD + tE) tF, a1, a2, a3, hAB, hC, hD, hE, hF]
  refine le_trans htot ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCxpos.le (by positivity))
  rw [norm_qParamFun, Real.exp_le_exp]
  nlinarith [Real.pi_pos, z.im_pos]

/-- **Bound for the slashed kernel `K_+` in dimensions `8` and `24`.**

For `τ` in the fundamental domain `𝒟` with `Im τ ≥ 1/2` and `z` with `Im z ≥ 1/3`, the
slashed kernel `z^{d/2-2} K_+^{(d)}(τ, S·z)` is bounded by `(1+‖τ‖)` times the exponential
`e^{-π Im z}` divided by `‖Δ(z)(j(τ)-j(z))‖`.  This is the `z`-cusp decay estimate used to
control the contour integral. -/
theorem KPlus_slash_bound_half (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (τ z : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im → 1 / 3 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ ((d : ℤ) / 2 - 2) * Work.Kernels.KPlus d τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  rcases hd with rfl | rfl
  · obtain ⟨C8, hC8, hX8⟩ := Xi8_bound_half
    set c8 : ℂ := (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hc8def
    refine ⟨C8 / ‖c8‖ + 1, 1, ?_, by norm_num, ?_⟩
    · have h := div_nonneg hC8.le (norm_nonneg c8); linarith
    intro τ z hD hτ2 hz hne
    have hτ3 : 1 / 3 ≤ τ.im := by linarith
    have hpow : (z : ℂ) ^ (((8 : ℕ) : ℤ) / 2 - 2) = (z : ℂ) ^ 2 := by
      rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num, _root_.zpow_ofNat]
    have hc8ne : c8 ≠ 0 := by
      rw [hc8def]
      refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
      exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
    have hDz : DeltaFun z * (jInvariantFun τ - jInvariantFun z) ≠ 0 :=
      mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero z) hJ
    have hkey := Xi8_eq τ z hne
    have hK2 : (z : ℂ) ^ 2 * KPlus 8 τ (ModularGroup.S • z)
        = Xi8 τ z / (c8 * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))) := by
      rw [eq_div_iff (mul_ne_zero hc8ne hDz)]
      rw [mul_comm]
      exact hkey
    rw [hpow, hK2, Real.rpow_one, norm_div, norm_mul]
    have hden0 : (0 : ℝ) < ‖c8‖ * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
      mul_pos (norm_pos_iff.mpr hc8ne) (norm_pos_iff.mpr hDz)
    have hXi := hX8 τ z hτ2 hz
    have hCpos : (0 : ℝ) < C8 / ‖c8‖ + 1 := by
      have h := div_nonneg hC8.le (norm_nonneg c8); linarith
    have hE0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)) := by positivity
    calc ‖Xi8 τ z‖ / (‖c8‖ * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖)
        ≤ (C8 * (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)))
            / (‖c8‖ * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖) :=
          div_le_div_of_nonneg_right hXi hden0.le
      _ = (C8 / ‖c8‖) * ((1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)))
            / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by ring
      _ ≤ (C8 / ‖c8‖ + 1) * ((1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)))
            / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) hE0) (norm_nonneg _)
      _ = (C8 / ‖c8‖ + 1) * (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im))
            / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by ring
  · obtain ⟨C24, hC24, hX24⟩ := Xi24_bound_half
    set c24 : ℂ := (36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hc24def
    refine ⟨C24 / ‖c24‖ + 1, 1, ?_, by norm_num, ?_⟩
    · have h := div_nonneg hC24.le (norm_nonneg c24); linarith
    intro τ z hD hτ2 hz hne
    have hτ3 : 1 / 3 ≤ τ.im := by linarith
    have hpow : (z : ℂ) ^ (((24 : ℕ) : ℤ) / 2 - 2) = (z : ℂ) ^ 10 := by
      rw [show (((24 : ℕ) : ℤ) / 2 - 2) = (10 : ℤ) by norm_num, _root_.zpow_ofNat]
    have hc24ne : c24 ≠ 0 := by
      rw [hc24def]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (by simp [Work.Kernels.c1728])) ?_) Complex.I_ne_zero
      exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
    have hDz : DeltaFun z * (jInvariantFun τ - jInvariantFun z) ≠ 0 :=
      mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero z) hJ
    have hkey := Xi24_eq τ z hne
    have hK10 : (z : ℂ) ^ 10 * KPlus 24 τ (ModularGroup.S • z)
        = Xi24 τ z / (c24 * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))) := by
      rw [eq_div_iff (mul_ne_zero hc24ne hDz)]
      rw [mul_comm]
      exact hkey
    rw [hpow, hK10, Real.rpow_one, norm_div, norm_mul]
    have hden0 : (0 : ℝ) < ‖c24‖ * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
      mul_pos (norm_pos_iff.mpr hc24ne) (norm_pos_iff.mpr hDz)
    have hXi := hX24 τ z hτ2 hz
    have hE0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)) := by positivity
    calc ‖Xi24 τ z‖ / (‖c24‖ * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖)
        ≤ (C24 * (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)))
            / (‖c24‖ * ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖) :=
          div_le_div_of_nonneg_right hXi hden0.le
      _ = (C24 / ‖c24‖) * ((1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)))
            / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by ring
      _ ≤ (C24 / ‖c24‖ + 1) * ((1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)))
            / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) hE0) (norm_nonneg _)
      _ = (C24 / ‖c24‖ + 1) * (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im))
            / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by ring

end

end Work.Asymptotics
