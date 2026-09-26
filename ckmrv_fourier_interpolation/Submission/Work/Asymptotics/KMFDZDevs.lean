import Mathlib
import Submission.Work.Asymptotics.KMFDDefs

set_option maxHeartbeats 2000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels
open Work.Residues (Ept)

noncomputable section

/-! ## Elementary facts about `Ept z` -/

private lemma kmfd_norm_Ept_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])

private lemma kmfd_q_eq (z : ℍ) : qParamFun z = (Ept z) ^ 2 :=
  Compact.qParamFun_eq_Ept_sq z

private lemma kmfd_norm_q_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖qParamFun z‖ ≤ 1 := by
  rw [kmfd_q_eq, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (kmfd_norm_Ept_le_one hz)

private lemma kmfd_norm_q_sq (z : ℍ) : ‖qParamFun z‖ ^ 2 = ‖Ept z‖ ^ 4 := by
  rw [kmfd_q_eq, norm_pow, ← pow_mul]

private lemma kmfd_norm_q2 (z : ℍ) : ‖qParamFun z ^ 2‖ = ‖Ept z‖ ^ 4 := by
  rw [norm_pow, kmfd_q_eq, norm_pow, ← pow_mul]

private lemma kmfd_sum3_le {a₁ a₂ a₃ : ℂ} {A₁ A₂ A₃ : ℝ}
    (h1 : ‖a₁‖ ≤ A₁) (h2 : ‖a₂‖ ≤ A₂) (h3 : ‖a₃‖ ≤ A₃) :
    ‖a₁ + a₂ + a₃‖ ≤ A₁ + A₂ + A₃ := by
  have h12 : ‖a₁ + a₂‖ ≤ A₁ + A₂ := by linarith [norm_add_le a₁ a₂, h1, h2]
  linarith [norm_add_le (a₁ + a₂) a₃, h3]

/-! ## The `z`-atom deviations -/

private lemma kmfd_dDelta_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dDelta z‖ ≤ C * ‖Ept z‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_invDelta
  exact ⟨C, hC, fun z hz => by
    simpa [Compact.dDelta, Compact.Dref, Compact.einv2] using h z hz⟩

private lemma kmfd_dW_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dW z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_W_second
  exact ⟨C, hC, fun z hz => by simpa [Compact.dW, Compact.Wref] using h z hz⟩

private lemma kmfd_dD2_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dD2 z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_D_second
  exact ⟨C, hC, fun z hz => by simpa [Compact.dD2, Compact.D2ref] using h z hz⟩

private lemma kmfd_dL_le (ℓ : LogLambdaData) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dL ℓ z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Compact.cuspC_spec ℓ
  exact ⟨C, hC, fun z hz => by simpa [Compact.dL, Compact.Lref, Compact.Xc] using h z hz⟩

/-- `‖E₄ z‖ ≤ 1 + 240 + C` for `Im z ≥ 1`. -/
private lemma kmfd_E4_bdd {C4 : ℝ} (hC4 : 0 < C4) (h4 : ∀ z : ℍ, 1 ≤ z.im →
      ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ C4 * ‖qParamFun z‖ ^ 2)
    {z : ℍ} (hz : 1 ≤ z.im) : ‖E4Fun z‖ ≤ 1 + 240 + C4 := by
  have h := h4 z hz
  have hq := kmfd_norm_q_le_one hz
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ 1 := by
    calc ‖qParamFun z‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hq0 hq 2
      _ = 1 := by norm_num
  have hsplit : E4Fun z = (E4Fun z - 1 - 240 * qParamFun z) + (1 + 240 * qParamFun z) := by ring
  have h1 : ‖1 + 240 * qParamFun z‖ ≤ 1 + 240 := by
    have h2 := norm_add_le (1 : ℂ) (240 * qParamFun z)
    rw [norm_one, norm_mul, show ‖(240 : ℂ)‖ = 240 by norm_num] at h2
    calc ‖1 + 240 * qParamFun z‖ ≤ 1 + 240 * ‖qParamFun z‖ := h2
      _ ≤ 1 + 240 := by linarith
  rw [hsplit]
  have hna1 := norm_add_le (E4Fun z - 1 - 240 * qParamFun z) (1 + 240 * qParamFun z)
  have h12 : ‖(E4Fun z - 1 - 240 * qParamFun z) + (1 + 240 * qParamFun z)‖
      ≤ C4 * ‖qParamFun z‖ ^ 2 + (1 + 240) := by linarith [hna1, h, h1]
  have h3 : C4 * ‖qParamFun z‖ ^ 2 ≤ C4 := by
    calc C4 * ‖qParamFun z‖ ^ 2 ≤ C4 * 1 := mul_le_mul_of_nonneg_left hq2 hC4.le
      _ = C4 := mul_one C4
  linarith [h12, h3]

/-- `‖E₆ z‖ ≤ 1 + 504 + C` for `Im z ≥ 1`. -/
private lemma kmfd_E6_bdd {C6 : ℝ} (hC6 : 0 < C6) (h6 : ∀ z : ℍ, 1 ≤ z.im →
      ‖E6Fun z - 1 + 504 * qParamFun z‖ ≤ C6 * ‖qParamFun z‖ ^ 2)
    {z : ℍ} (hz : 1 ≤ z.im) : ‖E6Fun z‖ ≤ 1 + 504 + C6 := by
  have h := h6 z hz
  have hq := kmfd_norm_q_le_one hz
  have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ 1 := by
    calc ‖qParamFun z‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hq0 hq 2
      _ = 1 := by norm_num
  have hsplit : E6Fun z = (E6Fun z - 1 + 504 * qParamFun z) + (1 - 504 * qParamFun z) := by ring
  have h1 : ‖1 - 504 * qParamFun z‖ ≤ 1 + 504 := by
    have h2 := norm_sub_le (1 : ℂ) (504 * qParamFun z)
    rw [norm_one, norm_mul, show ‖(504 : ℂ)‖ = 504 by norm_num] at h2
    calc ‖1 - 504 * qParamFun z‖ ≤ 1 + 504 * ‖qParamFun z‖ := h2
      _ ≤ 1 + 504 := by linarith
  rw [hsplit]
  have hna2 := norm_add_le (E6Fun z - 1 + 504 * qParamFun z) (1 - 504 * qParamFun z)
  have h12 : ‖(E6Fun z - 1 + 504 * qParamFun z) + (1 - 504 * qParamFun z)‖
      ≤ C6 * ‖qParamFun z‖ ^ 2 + (1 + 504) := by linarith [hna2, h, h1]
  have h3 : C6 * ‖qParamFun z‖ ^ 2 ≤ C6 := by
    calc C6 * ‖qParamFun z‖ ^ 2 ≤ C6 * 1 := mul_le_mul_of_nonneg_left hq2 hC6.le
      _ = C6 := mul_one C6
  linarith [h12, h3]

/-- `dE10 = O(‖Ept z‖⁴)` for `Im z ≥ 1`. -/
private lemma kmfd_dE10_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dE10 z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C4, hC4, h4⟩ := E4Fun_two_term
  obtain ⟨C6, hC6, h6⟩ := E6Fun_two_term
  refine ⟨C6 * (1 + 240 + C4) + C4 * 505 + 120961, by positivity, fun z hz => ?_⟩
  have hq := kmfd_norm_q_le_one hz
  have hE4 : ‖E4Fun z‖ ≤ 1 + 240 + C4 := kmfd_E4_bdd hC4 h4 hz
  have hδ : ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ C4 * ‖Ept z‖ ^ 4 := by
    rw [← kmfd_norm_q_sq]; exact h4 z hz
  have hε : ‖E6Fun z - 1 + 504 * qParamFun z‖ ≤ C6 * ‖Ept z‖ ^ 4 := by
    rw [← kmfd_norm_q_sq]; exact h6 z hz
  have hb : ‖1 - 504 * qParamFun z‖ ≤ 505 := by
    have h2 := norm_sub_le (1 : ℂ) (504 * qParamFun z)
    rw [norm_one, norm_mul, show ‖(504 : ℂ)‖ = 504 by norm_num] at h2
    calc ‖1 - 504 * qParamFun z‖ ≤ 1 + 504 * ‖qParamFun z‖ := h2
      _ ≤ 505 := by linarith
  have hdec : Compact.dE10 z
      = E4Fun z * (E6Fun z - 1 + 504 * qParamFun z)
        + (E4Fun z - 1 - 240 * qParamFun z) * (1 - 504 * qParamFun z)
        - 120960 * qParamFun z ^ 2 := by
    simp only [Compact.dE10, Compact.E10ref, Compact.qParamFun_eq_Ept_sq]
    ring
  have hA : ‖E4Fun z * (E6Fun z - 1 + 504 * qParamFun z)‖
      ≤ (1 + 240 + C4) * (C6 * ‖Ept z‖ ^ 4) := by
    rw [norm_mul]
    exact mul_le_mul hE4 hε (norm_nonneg _) (by positivity)
  have hB : ‖(E4Fun z - 1 - 240 * qParamFun z) * (1 - 504 * qParamFun z)‖
      ≤ C4 * 505 * ‖Ept z‖ ^ 4 := by
    rw [norm_mul]
    calc ‖E4Fun z - 1 - 240 * qParamFun z‖ * ‖1 - 504 * qParamFun z‖
        ≤ (C4 * ‖Ept z‖ ^ 4) * 505 := mul_le_mul hδ hb (norm_nonneg _) (by positivity)
      _ = C4 * 505 * ‖Ept z‖ ^ 4 := by ring
  have hC : ‖(120960 : ℂ) * qParamFun z ^ 2‖ = 120960 * ‖Ept z‖ ^ 4 := by
    rw [norm_mul, show ‖(120960 : ℂ)‖ = 120960 by norm_num, kmfd_norm_q2]
  rw [hdec]
  refine le_trans (norm_sub_le _ _) ?_
  have hna3 := norm_add_le (E4Fun z * (E6Fun z - 1 + 504 * qParamFun z))
    ((E4Fun z - 1 - 240 * qParamFun z) * (1 - 504 * qParamFun z))
  have hsum : ‖E4Fun z * (E6Fun z - 1 + 504 * qParamFun z)
      + (E4Fun z - 1 - 240 * qParamFun z) * (1 - 504 * qParamFun z)‖
      ≤ (1 + 240 + C4) * (C6 * ‖Ept z‖ ^ 4) + C4 * 505 * ‖Ept z‖ ^ 4 := by
    linarith [hna3, hA, hB]
  rw [hC]
  have h0 : (0 : ℝ) ≤ ‖Ept z‖ ^ 4 := by positivity
  linarith [hsum, h0]

/-- `dE14 = O(‖Ept z‖⁴)` for `Im z ≥ 1`. -/
private lemma kmfd_dE14_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖Compact.dE14 z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C4, hC4, h4⟩ := E4Fun_two_term
  obtain ⟨C6, hC6, h6⟩ := E6Fun_two_term
  refine ⟨(1 + 240 + C4) ^ 2 * C6 + (C4 * (1 + 240 + C4 + 241) + 57600) * 505 + 241921,
    by positivity, fun z hz => ?_⟩
  have hq := kmfd_norm_q_le_one hz
  have hE4 : ‖E4Fun z‖ ≤ 1 + 240 + C4 := kmfd_E4_bdd hC4 h4 hz
  have hδ : ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ C4 * ‖Ept z‖ ^ 4 := by
    rw [← kmfd_norm_q_sq]; exact h4 z hz
  have hε : ‖E6Fun z - 1 + 504 * qParamFun z‖ ≤ C6 * ‖Ept z‖ ^ 4 := by
    rw [← kmfd_norm_q_sq]; exact h6 z hz
  have hB1 : ‖1 + 240 * qParamFun z‖ ≤ 241 := by
    have h2 := norm_add_le (1 : ℂ) (240 * qParamFun z)
    rw [norm_one, norm_mul, show ‖(240 : ℂ)‖ = 240 by norm_num] at h2
    calc ‖1 + 240 * qParamFun z‖ ≤ 1 + 240 * ‖qParamFun z‖ := h2
      _ ≤ 241 := by linarith
  have hb : ‖1 - 504 * qParamFun z‖ ≤ 505 := by
    have h2 := norm_sub_le (1 : ℂ) (504 * qParamFun z)
    rw [norm_one, norm_mul, show ‖(504 : ℂ)‖ = 504 by norm_num] at h2
    calc ‖1 - 504 * qParamFun z‖ ≤ 1 + 504 * ‖qParamFun z‖ := h2
      _ ≤ 505 := by linarith
  have hna4 := norm_add_le (E4Fun z) (1 + 240 * qParamFun z)
  have hf : ‖E4Fun z + (1 + 240 * qParamFun z)‖ ≤ 1 + 240 + C4 + 241 := by
    linarith [hna4, hE4, hB1]
  have hq2 : ‖qParamFun z ^ 2‖ = ‖Ept z‖ ^ 4 := kmfd_norm_q2 z
  have hmid1 : ‖(E4Fun z - 1 - 240 * qParamFun z) * (E4Fun z + (1 + 240 * qParamFun z))‖
      ≤ C4 * ‖Ept z‖ ^ 4 * (1 + 240 + C4 + 241) := by
    rw [norm_mul]
    exact mul_le_mul hδ hf (norm_nonneg _) (by positivity)
  have hmid : ‖E4Fun z ^ 2 - (1 + 480 * qParamFun z)‖
      ≤ C4 * ‖Ept z‖ ^ 4 * (1 + 240 + C4 + 241) + 57600 * ‖Ept z‖ ^ 4 := by
    have hsplit : E4Fun z ^ 2 - (1 + 480 * qParamFun z)
        = (E4Fun z - 1 - 240 * qParamFun z) * (E4Fun z + (1 + 240 * qParamFun z))
          + 57600 * qParamFun z ^ 2 := by ring
    rw [hsplit]
    have h2 : ‖(57600 : ℂ) * qParamFun z ^ 2‖ = 57600 * ‖Ept z‖ ^ 4 := by
      rw [norm_mul, show ‖(57600 : ℂ)‖ = 57600 by norm_num, hq2]
    refine le_trans (norm_add_le _ _) ?_
    rw [h2]
    linarith [hmid1]
  have hdec : Compact.dE14 z = E4Fun z ^ 2 * (E6Fun z - 1 + 504 * qParamFun z)
      + (E4Fun z ^ 2 - (1 + 480 * qParamFun z)) * (1 - 504 * qParamFun z)
      - 241920 * qParamFun z ^ 2 := by
    simp only [Compact.dE14, Compact.E14ref, Compact.qParamFun_eq_Ept_sq]
    ring
  have hA : ‖E4Fun z ^ 2 * (E6Fun z - 1 + 504 * qParamFun z)‖
      ≤ (1 + 240 + C4) ^ 2 * (C6 * ‖Ept z‖ ^ 4) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4 2) hε (norm_nonneg _) (by positivity)
  have hB : ‖(E4Fun z ^ 2 - (1 + 480 * qParamFun z)) * (1 - 504 * qParamFun z)‖
      ≤ (C4 * ‖Ept z‖ ^ 4 * (1 + 240 + C4 + 241) + 57600 * ‖Ept z‖ ^ 4) * 505 := by
    rw [norm_mul]
    exact mul_le_mul hmid hb (norm_nonneg _) (by positivity)
  have hC : ‖(241920 : ℂ) * qParamFun z ^ 2‖ = 241920 * ‖Ept z‖ ^ 4 := by
    rw [norm_mul, show ‖(241920 : ℂ)‖ = 241920 by norm_num, hq2]
  rw [hdec]
  refine le_trans (norm_sub_le _ _) ?_
  have hna5 := norm_add_le (E4Fun z ^ 2 * (E6Fun z - 1 + 504 * qParamFun z))
    ((E4Fun z ^ 2 - (1 + 480 * qParamFun z)) * (1 - 504 * qParamFun z))
  have hsum : ‖E4Fun z ^ 2 * (E6Fun z - 1 + 504 * qParamFun z)
      + (E4Fun z ^ 2 - (1 + 480 * qParamFun z)) * (1 - 504 * qParamFun z)‖
      ≤ (1 + 240 + C4) ^ 2 * (C6 * ‖Ept z‖ ^ 4)
        + (C4 * ‖Ept z‖ ^ 4 * (1 + 240 + C4 + 241) + 57600 * ‖Ept z‖ ^ 4) * 505 := by
    linarith [hna5, hA, hB]
  rw [hC]
  have h0 : (0 : ℝ) ≤ ‖Ept z‖ ^ 4 := by positivity
  linarith [hsum, h0]

/-- `E₄(z)³ - (1+240E²)³ = O(‖Ept z‖⁴)` for `Im z ≥ 1`. -/
private lemma kmfd_E4cubedev_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖E4Fun z ^ 3 - kmfd_E4refc z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C4, hC4, h4⟩ := E4Fun_two_term
  refine ⟨C4 * ((1 + 240 + C4) ^ 2 + (1 + 240 + C4) * 241 + 241 ^ 2), by positivity,
    fun z hz => ?_⟩
  have hq := kmfd_norm_q_le_one hz
  have hE4 : ‖E4Fun z‖ ≤ 1 + 240 + C4 := kmfd_E4_bdd hC4 h4 hz
  have hδ : ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ C4 * ‖Ept z‖ ^ 4 := by
    rw [← kmfd_norm_q_sq]; exact h4 z hz
  have hB1 : ‖1 + 240 * qParamFun z‖ ≤ 241 := by
    have h2 := norm_add_le (1 : ℂ) (240 * qParamFun z)
    rw [norm_one, norm_mul, show ‖(240 : ℂ)‖ = 240 by norm_num] at h2
    calc ‖1 + 240 * qParamFun z‖ ≤ 1 + 240 * ‖qParamFun z‖ := h2
      _ ≤ 241 := by linarith
  have hfac : ‖E4Fun z ^ 2 + E4Fun z * (1 + 240 * qParamFun z)
      + (1 + 240 * qParamFun z) ^ 2‖
      ≤ (1 + 240 + C4) ^ 2 + (1 + 240 + C4) * 241 + 241 ^ 2 := by
    have h1 : ‖E4Fun z ^ 2‖ ≤ (1 + 240 + C4) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4 2
    have h2 : ‖E4Fun z * (1 + 240 * qParamFun z)‖ ≤ (1 + 240 + C4) * 241 := by
      rw [norm_mul]
      exact mul_le_mul hE4 hB1 (norm_nonneg _) (by positivity)
    have h3 : ‖(1 + 240 * qParamFun z) ^ 2‖ ≤ 241 ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hB1 2
    exact kmfd_sum3_le h1 h2 h3
  have hdec : E4Fun z ^ 3 - kmfd_E4refc z
      = (E4Fun z - 1 - 240 * qParamFun z)
        * (E4Fun z ^ 2 + E4Fun z * (1 + 240 * qParamFun z)
            + (1 + 240 * qParamFun z) ^ 2) := by
    simp only [kmfd_E4refc, kmfd_q_eq]
    ring
  rw [hdec, norm_mul]
  calc ‖E4Fun z - 1 - 240 * qParamFun z‖
        * ‖E4Fun z ^ 2 + E4Fun z * (1 + 240 * qParamFun z)
            + (1 + 240 * qParamFun z) ^ 2‖
      ≤ (C4 * ‖Ept z‖ ^ 4) * ((1 + 240 + C4) ^ 2 + (1 + 240 + C4) * 241 + 241 ^ 2) :=
        mul_le_mul hδ hfac (norm_nonneg _) (by positivity)
    _ = C4 * ((1 + 240 + C4) ^ 2 + (1 + 240 + C4) * 241 + 241 ^ 2) * ‖Ept z‖ ^ 4 := by ring

/-- `Δ(z) - E² = O(‖Ept z‖⁴)` for `Im z ≥ 1`. -/
private lemma kmfd_Deltadev_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖DeltaFun z - (Ept z) ^ 2‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C, hC, h⟩ := DeltaFun_two_term
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 := h z hz
  rw [kmfd_q_eq z] at h1
  have hq : ‖Ept z ^ 2‖ ^ 2 = ‖Ept z‖ ^ 4 := by
    rw [norm_pow, ← pow_mul]
  rwa [hq] at h1

/-- `j(z) - (1+240E²)³(E⁻²+24) = O(‖Ept z‖²)` for `Im z ≥ 1`. -/
private lemma kmfd_jdev_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖jInvariantFun z - kmfd_jref z‖ ≤ C * ‖Ept z‖ ^ 2 := by
  obtain ⟨Cd, hCd, hd⟩ := kmfd_dDelta_le
  obtain ⟨C8, hC8, h8⟩ := kmfd_E4cubedev_le
  obtain ⟨c, hc, hlow⟩ := Work.Asymptotics.DeltaFun_lower
  refine ⟨C8 * (c⁻¹) + 241 ^ 3 * Cd, by positivity, fun z hz => ?_⟩
  have hE : (0 : ℝ) < ‖Ept z‖ := norm_pos_iff.mpr (Work.Residues.Ept_ne_zero z)
  have hΔlow : c * ‖Ept z‖ ^ 2 ≤ ‖DeltaFun z‖ := by
    have h := hlow z hz
    rwa [kmfd_q_eq, norm_pow] at h
  have hΔpos : 0 < ‖DeltaFun z‖ := lt_of_lt_of_le (mul_pos hc (by positivity)) hΔlow
  have hinv : ‖(DeltaFun z)⁻¹‖ ≤ c⁻¹ * (‖Ept z‖ ^ 2)⁻¹ := by
    rw [norm_inv]
    have h1 : (‖DeltaFun z‖)⁻¹ ≤ (c * ‖Ept z‖ ^ 2)⁻¹ :=
      inv_anti₀ (mul_pos hc (by positivity)) hΔlow
    have h2 : (c * ‖Ept z‖ ^ 2)⁻¹ = c⁻¹ * (‖Ept z‖ ^ 2)⁻¹ := by rw [mul_inv]
    rwa [h2] at h1
  have hB : ‖(1 + 240 * qParamFun z) ^ 3‖ ≤ 241 ^ 3 := by
    have hq := kmfd_norm_q_le_one hz
    have h1 : ‖1 + 240 * qParamFun z‖ ≤ 241 := by
      have h2 := norm_add_le (1 : ℂ) (240 * qParamFun z)
      rw [norm_one, norm_mul, show ‖(240 : ℂ)‖ = 240 by norm_num] at h2
      calc ‖1 + 240 * qParamFun z‖ ≤ 1 + 240 * ‖qParamFun z‖ := h2
        _ ≤ 241 := by linarith
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 3
  have hsplit : jInvariantFun z - kmfd_jref z
      = (E4Fun z ^ 3 - kmfd_E4refc z) * (DeltaFun z)⁻¹
        + (1 + 240 * qParamFun z) ^ 3 * Compact.dDelta z := by
    have hΔne : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
    simp only [kmfd_jref, kmfd_E4refc, kmfd_q_eq, Compact.Dref, Compact.einv2,
      Compact.dDelta, jInvariantFun]
    field_simp
    ring
  rw [hsplit]
  have hE2 : ‖Ept z‖ ^ 4 * (‖Ept z‖ ^ 2)⁻¹ = ‖Ept z‖ ^ 2 := by
    field_simp
  have hsum : ‖(E4Fun z ^ 3 - kmfd_E4refc z) * (DeltaFun z)⁻¹
      + (1 + 240 * qParamFun z) ^ 3 * Compact.dDelta z‖
      ≤ (C8 * ‖Ept z‖ ^ 4) * (c⁻¹ * (‖Ept z‖ ^ 2)⁻¹) + 241 ^ 3 * (Cd * ‖Ept z‖ ^ 2) := by
    have hA1 : ‖(E4Fun z ^ 3 - kmfd_E4refc z) * (DeltaFun z)⁻¹‖
        ≤ (C8 * ‖Ept z‖ ^ 4) * (c⁻¹ * (‖Ept z‖ ^ 2)⁻¹) := by
      rw [norm_mul]
      exact mul_le_mul (h8 z hz) hinv (norm_nonneg _) (by positivity)
    have hA2 : ‖(1 + 240 * qParamFun z) ^ 3 * Compact.dDelta z‖
        ≤ 241 ^ 3 * (Cd * ‖Ept z‖ ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul hB (hd z hz) (norm_nonneg _) (by positivity)
    have hna6 := norm_add_le ((E4Fun z ^ 3 - kmfd_E4refc z) * (DeltaFun z)⁻¹)
      ((1 + 240 * qParamFun z) ^ 3 * Compact.dDelta z)
    linarith [hna6, hA1, hA2]
  have hfinal : (C8 * ‖Ept z‖ ^ 4) * (c⁻¹ * (‖Ept z‖ ^ 2)⁻¹) + 241 ^ 3 * (Cd * ‖Ept z‖ ^ 2)
      ≤ (C8 * (c⁻¹) + 241 ^ 3 * Cd) * ‖Ept z‖ ^ 2 := by
    rw [show (C8 * ‖Ept z‖ ^ 4) * (c⁻¹ * (‖Ept z‖ ^ 2)⁻¹)
          = C8 * c⁻¹ * (‖Ept z‖ ^ 4 * (‖Ept z‖ ^ 2)⁻¹) by ring, hE2]
    nlinarith [hE, hc.le, hC8.le, hCd.le, norm_nonneg (Ept z)]
  linarith [hsum, hfinal]

/-- `‖𝓛 z‖ ≤ C (1+‖z‖)` for `Im z ≥ 1`. -/
private lemma kmfd_L_le (ℓ : LogLambdaData) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  obtain ⟨C, hC, h⟩ := Compact.cuspC_spec ℓ
  refine ⟨Real.pi + ‖Compact.cuspC ℓ‖ + 20 + C + 1, by positivity, fun z hz => ?_⟩
  have hz1 := h z hz
  have he := kmfd_norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  have he3 : ‖Ept z‖ ^ 3 ≤ 1 := by
    calc ‖Ept z‖ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) he 3
      _ = 1 := by norm_num
  have hX : ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + Compact.cuspC ℓ‖
      ≤ Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
    calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + Compact.cuspC ℓ‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := norm_add_le _ _
      _ = Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
            Complex.norm_I, mul_one]
  have hY : ‖(-(8 : ℂ)) * Ept z + (12 : ℂ) * (Ept z) ^ 2‖ ≤ 20 := by
    have h1 : ‖(-(8 : ℂ)) * Ept z‖ ≤ 8 := by
      rw [norm_mul, show ‖(-(8 : ℂ))‖ = 8 by norm_num]
      linarith
    have h2 : ‖(12 : ℂ) * (Ept z) ^ 2‖ ≤ 12 := by
      rw [norm_mul, show ‖(12 : ℂ)‖ = 12 by norm_num]
      have := mul_le_mul_of_nonneg_left he2 (by norm_num : (0 : ℝ) ≤ 12)
      linarith
    have hsum := norm_add_le ((-(8 : ℂ)) * Ept z) ((12 : ℂ) * (Ept z) ^ 2)
    linarith [hsum, h1, h2]
  have herr : ‖ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + Compact.cuspC ℓ - 8 * Ept z
      + 12 * (Ept z) ^ 2)‖ ≤ C := by
    refine le_trans hz1 ?_
    calc C * ‖Ept z‖ ^ 3 ≤ C * 1 := mul_le_mul_of_nonneg_left he3 hC.le
      _ = C := mul_one C
  have hdec : ℓ.L z = (ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + Compact.cuspC ℓ
        - 8 * Ept z + 12 * (Ept z) ^ 2))
      + ((Real.pi : ℂ) * Complex.I * (z : ℂ) + Compact.cuspC ℓ)
      + ((-(8 : ℂ)) * Ept z + (12 : ℂ) * (Ept z) ^ 2) := by ring
  have hsum3 := kmfd_sum3_le herr hX hY
  rw [hdec]
  refine le_trans hsum3 ?_
  have hnn : (0 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by positivity
  nlinarith [Real.pi_pos, norm_nonneg (z : ℂ), norm_nonneg (Compact.cuspC ℓ), hC.le]

/-- `‖W(z)‖ ≤ C` for `Im z ≥ 1`. -/
private lemma kmfd_W_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖WFun z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_W_second
  refine ⟨1 + 8 + 24 + C, by positivity, fun z hz => ?_⟩
  have hz1 := h z hz
  have he := kmfd_norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  have he3 : ‖Ept z‖ ^ 3 ≤ 1 := by
    calc ‖Ept z‖ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) he 3
      _ = 1 := by norm_num
  have hY : ‖(-(8 : ℂ)) * Ept z + (24 : ℂ) * (Ept z) ^ 2‖ ≤ 8 + 24 := by
    have h1 : ‖(-(8 : ℂ)) * Ept z‖ ≤ 8 := by
      rw [norm_mul, show ‖(-(8 : ℂ))‖ = 8 by norm_num]
      linarith
    have h2 : ‖(24 : ℂ) * (Ept z) ^ 2‖ ≤ 24 := by
      rw [norm_mul, show ‖(24 : ℂ)‖ = 24 by norm_num]
      have := mul_le_mul_of_nonneg_left he2 (by norm_num : (0 : ℝ) ≤ 24)
      linarith
    have hsum := norm_add_le ((-(8 : ℂ)) * Ept z) ((24 : ℂ) * (Ept z) ^ 2)
    linarith [hsum, h1, h2]
  have herr : ‖WFun z - (1 - 8 * Ept z + 24 * (Ept z) ^ 2)‖ ≤ C := by
    refine le_trans hz1 ?_
    calc C * ‖Ept z‖ ^ 3 ≤ C * 1 := mul_le_mul_of_nonneg_left he3 hC.le
      _ = C := mul_one C
  have hdec : WFun z = (WFun z - (1 - 8 * Ept z + 24 * (Ept z) ^ 2)) + (1 : ℂ)
      + ((-(8 : ℂ)) * Ept z + (24 : ℂ) * (Ept z) ^ 2) := by ring
  have hsum3 := kmfd_sum3_le herr (le_of_eq norm_one) hY
  rw [hdec]
  refine le_trans hsum3 ?_
  linarith

/-- `‖U(z)² - V(z)²‖ ≤ C` for `Im z ≥ 1`. -/
private lemma kmfd_D2_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_D_second
  refine ⟨1 + 16 + 144 + C, by positivity, fun z hz => ?_⟩
  have hz1 := h z hz
  have he := kmfd_norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  have he3 : ‖Ept z‖ ^ 3 ≤ 1 := by
    calc ‖Ept z‖ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) he 3
      _ = 1 := by norm_num
  have hY : ‖(16 : ℂ) * Ept z - (144 : ℂ) * (Ept z) ^ 2‖ ≤ 16 + 144 := by
    have h1 : ‖(16 : ℂ) * Ept z‖ ≤ 16 := by
      rw [norm_mul, show ‖(16 : ℂ)‖ = 16 by norm_num]
      linarith
    have h2 : ‖(144 : ℂ) * (Ept z) ^ 2‖ ≤ 144 := by
      rw [norm_mul, show ‖(144 : ℂ)‖ = 144 by norm_num]
      have := mul_le_mul_of_nonneg_left he2 (by norm_num : (0 : ℝ) ≤ 144)
      linarith
    have hsum := norm_sub_le ((16 : ℂ) * Ept z) ((144 : ℂ) * (Ept z) ^ 2)
    linarith [hsum, h1, h2]
  have herr : ‖UFun z ^ 2 - VFun z ^ 2 - (1 + 16 * Ept z - 144 * (Ept z) ^ 2)‖ ≤ C := by
    refine le_trans hz1 ?_
    calc C * ‖Ept z‖ ^ 3 ≤ C * 1 := mul_le_mul_of_nonneg_left he3 hC.le
      _ = C := mul_one C
  have hdec : UFun z ^ 2 - VFun z ^ 2
      = (UFun z ^ 2 - VFun z ^ 2 - (1 + 16 * Ept z - 144 * (Ept z) ^ 2)) + (1 : ℂ)
      + ((16 : ℂ) * Ept z - (144 : ℂ) * (Ept z) ^ 2) := by ring
  have hsum3 := kmfd_sum3_le herr (le_of_eq norm_one) hY
  rw [hdec]
  refine le_trans hsum3 ?_
  linarith

/-! ## Reference values: boundedness and growth -/

private lemma kmfd_E10ref_le (z : ℍ) (hz : 1 ≤ z.im) : ‖Compact.E10ref z‖ ≤ 265 := by
  have he := kmfd_norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  simp only [Compact.E10ref]
  calc ‖1 - 264 * (Ept z) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖(264 : ℂ) * (Ept z) ^ 2‖ := norm_sub_le _ _
    _ ≤ 1 + 264 := by
        rw [norm_one, norm_mul, show ‖(264 : ℂ)‖ = 264 by norm_num]
        have h := mul_le_mul_of_nonneg_left he2 (by norm_num : (0:ℝ) ≤ 264)
        linarith
    _ ≤ 265 := by norm_num

private lemma kmfd_E14ref_le (z : ℍ) (hz : 1 ≤ z.im) : ‖Compact.E14ref z‖ ≤ 25 := by
  have he := kmfd_norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  simp only [Compact.E14ref]
  calc ‖1 - 24 * (Ept z) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * (Ept z) ^ 2‖ := norm_sub_le _ _
    _ ≤ 1 + 24 := by
        rw [norm_one, norm_mul, show ‖(24 : ℂ)‖ = 24 by norm_num]
        have h := mul_le_mul_of_nonneg_left he2 (by norm_num : (0:ℝ) ≤ 24)
        linarith
    _ ≤ 25 := by norm_num

private lemma kmfd_Dref_le (z : ℍ) (hz : 1 ≤ z.im) :
    ‖Compact.Dref z‖ ≤ 25 * (‖Ept z‖ ^ 2)⁻¹ := by
  have he := kmfd_norm_Ept_le_one hz
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := by
    calc ‖Ept z‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he 2
      _ = 1 := by norm_num
  have hepos2 : (0 : ℝ) < ‖Ept z‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (Work.Residues.Ept_ne_zero z)) 2
  have he1 : (1 : ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ := by
    rw [one_le_inv₀ hepos2]; exact he2
  simp only [Compact.Dref, Compact.einv2]
  have hnorm : ‖(Ept z)⁻¹ ^ 2‖ = (‖Ept z‖ ^ 2)⁻¹ := by
    rw [norm_pow, norm_inv, inv_pow]
  calc ‖(Ept z)⁻¹ ^ 2 + 24‖ ≤ ‖(Ept z)⁻¹ ^ 2‖ + ‖(24 : ℂ)‖ := norm_add_le _ _
    _ = (‖Ept z‖ ^ 2)⁻¹ + 24 := by rw [hnorm]; norm_num
    _ ≤ 25 * (‖Ept z‖ ^ 2)⁻¹ := by nlinarith [he1]

private lemma kmfd_E4refc_le (z : ℍ) (hz : 1 ≤ z.im) : ‖kmfd_E4refc z‖ ≤ 241 ^ 3 := by
  have he := kmfd_norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) he
  have h1 : ‖1 + 240 * (Ept z) ^ 2‖ ≤ 241 := by
    calc ‖1 + 240 * (Ept z) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖(240 : ℂ) * (Ept z) ^ 2‖ := norm_add_le _ _
      _ ≤ 1 + 240 := by
          rw [norm_one, norm_mul, show ‖(240 : ℂ)‖ = 240 by norm_num]
          have h := mul_le_mul_of_nonneg_left he2 (by norm_num : (0:ℝ) ≤ 240)
          linarith
      _ ≤ 241 := by norm_num
  simp only [kmfd_E4refc]
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 3

private lemma kmfd_jref_le (z : ℍ) (hz : 1 ≤ z.im) :
    ‖kmfd_jref z‖ ≤ 241 ^ 3 * (25 * (‖Ept z‖ ^ 2)⁻¹) := by
  rw [kmfd_jref, norm_mul]
  exact mul_le_mul (kmfd_E4refc_le z hz) (kmfd_Dref_le z hz) (norm_nonneg _) (by positivity)

/-! ## The package -/

/-- **Cusp deviations and boundedness of the `z`-atoms.** -/
theorem kmfd_zdevs (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Compact.dDelta z‖ ≤ C * ‖Ept z‖ ^ 2 ∧
      ‖Compact.dW z‖ ≤ C * ‖Ept z‖ ^ 3 ∧
      ‖Compact.dD2 z‖ ≤ C * ‖Ept z‖ ^ 3 ∧
      ‖Compact.dL ℓ z‖ ≤ C * ‖Ept z‖ ^ 3 ∧
      ‖Compact.dE14 z‖ ≤ C * ‖Ept z‖ ^ 4 ∧
      ‖Compact.dE10 z‖ ≤ C * ‖Ept z‖ ^ 4 ∧
      ‖E4Fun z ^ 3 - kmfd_E4refc z‖ ≤ C * ‖Ept z‖ ^ 4 ∧
      ‖DeltaFun z - (Ept z) ^ 2‖ ≤ C * ‖Ept z‖ ^ 4 ∧
      ‖jInvariantFun z - kmfd_jref z‖ ≤ C * ‖Ept z‖ ^ 2 ∧
      ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) ∧
      ‖WFun z‖ ≤ C ∧
      ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ C ∧
      ‖Compact.E10ref z‖ ≤ C ∧
      ‖Compact.E14ref z‖ ≤ C ∧
      ‖Compact.Dref z‖ ≤ C * (‖Ept z‖ ^ 2)⁻¹ ∧
      ‖kmfd_jref z‖ ≤ C * (‖Ept z‖ ^ 2)⁻¹ ∧
      ‖kmfd_E4refc z‖ ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := kmfd_dDelta_le
  obtain ⟨C2, hC2, h2⟩ := kmfd_dW_le
  obtain ⟨C3, hC3, h3⟩ := kmfd_dD2_le
  obtain ⟨C4, hC4, h4⟩ := kmfd_dL_le ℓ
  obtain ⟨C5, hC5, h5⟩ := kmfd_dE14_le
  obtain ⟨C6, hC6, h6⟩ := kmfd_dE10_le
  obtain ⟨C7, hC7, h7⟩ := kmfd_E4cubedev_le
  obtain ⟨C8, hC8, h8⟩ := kmfd_Deltadev_le
  obtain ⟨C9, hC9, h9⟩ := kmfd_jdev_le
  obtain ⟨C10, hC10, h10⟩ := kmfd_L_le ℓ
  obtain ⟨C11, hC11, h11⟩ := kmfd_W_le
  obtain ⟨C12, hC12, h12⟩ := kmfd_D2_le
  refine ⟨C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + 241 ^ 3 * 25 + 300,
    by positivity, fun z hz => ?_⟩
  have he := kmfd_norm_Ept_le_one hz
  have he0 : (0 : ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have he2 : ‖Ept z‖ ^ 2 ≤ 1 := by
    calc ‖Ept z‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ he0 he 2
      _ = 1 := by norm_num
  have he3 : ‖Ept z‖ ^ 3 ≤ ‖Ept z‖ ^ 2 := pow_le_pow_of_le_one he0 he (by norm_num)
  have he4 : ‖Ept z‖ ^ 4 ≤ ‖Ept z‖ ^ 2 := pow_le_pow_of_le_one he0 he (by norm_num)
  have hnn2 : (0 : ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans (h1 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h2 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h3 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h4 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h5 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h6 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h7 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h8 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h9 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · refine le_trans (h10 z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · exact le_trans (h11 z hz) (by linarith)
  · exact le_trans (h12 z hz) (by linarith)
  · exact le_trans (kmfd_E10ref_le z hz) (by linarith)
  · exact le_trans (kmfd_E14ref_le z hz) (by linarith)
  · refine le_trans (kmfd_Dref_le z hz) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hnn2
  · refine le_trans (kmfd_jref_le z hz) ?_
    have h : 241 ^ 3 * (25 * (‖Ept z‖ ^ 2)⁻¹)
        ≤ (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + 241 ^ 3 * 25 + 300)
          * (‖Ept z‖ ^ 2)⁻¹ := by nlinarith [hnn2]
    exact h
  · exact le_trans (kmfd_E4refc_le z hz) (by linarith)

end

end Work.Asymptotics
