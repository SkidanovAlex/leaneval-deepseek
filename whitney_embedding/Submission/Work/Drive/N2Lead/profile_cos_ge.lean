import Mathlib
import Submission.Work.Drive.N2Lead.saddleBridgeRow
import Submission.Work.Drive.N2Lead.mobius_lowerProfile

namespace Work.Drive.N2Lead

/-- **The radial profile dominates `1/4` against `cos` on the arc zone.**

With `φE = mobiusPhiE ηs m` the endpoint angle of the pinned top arc, and `r` any positive profile
satisfying `√(ηs² + m²) ≤ r φ²` on `Icc (-φE) φE`, one has `r φ * cos φ ≥ 1/4` there.

The content is entirely numerical: `φE ∈ (0, π/2)` with `cos (2 φE) = -ηs/√(ηs² + m²)` (the
analytic core `leadProfile_phiE`), and since `m > 1`, `ηs < 1/10` this forces
`cos φE ≥ 1/4`; while `√(ηs²+m²) > 1` forces `r φ > 1`. -/
theorem profile_cos_ge {ηs m φE : ℝ} {r : ℝ → ℝ} (hηs : 0 < ηs) (hηs' : ηs < 1 / 10)
    (hm : 1 < m) (hφE : φE = Work.Drive.N2Lead.mobiusPhiE ηs m)
    (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hlo : ∀ φ ∈ Set.Icc (-φE) φE, Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2) :
    ∀ φ ∈ Set.Icc (-φE) φE, (1 / 4 : ℝ) ≤ r φ * Real.cos φ := by
  have hm0 : 0 < m := by linarith
  obtain ⟨hcos2, hEpos0, hElt0⟩ := leadProfile_phiE hηs hm0
  have hEpos : 0 < φE := by rw [hφE]; exact hEpos0
  have hElt : φE < Real.pi / 2 := by rw [hφE]; exact hElt0
  have hcos2' : Real.cos (2 * φE) = -(ηs / Real.sqrt (ηs ^ 2 + m ^ 2)) := by
    rw [hφE, hcos2, leadProfileC1, neg_div]
  have hden : 0 < Real.sqrt (ηs ^ 2 + m ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq1 : 1 < Real.sqrt (ηs ^ 2 + m ^ 2) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    nlinarith
  have hratio : ηs / Real.sqrt (ηs ^ 2 + m ^ 2) < 7 / 8 := by
    rw [div_lt_iff₀ hden]
    calc ηs < 1 / 10 := hηs'
      _ < 7 / 8 * 1 := by norm_num
      _ < 7 / 8 * Real.sqrt (ηs ^ 2 + m ^ 2) :=
          mul_lt_mul_of_pos_left hsq1 (by norm_num)
  have hcosEsq : (1 / 16 : ℝ) ≤ Real.cos φE ^ 2 := by
    have hcx : Real.cos (2 * φE) = 2 * Real.cos φE ^ 2 - 1 := Real.cos_two_mul φE
    linarith
  have hcosEpos : 0 < Real.cos φE :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hElt⟩
  have hcosE : (1 / 4 : ℝ) ≤ Real.cos φE := by nlinarith
  intro φ hφ
  have hφabs : |φ| ≤ φE := by rw [abs_le]; exact ⟨hφ.1, hφ.2⟩
  have hcφ : Real.cos φE ≤ Real.cos φ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ)
      (by linarith [Real.pi_pos, hElt]) hφabs
    rwa [Real.cos_abs] at h
  have hr1 : 1 < r φ := by
    have h2 := hlo φ hφ
    have h3 : 1 < r φ ^ 2 := lt_of_lt_of_le hsq1 h2
    have h4 : 0 < r φ := hrpos φ
    nlinarith
  have hcosφ : (1 / 4 : ℝ) ≤ Real.cos φ := le_trans hcosE hcφ
  have h := mul_le_mul hcosφ hr1.le (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  nlinarith [h]

end Work.Drive.N2Lead
