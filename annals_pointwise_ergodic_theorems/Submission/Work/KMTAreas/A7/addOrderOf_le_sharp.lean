import Mathlib
import Submission.Work.KMTPlan.A6.iwP_element_le_sharp

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger

/-- **Sharp bound for the additive order of an Ionescu–Wainger arithmetic frequency.**

Every `α ∈ (ℚ/ℤ)_{≤l} = iwArithFreqs ρ l` is killed by some denominator `q ∈ P_{≤l}`, so
`addOrderOf α ∣ q`; hence `addOrderOf α ≤ q`, and the sharp element bound
`Work.KMTPlan.A6.iwP_element_le_sharp` for `P_{≤l}` gives
`addOrderOf α ≤ 2^{K(1 + l 2^{ρl/2} + l)}`. -/
theorem addOrderOf_le_sharp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ l : ℕ, ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
      ((addOrderOf α : ℕ) : ℝ)
        ≤ C * (2 : ℝ) ^ (K * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ))) := by
  obtain ⟨K, hKpos, hK⟩ := Work.KMTPlan.A6.iwP_element_le_sharp ρ hρ hρ1
  refine ⟨1, K, one_pos, hKpos, ?_⟩
  intro l α hα
  obtain ⟨q, hq, hαq⟩ := mem_iwArithFreqs.mp hα
  have hqpos : 0 < q := pos_of_mem_iwP hq
  have hdvd : addOrderOf α ∣ q := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hαq
  have hle : addOrderOf α ≤ q := Nat.le_of_dvd hqpos hdvd
  have hcast : ((addOrderOf α : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
  calc ((addOrderOf α : ℕ) : ℝ) ≤ (q : ℝ) := hcast
    _ ≤ (2 : ℝ) ^ (K * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ))) :=
        hK l q hq
    _ = 1 * (2 : ℝ) ^ (K * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ))) := by
        rw [one_mul]

end Work.KMTAreas.A7
