import Mathlib
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger

/-- The cardinality of the Ionescu–Wainger arithmetic frequency set `(ℚ/ℤ)_{≤l}` is at most
`2^{C 2^{ρl}}` for a constant `C = C(ρ)` depending only on `ρ`.

This is the form of the Ionescu–Wainger height bound of Krause–Mirek–Tao (Appendix A,
Lemma `mag-lem`(iii)) needed downstream: `Work.Analysis.IonescuWainger.iw_height_card_le` gives
`#(ℚ/ℤ)_{≤l} ≤ C₀ · 2^{2^{ρl}}` for a constant `C₀ = C₀(ρ)`, and since `2^{ρl} ≥ 1` the
multiplicative constant `C₀` is absorbed into the exponent:
`C₀ · 2^{2^{ρl}} = 2^{log₂ C₀ + 2^{ρl}} ≤ 2^{(C₀' + 2)·2^{ρl}}`. -/
theorem iwArithFreqs_card_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℕ,
      ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) ≤
        (2 : ℝ) ^ (C * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := iw_height_card_le hρ
  set A : ℝ := max 0 (Real.logb 2 C) with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact le_max_left _ _
  have hAlog : Real.logb 2 C ≤ A := by rw [hA]; exact le_max_right _ _
  refine ⟨A + 2, by positivity, fun l => ?_⟩
  have hT1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hAT : A ≤ A * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hT1 hA0
    simpa using h
  have hexp : Real.logb 2 C + (2 : ℝ) ^ (ρ * (l : ℝ))
      ≤ (A + 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
    nlinarith [hAlog, hAT, hT1, hA0]
  calc ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)
      ≤ C * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) := hC l
    _ = (2 : ℝ) ^ (Real.logb 2 C) * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hCpos]
    _ = (2 : ℝ) ^ (Real.logb 2 C + (2 : ℝ) ^ (ρ * (l : ℝ))) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ ((A + 2) * (2 : ℝ) ^ (ρ * (l : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

end Work.KMTAreas.A7
