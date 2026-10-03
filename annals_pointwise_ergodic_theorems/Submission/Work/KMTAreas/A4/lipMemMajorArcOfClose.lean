import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs
import Submission.Work.Analysis.IonescuWainger.Height

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory
open Work.Analysis.IonescuWainger

theorem lipMemMajorArcOfClose {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {Q : ℕ} (hQ : 1 ≤ Q)
    {l : ℕ} (hQl : Q ≤ 2 ^ l) {k : ℤ} {ε x : ℝ} {n : ℤ}
    (hxn : |(Q : ℝ) * x - (n : ℝ)| ≤ ε) (hε : ε ≤ (Q : ℝ) * (2 : ℝ) ^ k) :
    ((x : ℝ) : Work.Analysis.InverseTheory.FreqCircle)
      ∈ Work.Analysis.InverseTheory.majorArc ρ l k := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  -- Step 1: the denominator `Q` is admissible.
  have hQmem : Q ∈ iwP ρ l := by
    rw [mem_iwP]
    by_cases h : l ≤ iwC0 ρ
    · exact Or.inl ⟨h, hQ, hQl⟩
    · exact Or.inr ⟨not_le.mp h,
        iwPconcrete_contains_range hρ hρ1 (le_of_lt (not_le.mp h)) hQ hQl⟩
  -- Step 2: the arithmetic frequency `n/Q` lies in `(ℚ/ℤ)_{≤l}`.
  have hαmem : (((n : ℝ) / (Q : ℝ) : ℝ) : FreqCircle) ∈ iwArithFreqs ρ l := by
    rw [mem_iwArithFreqs]
    refine ⟨Q, hQmem, ?_⟩
    rw [← AddCircle.coe_nsmul]
    have hmul : (Q : ℕ) • ((n : ℝ) / (Q : ℝ)) = (n : ℝ) := by
      rw [nsmul_eq_mul]
      field_simp
    rw [hmul, AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩
  -- Step 3: the remainder `θ = x - n/Q` lies in `ℝ_{≤k}`.
  set θ : ℝ := x - (n : ℝ) / (Q : ℝ) with hθdef
  have hθmem : θ ∈ realFreqInterval k := by
    rw [mem_realFreqInterval]
    have hθeq : θ = ((Q : ℝ) * x - (n : ℝ)) / (Q : ℝ) := by
      rw [hθdef]
      field_simp
    have habs : |θ| ≤ (2 : ℝ) ^ k := by
      rw [hθeq, abs_div, abs_of_pos hQpos]
      have h1 : |(Q : ℝ) * x - (n : ℝ)| / (Q : ℝ) ≤ ε / (Q : ℝ) :=
        div_le_div_of_nonneg_right hxn hQpos.le
      have h2 : ε / (Q : ℝ) ≤ (2 : ℝ) ^ k := by
        rw [div_le_iff₀ hQpos]
        calc ε ≤ (Q : ℝ) * (2 : ℝ) ^ k := hε
          _ = (2 : ℝ) ^ k * (Q : ℝ) := by ring
      exact le_trans h1 h2
    exact abs_le.mp habs
  refine mem_majorArc.mpr ⟨_, hαmem, θ, hθmem, ?_⟩
  exact congrArg (fun t : ℝ => ((t : ℝ) : FreqCircle)) (by rw [hθdef]; ring)

end Work.KMTAreas.A4
