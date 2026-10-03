import Mathlib
import Submission.Work.KMTContract.Defs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- The union of two Ionescu--Wainger arithmetic frequency sets is the arithmetic frequency set
of the larger height: `(ℚ/ℤ)_{≤l₁} ∪ (ℚ/ℤ)_{≤L} = (ℚ/ℤ)_{≤max l₁ L}`.  This is the monotonicity
`iwArithFreqs_mono` (which needs `0 < ρ ≤ 1`). -/
theorem iwArithFreqs_union_max {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ L : ℕ) :
    Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
        ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ L
      = Work.Analysis.IonescuWainger.iwArithFreqs ρ (max l₁ L) := by
  have hmono := Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1
  refine Finset.Subset.antisymm ?_ ?_
  · intro α hα
    rcases Finset.mem_union.mp hα with h | h
    · exact hmono (le_max_left l₁ L) h
    · exact hmono (le_max_right l₁ L) h
  · intro α hα
    rcases le_total l₁ L with h | h
    · refine Finset.mem_union_right _ ?_
      rwa [max_eq_right h] at hα
    · refine Finset.mem_union_left _ ?_
      rwa [max_eq_left h] at hα

theorem nonAliasing_of_size (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ L : ℕ) (K : ℤ),
      (K : ℝ) + C * (2 : ℝ) ^ (ρ * (max l₁ L : ℝ)) < 0 →
      Work.Analysis.IonescuWainger.NonAliasing K
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ L) := by
  obtain ⟨Cρ, hCρ, hNA⟩ := Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ
  refine ⟨Cρ, hCρ, ?_⟩
  intro l₁ L K hK
  -- the hypothesis is exactly the strict form of the good-major-arcs condition at the size
  -- `2^{ρ max l₁ L}` of the union.
  have hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ (max l₁ L) K := by
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs, Nat.cast_max]
    linarith
  rw [iwArithFreqs_union_max hρ hρ1 l₁ L]
  exact hNA (max l₁ L) K hgood

end Work.KMTPlan.A6
