import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG4a.lipschitz_chart_point

namespace Work.WilG4a

theorem lipschitz_chart_point_on (p : ℕ) (f g : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p+1) → ℝ))
    (Λ : Set (Fin p → ℝ))
    (hκ : κ ⊆ Work.WilG4a.strip p) (hpt : ∀ l, (Work.WilG4a.fibre κ l).Subsingleton)
    (hg : ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, g l x ∈ Work.WilG4a.I) :
    (∀ l ∈ Λ, ∀ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 f κ l t ∈ Work.WilG4a.I) ∧
    (∀ l ∈ Λ, ContDiffOn ℝ 1 (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t)) Work.WilG4a.I ∧
      ∀ t ∈ Work.WilG4a.I, |iteratedDeriv 1 (fun t : ℝ => g l (Work.WilG4a.chart1 f κ l t)) t| ≤ 1) ∧
    (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.fibre κ l, ∃ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 f κ l t = x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l _ t ht
    exact chart1_mem_I_of_subset_strip f κ hκ l ht
  · intro l _
    exact ⟨contDiffOn_chart1_comp f g κ l (hpt l),
      fun t _ => by rw [iteratedDeriv_chart1_comp f g κ l (hpt l) t]; norm_num⟩
  · intro l _ x hx
    exact chart1_surjOn_fibre f κ l (hpt l) x hx

end Work.WilG4a
