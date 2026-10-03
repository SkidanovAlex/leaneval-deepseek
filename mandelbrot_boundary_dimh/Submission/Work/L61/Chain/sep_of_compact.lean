import Mathlib
import Submission.Work.L61.Basic

namespace Work.L61.Chain

/-- A continuous map on the compact unit interval whose image avoids a compact set `K` stays a
positive distance away from `K` (in fact the infimum of `dist (f t) y`, `y ∈ K`, is attained). -/
theorem sep_of_compact {K : Set ℂ} (hK : IsCompact K) (f : unitInterval → ℂ)
    (hf : Continuous f) (hanti : ∀ t, f t ∉ K) :
    ∃ δ > 0, ∀ t y, y ∈ K → δ ≤ dist (f t) y := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun t y hy => absurd hy (Set.notMem_empty y)⟩
  · have hcont : Continuous fun t : unitInterval => Metric.infDist (f t) K :=
      (Metric.continuous_infDist_pt K).comp hf
    obtain ⟨t₀, -, ht₀⟩ :=
      IsCompact.exists_isMinOn (s := Set.univ) isCompact_univ Set.univ_nonempty
        hcont.continuousOn
    refine ⟨Metric.infDist (f t₀) K,
      (hK.isClosed.notMem_iff_infDist_pos hne).1 (hanti t₀), fun t y hy => ?_⟩
    exact le_trans ((isMinOn_iff.mp ht₀) t (Set.mem_univ t)) (Metric.infDist_le_dist_of_mem hy)

end Work.L61.Chain
