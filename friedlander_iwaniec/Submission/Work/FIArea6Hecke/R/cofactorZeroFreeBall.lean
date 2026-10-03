import Mathlib

namespace Work.FIArea6Hecke.R

theorem cofactorZeroFreeBall {Λ : ℂ → ℂ} (hDiff : Differentiable ℂ Λ) (h0 : Λ 0 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ → Λ z ≠ 0 := by
  have hopen : IsOpen {z : ℂ | Λ z ≠ 0} :=
    isOpen_compl_singleton.preimage hDiff.continuous
  have hmem : (0 : ℂ) ∈ {z : ℂ | Λ z ≠ 0} := h0
  rcases Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem) with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun z hz => ?_⟩
  exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hz)

end Work.FIArea6Hecke.R
