import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk
import Submission.Work.Pert.Ksub2.deriv_phi_deep_upper
import Submission.Work.Pert.Ksub2.deriv_phi_le_of_deep_or_shallow

namespace Work.Pert.Ksub2

theorem sup_deriv_le_of_deep_or_shallow {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) {K' : Set ℂ} {ρe R Tb C Cd M : ℝ}
    (hρe : 0 ≤ ρe) (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hdeep : ∀ u : ℂ, u ∈ d.Dφ → R ≤ -u.re → |u.im| ≤ Tb + ρe → ‖deriv d.φ u‖ ≤ C)
    (hshallow : ∀ u ∈ (⋃ k ∈ Finset.range (⌈R + Tb + ρe⌉₊ + 1),
        (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K')), ‖deriv d.φ u‖ ≤ Cd)
    (hZsub : ∀ k ∈ Finset.range (⌈M + Tb + ρe⌉₊ + 1),
        ∀ u ∈ (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K'), u ∈ d.Dφ) :
    ∀ k ∈ Finset.range (⌈M + Tb + ρe⌉₊ + 1),
      ∀ u ∈ (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K'),
        ‖deriv d.φ u‖ ≤ max C Cd := by
  intro k hk u hu
  obtain ⟨z₀, hz₀, hzu⟩ := hu
  exact deriv_phi_le_of_deep_or_shallow d hρe hTb hdeep hshallow hz₀ hzu.symm
    (hZsub k hk u ⟨z₀, hz₀, hzu⟩)

end Work.Pert.Ksub2
