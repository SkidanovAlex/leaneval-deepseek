import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_le_of_deep_or_shallow
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk_bdd

namespace Work.Pert.Ksub2

open Metric

/-- Translating a point of the closed `ρe`-ball around `w - m` (`w ∈ K'`) back by `+ m` puts it in
the closed `ρe`-thickening of `K'`.  This is the ball-form of the `cthickening`-membership used by
`deriv_phi_le_of_deep_or_shallow`. -/
theorem mem_cthickening_of_dist_sub_nat_le {K' : Set ℂ} {ρe : ℝ} {w z : ℂ} {m : ℕ}
    (hw : w ∈ K') (hz : ‖z - (w - (m : ℂ))‖ ≤ ρe) :
    z + (m : ℂ) ∈ Metric.cthickening ρe K' := by
  refine Metric.mem_cthickening_of_dist_le (z + (m : ℂ)) w ρe K' hw ?_
  rw [Complex.dist_eq]
  have h : z + (m : ℂ) - w = z - (w - (m : ℂ)) := by ring
  rw [h]
  exact hz

/-- **Walk translate, derivative bound.**  If `z` lies in the closed `ρe`-ball around the translate
`w - m` of a point `w` of `K'`, then `z` is a translate (`z = z₀ - m`) of a point `z₀` of the closed
`ρe`-thickening of `K'`, so the deep-or-shallow bound `deriv_phi_le_of_deep_or_shallow` applies with
the very same data: `‖deriv d.φ z‖ ≤ max C Cd`. -/
theorem walk_translate_deriv_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} {ρe Tb R C Cd : ℝ} {w : ℂ} (hw : w ∈ K')
    (hρe : 0 ≤ ρe) (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hdeep : ∀ u : ℂ, u ∈ d.Dφ → R ≤ -u.re → |u.im| ≤ Tb + ρe → ‖deriv d.φ u‖ ≤ C)
    (hshallow : ∀ u ∈ (⋃ k ∈ Finset.range (⌈R + Tb + ρe⌉₊ + 1),
        (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K')), ‖deriv d.φ u‖ ≤ Cd)
    {m : ℕ} {z : ℂ} (hz : ‖z - (w - (m : ℂ))‖ ≤ ρe) (hzD : z ∈ d.Dφ) :
    ‖deriv d.φ z‖ ≤ max C Cd := by
  exact deriv_phi_le_of_deep_or_shallow (m := m) d hρe hTb hdeep hshallow
    (mem_cthickening_of_dist_sub_nat_le hw hz) (by ring) hzD

end Work.Pert.Ksub2
