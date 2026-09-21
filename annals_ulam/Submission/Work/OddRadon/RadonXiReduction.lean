import Submission.Work.OddRadon.Reduction
import Submission.Work.OddRadon.radonXi_norm
import Submission.Work.OddRadon.radonXi_zero_coord

/-!
# The reduction in the paper's angular parametrisation (`Work.OddRadon`, part 2b)

`ξ(α) = (sin α, 0, …, 0, -cos α)` is the unit normal used in Step 3 of Ryabogin's paper.  Its
first coordinate is `sin α`, so the one-variable reduction of the spherical Radon transform
reads `𝓡 (γ ∘ (· 0)) (ξ α) = radonProfile d γ (cos α)`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **The reduction in the paper's parametrisation.** -/
theorem sphericalRadon_radonXi (d : ℕ) [NeZero d] (hd : 3 ≤ d) {γ : ℝ → ℝ}
    (hγ : Continuous γ) {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    sphericalRadon d (fun w => γ (w 0)) (radonXi d α) = radonProfile d γ (Real.cos α) := by
  rw [sphericalRadon_rotationInvariant d hd hγ (radonXi_norm d (by omega) α)]
  have hcos : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  rw [radonXi_zero_coord d α,
    show 1 - Real.sin α ^ 2 = Real.cos α ^ 2 by nlinarith [Real.sin_sq_add_cos_sq α],
    Real.sqrt_sq hcos]

end Work.OddRadon
