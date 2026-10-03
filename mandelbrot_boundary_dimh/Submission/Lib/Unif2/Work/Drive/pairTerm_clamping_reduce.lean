import Mathlib
import Submission.Lib.Unif2.Work.Drive.lastMileTools

/-!
# Reducing the clamping radius of a pairing term

The Dirichlet pairing term `pairTerm x ρ σ W f χ` clamps the two differentiated functions at the
radius `ρ`.  If the *weight* `W` and the test function `χ` are supported in a **smaller** ball (of
radius `σ'`), then the clamping radius may be reduced from `ρ` to any `r ≥ σ'`:

  `pairTerm x ρ σ W f χ = pairTerm x r σ W f χ`     (`σ' < σ`, `σ ≤ r ≤ ρ`).

This removes the *radius obstruction* of the pole identity: the logarithmic expansion of the Green
function is available only on *some* ball around the pole, but the clamping radius `ρ` of the cover
need not be smaller than it — one only needs the *support* of the localised test function to lie in
the expansion ball, and the support radius is under one's control.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Reduction of the clamping radius** (when the weight and the test function are supported in a
smaller ball). -/
theorem pairTerm_clamping_reduce {x : X} {ρ r σ σ' : ℝ} {W f χ : X → ℝ}
    (hσ'σ : σ' < σ) (hσr : σ ≤ r) (hrρ : r ≤ ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hWsupp : tsupport W ⊆ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) σ')
    (hχsupp : tsupport χ ⊆ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) σ') :
    pairTerm x ρ σ W f χ = pairTerm x r σ W f χ := by
  rw [pairTerm, pairTerm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) σ
  · -- on the small ball the clamped weight is the honest weight, which forces `z` into the `σ'`-ball
    rw [clampedPullback_apply_of_mem hz]
    by_cases hW0 : W ((chartAt ℂ x).symm z) = 0
    · rw [hW0, zero_mul, zero_mul]
    · have hmem : (chartAt ℂ x).symm z ∈ tsupport W :=
        subset_tsupport _ (Function.mem_support.mpr hW0)
      have hz' : z ∈ Metric.ball ((chartAt ℂ x) x) σ' := by
        have h1 := hWsupp hmem
        rwa [Set.mem_preimage, (chartAt ℂ x).right_inv
          (htgt (Metric.ball_subset_ball (le_trans hσr hrρ) hz))] at h1
      have hzr : z ∈ Metric.ball ((chartAt ℂ x) x) r := Metric.ball_subset_ball hσr hz
      have hf_eq : clampedPullback x ρ f =ᶠ[𝓝 z] clampedPullback x r f := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzr] with w hw
        rw [clampedPullback_apply_of_mem (u := f) (Metric.ball_subset_ball hrρ hw),
          clampedPullback_apply_of_mem (u := f) hw]
      have hχ_eq : clampedPullback x ρ χ =ᶠ[𝓝 z] clampedPullback x r χ := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzr] with w hw
        rw [clampedPullback_apply_of_mem (u := χ) (Metric.ball_subset_ball hrρ hw),
          clampedPullback_apply_of_mem (u := χ) hw]
      rw [Filter.EventuallyEq.gradient_eq hf_eq, Filter.EventuallyEq.gradient_eq hχ_eq]
  · rw [clampedPullback_eq_zero_of_notMem_ball (u := W) hz, zero_mul, zero_mul]

end Work.Drive
