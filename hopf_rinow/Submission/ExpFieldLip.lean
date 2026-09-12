import Mathlib
import Submission.Model
import Submission.ModelCore
import Submission.ModelVarError

/-!
# The geodesic field is Lipschitz on the closed ball `closedBall z₀ 2`

Task: prove the final theorem `field_lipschitzOn` (supply the proof).

For a `C³` metric family `g : E → Bilin E` (with `Bilin E := E →L[ℝ] (E →L[ℝ] ℝ)`) whose
values are all invertible, the geodesic first-order field `V := odeField g : E × E → E × E`
is Lipschitz on every closed ball `closedBall z₀ R` (we only need `R := 2`).

## Proof sketch

`V` is `C¹` everywhere: `ContDiff ℝ 1 V` (from `ContDiffAt` at each point: use
`Submission.ModelCore.odeField_contDiffAt` and `rw [contDiff_iff_contDiffAt]`).  Hence
`fderiv ℝ V` is continuous.  On the compact set `S := closedBall z₀ 2` the continuous function
`x ↦ ‖fderiv ℝ V x‖` attains a maximum at some `xm ∈ S` (use `IsCompact.exists_isMaxOn` with
`isCompact_closedBall` and nonemptyness).  Then for all `x ∈ S`:
`‖fderiv ℝ V x‖ ≤ K` where `K := ‖fderiv ℝ V xm‖`.

Finally use the mean-value inequality for a function on a convex set with bounded derivative:

    `Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := V) hdiff hKbnd
      (convex_closedBall z₀ 2) hx hy : ‖V y - V x‖ ≤ K * ‖y - x‖`

where `hdiff : ∀ q ∈ S, DifferentiableAt ℝ V q` comes from `ContDiff ℝ 1 V`
(`hV1.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)`); then convert to `LipschitzOnWith` via
`rw [lipschitzOnWith_iff_dist_le_mul]` and `dist_eq_norm`, `norm_sub_rev`.

(All of this is exactly the argument used inside
`Submission.ModelVarConv.flowOnUnitBall`, lines 60-135 of that file — read it.)

Do NOT change the statement.  You may add helper lemmas.  No gaps or axioms may remain.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- The geodesic field is Lipschitz on the closed ball of radius 2 around `z₀`. -/
theorem field_lipschitzOn (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) :
    ∃ K : NNReal, LipschitzOnWith K (odeField g) (closedBall z₀ 2) := by
  let V : (E × E) → (E × E) := odeField g
  have hV1 : ContDiff ℝ 1 V := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases p with ⟨x, v⟩
    simpa [V] using odeField_contDiffAt g hg hinv x v
  have hfcont : Continuous (fderiv ℝ V) := hV1.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  let S : Set (E × E) := closedBall z₀ 2
  have hScomp : IsCompact S := isCompact_closedBall z₀ 2
  have hSne : S.Nonempty := ⟨z₀, by simp [S]⟩
  have hnormOn : ContinuousOn (fun x => ‖fderiv ℝ V x‖) S := hfcont.norm.continuousOn
  rcases hScomp.exists_isMaxOn hSne hnormOn with ⟨xm, hxm, hmax⟩
  let K : NNReal := ⟨‖fderiv ℝ V xm‖, norm_nonneg _⟩
  have hKbnd : ∀ x ∈ S, ‖fderiv ℝ V x‖ ≤ (K : ℝ) := by
    intro x hx
    calc
      ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ V xm‖ := hmax hx
      _ = (K : ℝ) := rfl
  refine ⟨K, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hdiff : ∀ q ∈ S, DifferentiableAt ℝ V q := fun q _ =>
    (hV1.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
  have hsub := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := V) hdiff hKbnd
    (convex_closedBall z₀ 2) hx hy
  have hnorm : ‖V y - V x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    simpa [V, S] using hsub
  simpa [dist_eq_norm, norm_sub_rev] using hnorm

end

end Submission.Model
