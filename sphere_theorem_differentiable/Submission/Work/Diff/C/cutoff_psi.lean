import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.cutoff_psi_defs
import Submission.Work.Diff.C.cutW_basic
import Submission.Work.Diff.C.cutW_integral
import Submission.Work.Diff.C.cutPsi_hasDeriv
import Submission.Work.Diff.C.cutPsi_values

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open MeasureTheory

/-- The transition profile `cutW` is smooth. -/
theorem cutW_contDiff : ContDiff ℝ ∞ cutW := by
  unfold cutW
  fun_prop

/-- The rescaled profile `cutRho c` is smooth. -/
theorem cutRho_contDiff (c : ℝ) : ContDiff ℝ ∞ (cutRho c) := by
  unfold cutRho
  refine cutW_contDiff.comp ?_
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => x + 1 - c) := by fun_prop
  simpa using h1.div_const c

theorem cutoff_psi {c : ℝ} (hc : 0 < c) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧ (∀ s : ℝ, 0 ≤ deriv ψ s ∧ deriv ψ s ≤ 2) ∧
      (∀ s : ℝ, -1 + 2 * c ≤ s → ψ s = s) ∧ (∀ s : ℝ, s ≤ -1 + c → ψ s = -1 + c) := by
  obtain ⟨hW0, hW1, hWnn, hWle⟩ := cutW_basic
  have hderiv : deriv (cutPsi c) = cutRho c :=
    funext fun s => (cutPsi_hasDeriv hc s).deriv
  have hdiff : Differentiable ℝ (cutPsi c) :=
    fun s => (cutPsi_hasDeriv hc s).differentiableAt
  refine ⟨cutPsi c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨hdiff, by rw [hderiv]; exact cutRho_contDiff c⟩
  · apply monotone_of_deriv_nonneg hdiff
    intro s
    rw [hderiv]
    exact hWnn _
  · intro s
    have hd : deriv (cutPsi c) s = cutW ((s + 1 - c) / c) := by
      rw [(cutPsi_hasDeriv hc s).deriv]
      rfl
    rw [hd]
    exact ⟨hWnn _, hWle _⟩
  · exact (cutPsi_values hc cutW_integral).1
  · exact (cutPsi_values hc cutW_integral).2

end Work.Diff.C
