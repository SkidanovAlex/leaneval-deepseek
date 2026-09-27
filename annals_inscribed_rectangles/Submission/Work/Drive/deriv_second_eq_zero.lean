import Mathlib
import Submission.Work.Drive.UmlaufSetup

namespace Work.Drive

/-- If `t₀` minimises the second coordinate of a regular closed curve, the tangent at `t₀` is
horizontal.

`t ↦ (c t).2` attains a global (hence local) minimum at `t₀` and is differentiable
(`hc.contDiff`), so `deriv (fun t => (c t).2) t₀ = 0` (Fermat, `IsLocalMin.deriv_eq_zero`), and
`deriv (fun t => (c t).2) t₀ = (deriv c t₀).2`. -/
theorem deriv_second_eq_zero (c : ℝ → ℝ × ℝ) (hc : Work.Drive.RegCurve c) {t₀ : ℝ}
    (hmin : ∀ t, (c t₀).2 ≤ (c t).2) : (deriv c t₀).2 = 0 := by
  have hdiff : DifferentiableAt ℝ c t₀ :=
    (hc.contDiff.differentiable (by norm_num)).differentiableAt
  have hloc : IsLocalMin (fun t => (c t).2) t₀ := Filter.Eventually.of_forall hmin
  have h0 : deriv (fun t => (c t).2) t₀ = 0 := hloc.deriv_eq_zero
  have hderiv : deriv (fun t => (c t).2) t₀ = (deriv c t₀).2 := by
    change fderiv ℝ (fun t => (c t).2) t₀ 1 = (fderiv ℝ c t₀ 1).2
    rw [fderiv.snd hdiff]
    rfl
  rw [hderiv] at h0
  exact h0

end Work.Drive
