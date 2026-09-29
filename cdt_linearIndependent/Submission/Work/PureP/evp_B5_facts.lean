import Mathlib
import Submission.Work.CPull.evp_B2_facts_ball1
import Submission.Work.CPull.evp_B2_ode
import Submission.Work.CPull.ps_analytic2
import Submission.Work.B5pull.coeff_bounds
import Submission.Work.B5pull.evp_ode
import Submission.Work.Pure.b5_rel

namespace Work.PureP

/-! Analytic facts about the evaluation series `y ↦ evp B₅ y = Σ [yⁿ]B₅ · yⁿ` on the unit disc.

Model: `Submission/Work/CPull/evp_B2_facts_ball1.lean` (proved, identical shape for `B₂`).
Ingredients: `Work.CPull.ps_analytic2` (a `C·(1/4)ⁿ` coefficient bound gives convergence,
term-by-term derivative and differentiability on the disc of radius `2 ⊇` unit disc),
`Work.B5pull.coeff_bounds` (`‖[yⁿ]B₅‖ ≤ 4·(1/4)ⁿ`), the formal ODE `Work.Pure.b5_rel`
(`2X(4-X)·B₅' = (4-X)·B₅ - 2·B₂ + 4X`), and the term-by-term comparison of the two series
(the local `evp_ode_of_rec` in `evp_B2_facts_ball1.lean` is `private`; here one needs the
two-series version: LHS coefficients `8n·cₙ - 2(n-1)·cₙ₋₁`, RHS coefficients
`4cₙ - cₙ₋₁ - 2dₙ + 4·[n=1]` with `c = [yⁿ]B₅`, `d = [yⁿ]B₂`), exactly as `Work.CPull.evp_B2_ode`
does it for `B₂` with `Work.CPull.B2_rec_cplx`.

The two-series term-by-term comparison is `Work.B5pull.series_ode`, and the transfer of the
formal relation `Work.Pure.b5_rel` to the disc `‖y‖ < 4` is `Work.B5pull.evp_ode` (whose
second component is precisely the analytic equation required here).  The summability and
term-by-term differentiation on the disc of radius `2` come from `Work.CPull.ps_analytic2`
applied to the coefficient bound `Work.B5pull.coeff_bounds`. -/
theorem evp_B5_facts :
    DifferentiableOn ℂ (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B5 y) (Metric.ball 0 1) ∧
    (∀ y ∈ Metric.ball (0 : ℂ) 1, HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ) * y ^ n)
      (Work.CPull.evp Submission.CDTPlan.B5 y)) ∧
    (∀ y ∈ Metric.ball (0 : ℂ) 1,
      2 * y * (4 - y) * deriv (fun w : ℂ => Work.CPull.evp Submission.CDTPlan.B5 w) y
        = (4 - y) * Work.CPull.evp Submission.CDTPlan.B5 y
          - 2 * Work.CPull.evp Submission.CDTPlan.B2 y + 4 * y) := by
  -- Coefficient bounds: `‖[yⁿ]B₅‖ ≤ 4·(1/4)ⁿ` and `‖[yⁿ]B₂‖ ≤ 10·(1/4)ⁿ`.
  obtain ⟨h5bound, h2bound⟩ := Work.B5pull.coeff_bounds
  -- Summability and term-by-term differentiation on the disc of radius `2`.
  obtain ⟨hS, _hS2, _hS3, hhderiv⟩ :=
    Work.CPull.ps_analytic2
      (fun n : ℕ => ((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ)) 4
      (by norm_num) h5bound
  -- The analytic ODE on the disc of radius `4`, which contains the unit disc.
  have hode : ∀ y : ℂ, ‖y‖ < 4 →
      2 * y * (4 - y) * deriv (fun z : ℂ => Work.CPull.evp Submission.CDTPlan.B5 z) y
        = (4 - y) * Work.CPull.evp Submission.CDTPlan.B5 y
          - 2 * Work.CPull.evp Submission.CDTPlan.B2 y + 4 * y :=
    (Work.B5pull.evp_ode (C2 := 10) (C5 := 4) (by norm_num) (by norm_num)
      h2bound h5bound).2
  have hnorm : ∀ y ∈ Metric.ball (0 : ℂ) 1, ‖y‖ < 1 := by
    intro y hy
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  refine ⟨?_, ?_, ?_⟩
  · -- Differentiability on the unit disc.
    intro y hy
    have h1 := hnorm y hy
    exact ((hhderiv y (by linarith)).differentiableAt).differentiableWithinAt
  · -- The series sums to `evp B₅`.
    intro y hy
    have h1 := hnorm y hy
    exact (hS y (by linarith)).hasSum
  · -- The differential equation.
    intro y hy
    have h1 := hnorm y hy
    exact hode y (by linarith)

end Work.PureP
