import Mathlib
import Submission.Work.FIArea7.Defs

/-!
# The elementary integral `∫_0^1 (cos α - x)/Q α x dx = -log(2 |sin(α/2)|)`

Here `Q α x = 1 - 2 x cos α + x² = |1 - x e^{iα}|²`.
Since `d/dx log (Q α x) = (2x - 2 cos α)/Q α x`, the integrand is the derivative of
`-(1/2) log (Q α x)`, and evaluating at the endpoints (`Q α 0 = 1`, `Q α 1 = 4 sin²(α/2)`)
gives the stated identity.
-/

namespace Work.FIArea7

open MeasureTheory intervalIntegral

/-- The derivative of `x ↦ Q α x`. -/
lemma hasDerivAt_Q (α x : ℝ) : HasDerivAt (fun y => Q α y) (2 * x - 2 * Real.cos α) x := by
  unfold Q
  change HasDerivAt ((fun _ : ℝ => (1:ℝ)) - (fun y : ℝ => 2*y*Real.cos α) + (fun y : ℝ => y^2))
      (2*x - 2*Real.cos α) x
  have hg : HasDerivAt (fun y : ℝ => 2*y*Real.cos α) (2*Real.cos α) x := by
    have h2 : HasDerivAt (fun y : ℝ => 2*y) (2:ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (2:ℝ)
    simpa using h2.mul_const (Real.cos α)
  have hs2 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    simpa using hasDerivAt_pow 2 x
  have h := ((hasDerivAt_const x (1:ℝ)).sub hg).add hs2
  exact h.congr_deriv (by ring)

theorem integral_cos_sub_div_Q (α : ℝ) (hs : Real.sin (α / 2) ≠ 0) :
    (∫ x in (0:ℝ)..1, (Real.cos α - x) / Q α x) = -Real.log (2 * |Real.sin (α / 2)|) := by
  have hmem : ∀ x ∈ Set.uIcc (0:ℝ) 1, (0:ℝ) ≤ x ∧ x ≤ 1 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    exact hx
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y => -(1/2) * Real.log (Q α y)) ((Real.cos α - x)/Q α x) x := by
    intro x hx
    obtain ⟨h0, h1⟩ := hmem x hx
    have hQne : Q α x ≠ 0 := Q_ne_zero α x hs h0 h1
    have hlog := (hasDerivAt_Q α x).log hQne
    have h := hlog.const_mul (-(1/2))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun x => (Real.cos α - x)/Q α x) volume (0:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · fun_prop
    · unfold Q; fun_prop
    · intro x hx
      exact Q_ne_zero α x hs (hmem x hx).1 (hmem x hx).2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hQ1 : Q α 1 = (2 * |Real.sin (α/2)|)^2 := by
    rw [Q_one, mul_pow, sq_abs]; ring
  have hlog1 : Real.log (Q α 1) = 2 * Real.log (2 * |Real.sin (α/2)|) := by
    rw [hQ1, Real.log_pow]; norm_num
  rw [Q_zero, Real.log_one, hlog1]
  ring

end Work.FIArea7
