import Mathlib
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound

namespace Work.LinnikAreas.turanAux2

open scoped BigOperators

noncomputable section

/-- **The multiplicity-weighted inverse-square zero sum of the completed Riemann zeta
function is bounded, uniformly on the half-plane `re w ≥ 3/2`.**

This is deduced from the Poisson-kernel bound `zetaHalfKernelBound`: on `re w ≥ 3/2`
every zero `u` of `Λ` satisfies `re u < 1`, hence `‖w - u‖ ≥ 1/2`, so that
`1/‖w - u‖² ≤ 5/(1 + ‖w - u‖²)`; for non-zeros the summand vanishes identically. -/
theorem completedZetaInvSq :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : ℂ), (3 / 2 : ℝ) ≤ w.re →
      Summable (fun u : ℂ => (analyticOrderNatAt completedRiemannZeta u : ℝ) / ‖w - u‖ ^ 2) ∧
        (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) / ‖w - u‖ ^ 2)
          ≤ C * (Real.log (2 + ‖w‖) + 2) := by
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.FarRepel.zetaHalfKernelBound
  refine ⟨5 * C, by positivity, fun w hw => ?_⟩
  obtain ⟨hsum, hbnd⟩ := hC w
  -- Pointwise domination of the inverse-square kernel by the Poisson kernel.
  have hpt : ∀ u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) / ‖w - u‖ ^ 2
      ≤ 5 * ((analyticOrderNatAt completedRiemannZeta u : ℝ)
          * (1 / (1 + ‖w - u‖ ^ 2))) := by
    intro u
    by_cases h : (analyticOrderNatAt completedRiemannZeta u : ℝ) = 0
    · rw [h]; simp
    · have hpos : 0 < (analyticOrderNatAt completedRiemannZeta u : ℝ) :=
        lt_of_le_of_ne (by positivity) (Ne.symm h)
      have hz : analyticOrderNatAt completedRiemannZeta u ≠ 0 := by
        intro h0; exact h (by rw [h0]; simp)
      have hΛ : completedRiemannZeta u = 0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero hz
      have hure : u.re < 1 := (Work.LinnikAreas.completedRiemannZeta_zero_strip hΛ).2
      have hdist : (1 / 2 : ℝ) ≤ ‖w - u‖ := by
        have h1 : |w.re - u.re| ≤ ‖w - u‖ := by
          simpa using Complex.abs_re_le_norm (w - u)
        have h2 : |w.re - u.re| = w.re - u.re := abs_of_nonneg (by linarith)
        rw [h2] at h1
        linarith
      have h4 : (1 : ℝ) ≤ 4 * ‖w - u‖ ^ 2 := by
        nlinarith [hdist, sq_nonneg ‖w - u‖]
      have hk : (1 : ℝ) / ‖w - u‖ ^ 2 ≤ 5 * (1 / (1 + ‖w - u‖ ^ 2)) := by
        rw [show (5 : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)) = 5 / (1 + ‖w - u‖ ^ 2) by ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h4]
      rw [div_eq_mul_one_div]
      have hrw : (5 : ℝ) * ((analyticOrderNatAt completedRiemannZeta u : ℝ)
            * (1 / (1 + ‖w - u‖ ^ 2)))
          = (analyticOrderNatAt completedRiemannZeta u : ℝ)
            * (5 * (1 / (1 + ‖w - u‖ ^ 2))) := by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hk (le_of_lt hpos)
  have hsum5 : Summable (fun u : ℂ => 5 * ((analyticOrderNatAt completedRiemannZeta u : ℝ)
      * (1 / (1 + ‖w - u‖ ^ 2)))) := hsum.mul_left 5
  have hsumT : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℝ) / ‖w - u‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun u => by positivity) hpt hsum5
  refine ⟨hsumT, ?_⟩
  have h2 := Summable.tsum_le_tsum hpt hsumT hsum5
  rw [tsum_mul_left] at h2
  calc (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) / ‖w - u‖ ^ 2)
      ≤ 5 * (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ)
          * (1 / (1 + ‖w - u‖ ^ 2))) := h2
    _ ≤ 5 * (C * (Real.log (2 + ‖w‖) + 2)) :=
        mul_le_mul_of_nonneg_left hbnd (by norm_num)
    _ = 5 * C * (Real.log (2 + ‖w‖) + 2) := by ring

end

end Work.LinnikAreas.turanAux2
