import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_zeroSumKMultBound
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount
import Submission.Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count

namespace Work.LinnikAreas.turanAux2

open scoped Classical BigOperators

/-- **Pointwise comparison of the inverse-square kernel with its bounded variant.**

For a zero `u` of `completedLFunction χ` one has `Re u < 1`, while `Re w ≥ 3/2`; hence
`‖w - u‖ ≥ 1/2` and `1/‖w-u‖² ≤ 5/(1 + ‖w-u‖²)`.  For a non-zero of `Λ(·,χ)` both sides
vanish. -/
private lemma ord_div_norm_sq_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (w : ℂ) (hw : (3 / 2 : ℝ) ≤ w.re) (u : ℂ) :
    (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) / ‖w - u‖ ^ 2
      ≤ 5 * ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖w - u‖ ^ 2))) := by
  by_cases h : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u = 0
  · rw [h]; simp
  · have hpos : 0 < (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    have hz : DirichletCharacter.completedLFunction χ u = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero h
    have hre : u.re ≤ 1 :=
      le_of_lt (Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hprim hz).2
    have hdist : (1 / 2 : ℝ) ≤ ‖w - u‖ := by
      have h1 : |w.re - u.re| ≤ ‖w - u‖ := by
        simpa using Complex.abs_re_le_norm (w - u)
      have h2 : |w.re - u.re| = w.re - u.re := abs_of_nonneg (by linarith)
      linarith
    have h4 : (1 : ℝ) ≤ 4 * ‖w - u‖ ^ 2 := by nlinarith [hdist, sq_nonneg ‖w - u‖]
    have hk : (1 : ℝ) / ‖w - u‖ ^ 2 ≤ 5 * (1 / (1 + ‖w - u‖ ^ 2)) := by
      rw [show (5 : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)) = 5 / (1 + ‖w - u‖ ^ 2) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h4]
    rw [div_eq_mul_one_div]
    calc (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
            (1 / ‖w - u‖ ^ 2)
        ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
            (5 * (1 / (1 + ‖w - u‖ ^ 2))) := mul_le_mul_of_nonneg_left hk (le_of_lt hpos)
      _ = 5 * ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
            (1 / (1 + ‖w - u‖ ^ 2))) := by ring

theorem completedLInvSq :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → χ.IsPrimitive → ∀ (w : ℂ), (3 / 2 : ℝ) ≤ w.re →
      Summable (fun u : ℂ =>
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) / ‖w - u‖ ^ 2) ∧
        (∑' u : ℂ,
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) / ‖w - u‖ ^ 2)
          ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
  classical
  -- The uniform (in `χ` and in the centre) ball count of the zeros of `Λ(·,χ)`.
  obtain ⟨c, hcpos, hc⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  -- The dyadic estimate converting a ball count into a Poisson-kernel bound, with the
  -- counting parameter `q = log N` kept symbolic so that the constant is absolute.
  obtain ⟨C, hCpos, hC⟩ :=
    Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count (c := c) hcpos.le
  refine ⟨5 * C, by positivity, ?_⟩
  intro q hq _inst χ hχ hprim w hw
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hcnt : ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (q : ℝ) + 2) :=
    fun a ρ hρ => hc χ hχ hprim a ρ hρ
  -- Finset-form bound with the bounded kernel `1/(1 + ‖w-u‖²)`.
  have hkey : ∀ S : Finset ℂ,
      ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖w - u‖ ^ 2))
        ≤ C * (Real.log (2 + ‖w‖) + Real.log (q : ℝ) + 2) :=
    fun S => hC (DirichletCharacter.completedLFunction χ) hΛan (Real.log (q : ℝ)) hlogq hcnt w S
  -- Pass to the genuine inverse-square kernel, at the cost of the factor `5`.
  have hmain : ∀ S : Finset ℂ,
      ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) / ‖w - u‖ ^ 2
        ≤ (5 * C) * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
    intro S
    have h1 : ∑ u ∈ S,
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) / ‖w - u‖ ^ 2
        ≤ 5 * ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
            (1 / (1 + ‖w - u‖ ^ 2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun u _ => ord_div_norm_sq_le χ hχ hprim w hw u)
    calc ∑ u ∈ S,
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) / ‖w - u‖ ^ 2
        ≤ 5 * ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
            (1 / (1 + ‖w - u‖ ^ 2)) := h1
      _ ≤ 5 * (C * (Real.log (2 + ‖w‖) + Real.log (q : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (hkey S) (by norm_num)
      _ = (5 * C) * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by ring
  have hnn : ∀ u : ℂ, 0 ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
      / ‖w - u‖ ^ 2 :=
    fun u => div_nonneg (by positivity) (sq_nonneg _)
  exact ⟨summable_of_sum_le hnn hmain, Real.tsum_le_of_sum_le hnn hmain⟩

end Work.LinnikAreas.turanAux2
