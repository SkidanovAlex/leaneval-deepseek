import Mathlib
import Submission.Work.LinnikAreas.Zeta1Aux.CommonsImports
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_window_mem_inner_ball
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_inner_ball_subset_closedBall

/-!
# The `ζ₁`-window sum is bounded by the divisor sum on the inner ball

For `|t| ≥ 5` we compare two sums over the (finite) divisor of the entire function
`riemannZeta₁ = (s-1)·ζ(s)`:

* the **window sum** over the large ball `B(0, |t|+6)`, restricted to the zeros whose
  imaginary part satisfies `|Im u - t| ≤ 3`;
* the **inner divisor sum** over the small ball `B(2 + i t, 37/10)`.

Every zero `u` counted by the window has `u.im ≠ 0` (because `|u.im| ≥ |t| - 3 ≥ 2`), so
by `hstrip` it satisfies `0 < u.re < 1`; together with `|u.im - t| ≤ 3` this gives
`dist u (2 + it)² < 4 + 9 = 13 < (37/10)²`, i.e. `u` lies in the inner ball.  On the inner
ball the two divisors agree (`divisor_eq_closedBall_subset`), and the divisor of an
analytic function is nonnegative, so the window sum is at most the full inner divisor sum.
-/

namespace Work.LinnikAreas.Zeta1Aux

private lemma analyticOnNhd_riemannZeta₁ (U : Set ℂ) : AnalyticOnNhd ℂ riemannZeta₁ U :=
  fun z _ => differentiable_riemannZeta₁.analyticAt z

private lemma meromorphicOn_riemannZeta₁ (U : Set ℂ) : MeromorphicOn riemannZeta₁ U :=
  fun z _ => (differentiable_riemannZeta₁.analyticAt z).meromorphicAt

/-- The divisor of the entire function `ζ₁` vanishes at every point where `ζ₁` does not. -/
private lemma zeta1_divisor_eq_zero_of_ne_zero {U : Set ℂ} {u : ℂ} (hu : u ∈ U)
    (h : riemannZeta₁ u ≠ 0) : MeromorphicOn.divisor riemannZeta₁ U u = 0 := by
  rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannZeta₁ U) hu]
  have h0 : meromorphicOrderAt riemannZeta₁ u = (0 : WithTop ℤ) :=
    (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff
      (differentiable_riemannZeta₁.analyticAt u).meromorphicNFAt).2 h
  rw [h0]
  simp

/-- A point with non-zero divisor (for a closed ball) is a zero of `ζ₁`. -/
private lemma zeta1_eq_zero_of_divisor_ne_zero {c : ℂ} {R : ℝ} {u : ℂ}
    (h : MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c R) u ≠ 0) :
    riemannZeta₁ u = 0 := by
  by_contra hz
  by_cases hu : u ∈ Metric.closedBall c R
  · exact h (zeta1_divisor_eq_zero_of_ne_zero hu hz)
  · exact h (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu)

/-- `ζ₁` is entire, so its divisor on any closed ball is nonnegative. -/
private lemma zeta1_divisor_nonneg (c : ℂ) (R : ℝ) (u : ℂ) :
    0 ≤ MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c R) u :=
  (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (analyticOnNhd_riemannZeta₁ _)) u

/-- **Pointwise comparison.**  Each summand of the window sum is bounded by the
corresponding summand of the inner divisor sum. -/
private lemma zeta1_window_term_le
    (hstrip : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ 0 → 0 < ρ.re ∧ ρ.re < 1)
    {t : ℝ} (ht : 5 ≤ |t|) (u : ℂ) :
    (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
        (if |u.im - t| ≤ 3 then 1 else 0)
      ≤ ((MeromorphicOn.divisor riemannZeta₁
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u : ℤ) : ℝ) := by
  by_cases hw : |u.im - t| ≤ 3
  · rw [if_pos hw]
    by_cases hD : MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6)) u = 0
    · rw [hD, Int.cast_zero, zero_mul]
      exact Int.cast_nonneg (zeta1_divisor_nonneg _ _ u)
    · have hz : riemannZeta₁ u = 0 := zeta1_eq_zero_of_divisor_ne_zero hD
      have him : u.im ≠ 0 := by
        have hge : (2 : ℝ) ≤ |u.im| := by
          have h1 : |t| - |u.im| ≤ |u.im - t| := by
            simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub t u.im
          linarith
        intro h0
        rw [h0, abs_zero] at hge
        norm_num at hge
      obtain ⟨hre, hre'⟩ := hstrip u hz him
      have hmemB : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10) :=
        zeta1_window_mem_inner_ball ht hre hre' hw
      have hmemA : u ∈ Metric.closedBall (0 : ℂ) (|t| + 6) := by
        by_contra h
        exact hD (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h)
      have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
        (f := riemannZeta₁) (a := (0 : ℂ)) (b := (2 : ℂ) + Complex.I * (t : ℂ))
        (ra := |t| + 6) (rb := 37 / 10) (analyticOnNhd_riemannZeta₁ _) hmemA hmemB
      rw [heq]
      simp
  · rw [if_neg hw, mul_zero]
    exact Int.cast_nonneg (zeta1_divisor_nonneg _ _ u)

/-- **The window sum is bounded by the divisor sum on the inner ball.**

All zeros of `ζ₁` inside the ball `B(0, |t|+6)` are among the finitely many zeros
enumeration `S`; those counted by the window lie in the inner ball `B(2+it, 37/10)`, where
the two divisors agree and where the divisor is nonnegative. -/
theorem zeta1_windowSum_le_inner_divisor
    (hstrip : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ 0 → 0 < ρ.re ∧ ρ.re < 1)
    {t : ℝ} (ht : 5 ≤ |t|) :
    (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0))
      ≤ ((∑ᶠ u : ℂ,
          MeromorphicOn.divisor riemannZeta₁
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u : ℤ) : ℝ) := by
  classical
  obtain ⟨S, hS⟩ := Commons.NumberTheory.Zeta.zetaZeroBall (|t| + 6) (by positivity)
  have hsuppL : Function.support (fun u : ℂ =>
      (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
        (if |u.im - t| ≤ 3 then 1 else 0)) ⊆ ↑S := by
    intro u hu
    rw [Function.mem_support] at hu
    have hD : MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6)) u ≠ 0 := by
      intro h0
      exact hu (by rw [h0]; simp)
    refine (hS u).mpr ⟨?_, zeta1_eq_zero_of_divisor_ne_zero hD⟩
    by_contra h
    exact hD (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h)
  have hsuppR : Function.support (fun u : ℂ =>
      MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u) ⊆ ↑S := by
    intro u hu
    rw [Function.mem_support] at hu
    have hmemB : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10) := by
      by_contra h
      exact hu (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h)
    exact (hS u).mpr ⟨zeta1_inner_ball_subset_closedBall ht hmemB,
      zeta1_eq_zero_of_divisor_ne_zero hu⟩
  have hL := finsum_eq_sum_of_support_subset (fun u : ℂ =>
      (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
        (if |u.im - t| ≤ 3 then 1 else 0)) hsuppL
  have hR := finsum_eq_sum_of_support_subset (fun u : ℂ =>
      MeromorphicOn.divisor riemannZeta₁
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u) hsuppR
  calc (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0))
      = ∑ u ∈ S, ((((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0)) := hL
    _ ≤ ∑ u ∈ S, ((MeromorphicOn.divisor riemannZeta₁
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u : ℤ) : ℝ) :=
        Finset.sum_le_sum (fun u _ => zeta1_window_term_le hstrip ht u)
    _ = ((∑ u ∈ S, MeromorphicOn.divisor riemannZeta₁
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u : ℤ) : ℝ) :=
        (Int.cast_sum S _).symm
    _ = ((∑ᶠ u : ℂ, MeromorphicOn.divisor riemannZeta₁
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (37 / 10)) u : ℤ) : ℝ) := by rw [hR]

end Work.LinnikAreas.Zeta1Aux
