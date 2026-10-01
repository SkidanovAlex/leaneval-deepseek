import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l63

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables

/-- Real part of `∫₀^{x₀} f` as a complex integral. -/
private lemma re_integral_ofReal (f : ℝ → ℝ) (x₀ : ℝ) :
    (∫ t in (0:ℝ)..x₀, ((f t : ℝ) : ℂ)).re = ∫ t in (0:ℝ)..x₀, f t := by
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]

theorem winSumTwoMul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ L δ β₁ : ℝ} (hL : 0 ≤ L) (hδ1 : δ < 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hwin : ‖(1:ℂ) - (β₁ : ℂ)‖ ≤ δ)
    (hcoeff : (2 : ℤ) ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2))) (β₁ : ℂ))
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) - u‖ ≤ δ → u.re ≤ β₁) :
    2 * (∫ t in (0:ℝ)..x₀, f t)
      ≤ Commons.NumberTheory.Linnik.winSum χ f x₀ L δ (β₁ : ℂ) := by
  classical
  rw [Commons.NumberTheory.Linnik.winSum]
  set T : ℂ → ℝ := fun u =>
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-((((β₁ : ℂ) - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        else 0) with hT
  change 2 * (∫ t in (0:ℝ)..x₀, f t) ≤ ∑ᶠ u : ℂ, T u
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hDnn : ∀ u : ℂ, (0 : ℤ) ≤ (MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2))) u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg han u
  have hzshift : ∀ u : ℂ, u.re ≤ β₁ → 0 ≤ (((β₁ : ℂ) - u) * L).re := by
    intro u hu
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h1 : 0 ≤ ((β₁ : ℂ) - u).re := by
      rw [Complex.sub_re, Complex.ofReal_re]; linarith
    exact mul_nonneg h1 hL
  have hwincond : ∀ u : ℂ,
      ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → ‖(1:ℂ) - u‖ ≤ δ := by
    intro u hu
    simpa only [Complex.ofReal_im, Complex.ofReal_zero, zero_mul, add_zero] using hu
  have hTnn : ∀ u : ℂ, 0 ≤ T u := by
    intro u
    simp only [hT]
    by_cases hdu : (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2))) u = 0
    · rw [hdu]; simp
    · by_cases hw : ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [if_pos hw]
        exact mul_nonneg (by exact_mod_cast hDnn u)
          (hF (((β₁ : ℂ) - u) * L) (hzshift u (hzero u hdu (hwincond u hw))))
      · rw [if_neg hw]; simp
  have hTβ1 : 2 * (∫ t in (0:ℝ)..x₀, f t) ≤ T (β₁ : ℂ) := by
    simp only [hT]
    have hw' : ‖(1:ℂ) + (((β₁ : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ := by
      simpa only [Complex.ofReal_im, Complex.ofReal_zero, zero_mul, add_zero] using hwin
    rw [if_pos hw']
    have hDβ : (2 : ℝ) ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2))) (β₁ : ℂ) : ℤ) : ℝ) := by
      exact_mod_cast hcoeff
    have hF0 : (∫ t in (0:ℝ)..x₀,
          Complex.exp (-((((β₁ : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
        = ∫ t in (0:ℝ)..x₀, f t := by
      have h1 : (fun t : ℝ =>
            Complex.exp (-((((β₁ : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ))
          = (fun t : ℝ => ((f t : ℝ) : ℂ)) := by
        funext t; simp
      rw [h1, re_integral_ofReal]
    rw [hF0]
    have hIf : 0 ≤ ∫ t in (0:ℝ)..x₀, f t := by
      have h0 := hF 0 (by simp)
      have h1 : (fun t : ℝ => Complex.exp (-((0 : ℂ) * (t : ℂ))) * ((f t : ℝ) : ℂ))
          = (fun t : ℝ => ((f t : ℝ) : ℂ)) := by
        funext t; simp
      rw [h1, re_integral_ofReal] at h0
      exact h0
    exact mul_le_mul_of_nonneg_right hDβ hIf
  have hTfin : (Function.support T).Finite := by
    have hDfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β₁ : ℂ)).im| + 2)) u)).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2))
        (V := Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2))
        (fun z _ => ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z).meromorphicAt)
        (isCompact_closedBall 0 _) (subset_refl _)
    refine hDfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    simp only [hT]
    rw [h0]
    simp
  rcases eq_or_lt_of_le (hTnn (β₁ : ℂ)) with h0 | h0
  · exact le_trans hTβ1 (le_trans (le_of_eq h0.symm) (finsum_nonneg hTnn))
  · have hmem : (β₁ : ℂ) ∈ Function.support T := Function.mem_support.mpr (ne_of_gt h0)
    have heq := finsum_eq_sum_of_support_subset T (s := hTfin.toFinset)
      (fun x hx => hTfin.mem_toFinset.mpr hx)
    rw [heq]
    exact le_trans hTβ1 (Finset.single_le_sum (fun i _ => hTnn i) (hTfin.mem_toFinset.mpr hmem))

end Work.ZeroFreeTables
