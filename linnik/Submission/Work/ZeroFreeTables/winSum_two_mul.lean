import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l63
import Submission.Work.LinnikContract.Defs
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

namespace Work.ZeroFreeTables

open DirichletCharacter Complex

open scoped Classical BigOperators

/-- The Laplace transform at `z = 0` of a real function `f` has real part the ordinary
real integral of `f`.  (`0` is the only point where no integrability hypothesis is needed.) -/
private lemma re_laplace_at_zero (f : ℝ → ℝ) (x₀ : ℝ) {z : ℂ} (hz : z = 0) :
    (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..x₀, f t := by
  rw [hz]
  simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal]
  simp

/-- The window sum of §6 at `β₁` carries the multiplicity of the zero `β₁`; for a zero of
multiplicity at least `2` it dominates twice the multiplicity-one contribution `∫₀^{x₀} f`. -/
theorem winSum_two_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    [NeZero χ.conductor]
    {f : ℝ → ℝ} {x₀ L δ β₁ : ℝ} (hL : 0 ≤ L) (hδ1 : δ < 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hβ₁δ : |1 - β₁| ≤ δ)
    (hmult : 2 ≤ Work.LinnikContract.zeroMult χ (β₁ : ℂ))
    (hzero : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 1 → u.re ≤ β₁) :
    2 * (∫ t in (0:ℝ)..x₀, f t)
      ≤ Commons.NumberTheory.Linnik.winSum χ.primitiveCharacter f x₀ L δ (β₁ : ℂ) := by
  classical
  -- the radius `|Im β₁| + 2` of the divisor of the window sum is just `2`
  have hR : |((β₁ : ℂ)).im| + 2 = 2 := by rw [Complex.ofReal_im]; norm_num
  -- the primitive character inducing `χ` is non-principal, so its completed `L`-function is entire
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ := χ), h1,
      DirichletCharacter.changeLevel_one]
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
  -- `zeroMult` is the order of vanishing of that completed `L`-function
  have hzm : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u
      = analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u := by
    intro u
    simp only [Work.LinnikContract.zeroMult]
  -- on the ball the divisor of that function is the multiplicity
  have hDval : ∀ u : ℂ, u ∈ Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2) →
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2)) u
        = (Work.LinnikContract.zeroMult χ u : ℤ) := by
    intro u hu
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu, hzm u]
  -- the window `‖1 - u‖ ≤ δ < 1` puts `u` in the ball and bounds its imaginary part
  have hball_of_win : ∀ u : ℂ, ‖(1:ℂ) - u‖ ≤ δ →
      u ∈ Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2) := by
    intro u hw
    have h1 : ‖u‖ ≤ 2 := by
      have h : ‖u‖ ≤ ‖(1:ℂ) - u‖ + 1 := by
        have hsub := norm_sub_le (1:ℂ) ((1:ℂ) - u)
        rw [show (1:ℂ) - ((1:ℂ) - u) = u by ring, norm_one] at hsub
        linarith
      linarith
    rw [Metric.mem_closedBall, dist_eq_norm, hR]
    simpa using h1
  have him_of_win : ∀ u : ℂ, ‖(1:ℂ) - u‖ ≤ δ → |u.im| ≤ 1 := by
    intro u hw
    have h1 : |u.im| = |((1:ℂ) - u).im| := by simp
    rw [h1]
    exact le_trans (le_trans (Complex.abs_im_le_norm _) hw) (le_of_lt hδ1)
  -- the real integral of `f` is non-negative
  have hF0 : 0 ≤ ∫ t in (0:ℝ)..x₀, f t := by
    have h := hF 0 (by simp)
    rwa [re_laplace_at_zero f x₀ rfl] at h
  -- the point `β₁` lies in the ball, and the divisor there is at least two
  have hβball : (β₁ : ℂ) ∈ Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2) := by
    apply hball_of_win
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hβ₁δ
  have hDβ : (2:ℤ) ≤ MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2)) (β₁ : ℂ) := by
    rw [hDval (β₁ : ℂ) hβball]
    exact_mod_cast hmult
  -- the summands of the window sum
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2)) u
  let T : ℂ → ℝ := fun u => (D u : ℤ) *
      (if ‖(1:ℂ) - u‖ ≤ δ then
        (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β₁ : ℂ) - u) * L) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re
      else 0)
  rw [Commons.NumberTheory.Linnik.winSum]
  simp only [Complex.ofReal_im, Complex.ofReal_zero, zero_mul, add_zero]
  change 2 * (∫ t in (0:ℝ)..x₀, f t) ≤ ∑ᶠ u : ℂ, T u
  -- the term at `β₁` alone is at least `2 ∫ f`
  have hTβ : 2 * (∫ t in (0:ℝ)..x₀, f t) ≤ T (β₁ : ℂ) := by
    have hwin : ‖(1:ℂ) - (β₁ : ℂ)‖ ≤ δ := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hβ₁δ
    have hinner : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β₁ : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
        = ∫ t in (0:ℝ)..x₀, f t :=
      re_laplace_at_zero f x₀ (by rw [sub_self, zero_mul])
    have h2 : (2:ℝ) ≤ ((D (β₁ : ℂ) : ℤ) : ℝ) := by
      have h := hDβ
      simp only [D] at h ⊢
      exact_mod_cast h
    simp only [T]
    rw [if_pos hwin, hinner]
    exact mul_le_mul_of_nonneg_right h2 hF0
  -- every summand is non-negative
  have hTnn : ∀ u : ℂ, 0 ≤ T u := by
    intro u
    by_cases hw : ‖(1:ℂ) - u‖ ≤ δ
    · have hball := hball_of_win u hw
      by_cases hz0 : Work.LinnikContract.zeroMult χ u = 0
      · -- the summand vanishes
        have hDu0 : D u = 0 := by
          rw [show D u = (Work.LinnikContract.zeroMult χ u : ℤ) from hDval u hball, hz0]
          simp
        simp only [T]
        rw [hDu0]
        simp
      · have hure : u.re ≤ β₁ := hzero u hz0 (him_of_win u hw)
        have hDge : (0:ℝ) ≤ (D u : ℤ) := by
          have h0 : (0:ℤ) ≤ D u := by
            rw [show D u = (Work.LinnikContract.zeroMult χ u : ℤ) from hDval u hball]
            exact_mod_cast Nat.zero_le _
          exact_mod_cast h0
        simp only [T]
        rw [if_pos hw]
        refine mul_nonneg hDge ?_
        apply hF
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        have hsub : 0 ≤ ((β₁ : ℂ) - u).re := by
          rw [Complex.sub_re, Complex.ofReal_re]
          linarith
        exact mul_nonneg hsub hL
    · simp only [T]
      rw [if_neg hw, mul_zero]
  -- the summand function is finitely supported
  have hTfin : (Function.support T).Finite := by
    have hDfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2)) u)).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (U := Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2))
        (V := Metric.closedBall (0:ℂ) (|((β₁ : ℂ)).im| + 2))
        (fun z _ =>
          ((DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z).meromorphicAt)
        (isCompact_closedBall 0 (|((β₁ : ℂ)).im| + 2)) (subset_refl _)
    refine hDfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    refine hu ?_
    have hDu0 : D u = 0 := by
      simp only [D]
      exact h0
    simp only [T]
    rw [hDu0]
    simp
  -- assemble
  rcases eq_or_lt_of_le (hTnn (β₁ : ℂ)) with h0 | h0
  · exact le_trans hTβ (le_trans (le_of_eq h0.symm) (finsum_nonneg hTnn))
  · have hmem : (β₁ : ℂ) ∈ Function.support T := Function.mem_support.mpr (ne_of_gt h0)
    have heq := finsum_eq_sum_of_support_subset T (s := hTfin.toFinset)
      (fun x hx => hTfin.mem_toFinset.mpr hx)
    rw [heq]
    exact le_trans hTβ (Finset.single_le_sum (fun i _ => hTnn i) (hTfin.mem_toFinset.mpr hmem))

end Work.ZeroFreeTables
