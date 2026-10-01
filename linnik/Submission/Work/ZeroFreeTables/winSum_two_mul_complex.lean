/-
# ZeroFreeTables — winSum_two_mul_complex

The §6 window bound at a **complex** point: the generalisation of `winSum_two_mul` (there for a
real `β₁`) to an arbitrary `s : ℂ`.  It is the one new ingredient of the general repeated-zero
engine `HB6RepeatedGeneral` (see `NOTE_HB6RepeatedGeneral_repair.md`, §3): the doubled zero sits
at `u = s` itself, where the window term is `F(0) = ∫ f`, and its multiplicity `≥ 2` is what
produces the `−4F(0)` of the engine.
-/
import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l63
import Submission.Work.LinnikContract.Defs

open DirichletCharacter Complex Metric
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- The Laplace transform at `z = 0` of a real function has, as real part, the ordinary
integral of that function. -/
private lemma re_laplace_at_zero (f : ℝ → ℝ) (x₀ : ℝ) {z : ℂ} (hz : z = 0) :
    (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..x₀, f t := by
  rw [hz]
  simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal]
  simp

/-- **The window sum at a complex point carries the multiplicity.**  If the point `s` lies in
its own window, `‖1 + i·Im s − s‖ ≤ δ`, if `s` is a zero of multiplicity `≥ 2`, and if every
other zero in the window lies to the left of `s`, then the window sum at `s` is at least
`2·∫₀^{x₀} f`. -/
theorem winSum_two_mul_complex {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    [NeZero χ.conductor]
    {f : ℝ → ℝ} {x₀ L δ : ℝ} {s : ℂ} (hL : 0 ≤ L) (hδ1 : δ < 1)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - s‖ ≤ δ)
    (hmult : 2 ≤ Work.LinnikContract.zeroMult χ s)
    (hzero : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re) :
    2 * (∫ t in (0:ℝ)..x₀, f t)
      ≤ Commons.NumberTheory.Linnik.winSum χ.primitiveCharacter f x₀ L δ s := by
  classical
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ := χ), h1,
      DirichletCharacter.changeLevel_one]
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
  have hzm : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u
      = analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u := by
    intro u; simp only [Work.LinnikContract.zeroMult]
  have hDval : ∀ u : ℂ, u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) →
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) (|s.im| + 2)) u
        = (Work.LinnikContract.zeroMult χ u : ℤ) := by
    intro u hu
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu, hzm u]
  -- the centre `1 + i·Im s` of the window has norm at most `|Im s| + 1`
  have hcenter : ‖(1:ℂ) + (s.im : ℂ) * Complex.I‖ ≤ |s.im| + 1 := by
    have hsq : ‖(1:ℂ) + (s.im : ℂ) * Complex.I‖ ^ 2 = 1 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, mul_one, add_zero, zero_add]
      ring
    have hnn : (0:ℝ) ≤ ‖(1:ℂ) + (s.im : ℂ) * Complex.I‖ := norm_nonneg _
    nlinarith [hsq, hnn, abs_nonneg s.im, sq_abs s.im]
  -- the window puts its zero `u` in the divisor ball
  have hball_of_win : ∀ u : ℂ, ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ →
      u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := by
    intro u hw
    have hsub : (1:ℂ) + (s.im : ℂ) * Complex.I - ((1:ℂ) + (s.im : ℂ) * Complex.I - u) = u := by
      ring
    have h1 : ‖u‖ ≤ |s.im| + 2 := by
      have h := norm_sub_le ((1:ℂ) + (s.im : ℂ) * Complex.I) ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
      rw [hsub] at h
      linarith
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using h1
  -- the real integral of `f` is non-negative
  have hF0 : 0 ≤ ∫ t in (0:ℝ)..x₀, f t := by
    have h := hF 0 (by simp)
    rwa [re_laplace_at_zero f x₀ rfl] at h
  -- the divisor at `s` is at least two
  have hDs : (2:ℤ) ≤ MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|s.im| + 2)) s := by
    rw [hDval s (hball_of_win s hwin)]
    exact_mod_cast hmult
  -- the summands of the window sum
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|s.im| + 2)) u
  let T : ℂ → ℝ := fun u => (D u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re
      else 0)
  rw [Commons.NumberTheory.Linnik.winSum]
  change 2 * (∫ t in (0:ℝ)..x₀, f t) ≤ ∑ᶠ u : ℂ, T u
  -- the term at `s` alone is at least `2 ∫ f`
  have hTs : 2 * (∫ t in (0:ℝ)..x₀, f t) ≤ T s := by
    have hinner : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - s) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
        = ∫ t in (0:ℝ)..x₀, f t :=
      re_laplace_at_zero f x₀ (by rw [sub_self, zero_mul])
    have h2 : (2:ℝ) ≤ ((D s : ℤ) : ℝ) := by
      have h := hDs
      simp only [D] at h ⊢
      exact_mod_cast h
    simp only [T]
    rw [if_pos hwin, hinner]
    exact mul_le_mul_of_nonneg_right h2 hF0
  -- every summand is non-negative
  have hTnn : ∀ u : ℂ, 0 ≤ T u := by
    intro u
    by_cases hw : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
    · have hball : u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := hball_of_win u hw
      by_cases hz0 : Work.LinnikContract.zeroMult χ u = 0
      · have hDu0 : D u = 0 := by
          rw [show D u = (Work.LinnikContract.zeroMult χ u : ℤ) from hDval u hball, hz0]
          simp
        simp only [T]
        rw [hDu0]
        simp
      · have hure : u.re ≤ s.re := hzero u hz0 hw
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
        have hsub : 0 ≤ (s - u).re := by
          rw [Complex.sub_re]
          linarith
        exact mul_nonneg hsub hL
    · simp only [T]
      rw [if_neg hw, mul_zero]
  -- the summand function is finitely supported
  have hTfin : (Function.support T).Finite := by
    have hDfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) (|s.im| + 2)) u)).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (U := Metric.closedBall (0:ℂ) (|s.im| + 2))
        (V := Metric.closedBall (0:ℂ) (|s.im| + 2))
        (fun z _ =>
          AnalyticAt.meromorphicAt ((DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z))
        (isCompact_closedBall 0 (|s.im| + 2)) (subset_refl _)
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
  rcases eq_or_lt_of_le (hTnn s) with h0 | h0
  · exact le_trans hTs (le_trans (le_of_eq h0.symm) (finsum_nonneg hTnn))
  · have hmem : s ∈ Function.support T := Function.mem_support.mpr (ne_of_gt h0)
    have heq := finsum_eq_sum_of_support_subset T (s := hTfin.toFinset)
      (fun x hx => hTfin.mem_toFinset.mpr hx)
    rw [heq]
    exact le_trans hTs (Finset.single_le_sum (fun i _ => hTnn i) (hTfin.mem_toFinset.mpr hmem))

end Work.ZeroFreeTables
