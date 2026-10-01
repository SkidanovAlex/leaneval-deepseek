/-
# `WindowSumFinset` — multi-zero window retention for HB Lemma 5.2

`XY.WindowSumTwoWeak` and `Work.ZeroFreeTables.div_mul_kernel_le_windowSum` show that the
divisor-weighted kernel of *one* (or two) retained zeros lying in the Lemma-5.2 window
`‖1 + i·Im s - u‖ ≤ δ` of `s` is dominated by the full window sum, provided every other window
zero lies to the left of `s` (`Re u ≤ Re s`), so that its kernel is non-negative by Condition 2.

This file provides the direct `Finset`-set version needed by the order-2 `Nebenfall` inequality
(`XY/LamPrimeNebenfall`), where three (and later one) retained zeros are compared with the window
sum at once.  The proof is the bookkeeping one: every summand of the window sum is `≥ 0`, the
retained set lies in the divisor's support, and the `Finset` sum over the retained set is
therefore dominated by the `∑ᶠ` over the whole support.
-/
import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l52phi_imprim

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables.XY

/-- **Multi-zero window retention.**  If the retained zeros `u ∈ A` lie in the window
`‖1 + i·Im s - u‖ ≤ δ` of `s` and every window zero satisfies `Re u ≤ Re s` (so that all kernel
terms are non-negative by Condition 2), then the divisor-weighted sum of their kernels is at most
the full window sum. -/
theorem windowSum_finset_ge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ L : ℝ} {s : ℂ} {δ : ℝ} (hL : 0 ≤ L)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (A : Finset ℂ)
    (hdiv : ∀ u ∈ A, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0)
    (hwin : ∀ u ∈ A, ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ)
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re) :
    (∑ u ∈ A, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re))
      ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0) := by
  classical
  -- the two summands of the statement, as local definitions
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) u
  let K : ℂ → ℝ := fun u =>
      ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
  let G : ℂ → ℝ := fun u => ((D u : ℤ) : ℝ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then K u else 0)
  -- the divisor is non-negative on the ball
  have hDnn : ∀ u : ℂ, (0:ℝ) ≤ ((D u : ℤ) : ℝ) := by
    intro u
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u)
  -- every summand of the window sum is non-negative
  have hGnn : ∀ u : ℂ, 0 ≤ G u := by
    intro u
    show 0 ≤ ((D u : ℤ) : ℝ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then K u else 0)
    by_cases hd : D u = 0
    · rw [hd]; simp
    · by_cases hw : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [if_pos hw]
        have hre : u.re ≤ s.re := hzero u hd hw
        have hznn : 0 ≤ (((s - u) * L : ℂ)).re := by
          rw [Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          have : 0 ≤ (s - u).re := by rw [Complex.sub_re]; linarith
          exact mul_nonneg this hL
        exact mul_nonneg (hDnn u) (hF ((s - u) * L) hznn)
      · rw [if_neg hw]; simp
  -- the divisor has finite support on the ball
  have hDfin : (Function.support D).Finite := by
    have hmer : MeromorphicOn (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
      fun z _ =>
        ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z).meromorphicAt
    have h := MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall (0:ℂ) (|s.im| + 2))
      (V := Metric.closedBall (0:ℂ) (|s.im| + 2))
      hmer (isCompact_closedBall 0 (|s.im| + 2)) (subset_refl _)
    exact h.subset (by intro u hu; exact hu)
  have hsuppG : Function.support G ⊆ (hDfin.toFinset : Set ℂ) := by
    intro u hu
    rw [Set.Finite.coe_toFinset hDfin]
    refine Function.mem_support.mpr ?_
    intro hD0
    exact (Function.mem_support.mp hu) (by
      show G u = 0
      show ((D u : ℤ) : ℝ) * _ = 0
      rw [hD0]; simp)
  have hfinsum : (∑ᶠ u : ℂ, G u) = ∑ u ∈ hDfin.toFinset, G u :=
    finsum_eq_sum_of_support_subset G hsuppG
  have hGrw : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0)) = ∑ᶠ u : ℂ, G u := rfl
  rw [hGrw, hfinsum]
  have hAsub : A ⊆ hDfin.toFinset := by
    intro u hu
    exact hDfin.mem_toFinset.mpr (Function.mem_support.mpr (hdiv u hu))
  have hAcongr : (∑ u ∈ A, (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re))
      = ∑ u ∈ A, G u := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    show _ = ((D u : ℤ) : ℝ) * (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then K u else 0)
    rw [if_pos (hwin u hu)]
  rw [hAcongr]
  exact Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun i _ _ => hGnn i)

end Work.ZeroFreeTables.XY
