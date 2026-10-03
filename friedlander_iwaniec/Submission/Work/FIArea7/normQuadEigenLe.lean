import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The support of the quadratic eigenvalue `λ(n)`: the Gaussian integers in the box `gBox n`
with `|z|² = n` that are primary. -/
def quadSupp (n : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (n : ℤ)).filter
    (fun z => Work.FIPlan.gnorm z = n ∧ Work.FIPlan.IsPrimary z)

/-- `quadEigen` is the sum of `ψ z · [z]` over the support `quadSupp n`. -/
lemma quadEigen_eq_sum_quadSupp (psi : GaussianInt → ℂ) (n : ℕ) :
    quadEigen psi n = ∑ z ∈ quadSupp n, psi z * JKSym z := by
  rw [quadEigen, quadSupp, Finset.sum_filter]

/-- The trivial bound: `‖λ(n)‖` is at most the number of terms in its support. -/
lemma norm_quadEigen_le_card (psi : GaussianInt → ℂ) (hpsi : ∀ z, ‖psi z‖ ≤ 1) (n : ℕ) :
    ‖quadEigen psi n‖ ≤ ((quadSupp n).card : ℝ) := by
  rw [quadEigen_eq_sum_quadSupp]
  have hterm : ∀ z ∈ quadSupp n, ‖psi z * JKSym z‖ ≤ (1 : ℝ) := by
    intro z _
    calc ‖psi z * JKSym z‖ = ‖psi z‖ * ‖JKSym z‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hpsi z) (norm_JKSym_le_one z) (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
  calc ‖∑ z ∈ quadSupp n, psi z * JKSym z‖
      ≤ ∑ z ∈ quadSupp n, ‖psi z * JKSym z‖ := norm_sum_le _ _
    _ ≤ ∑ _z ∈ quadSupp n, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((quadSupp n).card : ℝ) := by simp

/-- At most `4 τ(n)` Gaussian integers of norm `n` lie in the primary quadrant. -/
lemma quadSupp_card_le (n : ℕ) : (quadSupp n).card ≤ 4 * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hempty : quadSupp 0 = ∅ := by
      rw [quadSupp, Finset.filter_eq_empty_iff]
      intro z _ hP
      have hz0 : z = 0 := gnorm_eq_zero_iff.mp hP.1
      subst hz0
      exact absurd hP.2 (by simp [Work.FIPlan.IsPrimary])
    rw [hempty]
    simp
  · have hsub : quadSupp n ⊆ Commons.NumberTheory.GaussianInt.elemF n := by
      intro z hz
      rw [quadSupp, Finset.mem_filter] at hz
      rw [Commons.NumberTheory.GaussianInt.mem_elemF hn z]
      simpa [Work.FIPlan.gnorm] using hz.2.1
    have h1 : (quadSupp n).card ≤ (Commons.NumberTheory.GaussianInt.elemF n).card :=
      Finset.card_le_card hsub
    rw [← Commons.NumberTheory.GaussianInt.targetF_card_eq_elemF_card n] at h1
    refine le_trans h1 ?_
    have h := Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos n hn
    exact_mod_cast h

/-- **Size of the quadratic eigenvalue.**  For a coefficient function with `‖ψ‖ ≤ 1`, the level-set
sum `λ(n) = Σ^∧_{z z̄ = n} ψ(z)[z]` over primary `z` of norm `n` satisfies `‖λ(n)‖ ≤ 4 τ(n)`: there
are at most `r₂(n) ≤ 4 τ(n)` Gaussian integers of norm `n`, and `r₂(n) ≤ 4 τ(n)` follows from the
injective map `z ↦ z.re + z.im` from the quadrant `{0 ≤ re, 0 ≤ im}` into the divisors of `n`
(`(re + im)(re - im) = n`) together with the free action of the four units. -/
theorem normQuadEigenLe (psi : GaussianInt → ℂ) (hpsi : ∀ z, ‖psi z‖ ≤ 1) (n : ℕ) :
    ‖quadEigen psi n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) := by
  refine le_trans (norm_quadEigen_le_card psi hpsi n) ?_
  have h := quadSupp_card_le n
  have hcast : ((quadSupp n).card : ℝ) ≤ ((4 * n.divisors.card : ℕ) : ℝ) := by
    exact_mod_cast h
  simpa using hcast

end

end Work.FIArea7
