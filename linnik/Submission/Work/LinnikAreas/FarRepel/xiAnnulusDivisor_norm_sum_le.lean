import Mathlib
import Submission.Work.LinnikAreas.FarRepel.XiAnnulusDefs

/-!
# `Work.LinnikAreas.FarRepel.xiAnnulusDivisor_norm_sum_le`

The norm of the annulus divisor sum is bounded by the corresponding annulus mass sum.

Both sums are finite (their supports sit inside the finite support of the ball-`R'` divisor of
`Ξ`), so the statement is the triangle inequality plus the termwise identity

`‖((d : ℤ) : ℂ) * (1 / (s - u)) ^ n‖ = xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ n`

which holds because `xiAnnulusDivisor R R' u` is a nonnegative integer whose real cast is
`xiAnnulusMass R R' u`.
-/

open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas.FarRepel

/-- The termwise bound: the norm of a divisor summand is at most the corresponding mass
summand. -/
lemma xiAnnulusDivisor_term_norm_le (n : ℕ) (s : ℂ) {R R' : ℝ} (hR : R ≤ R') (u : ℂ) :
    ‖((xiAnnulusDivisor R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n‖
      ≤ xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ n := by
  have hd : (0 : ℝ) ≤ ((xiAnnulusDivisor R R' u : ℤ) : ℝ) := by
    rw [xiAnnulusDivisor_cast_eq hR u]; exact xiAnnulusMass_nonneg R R' u
  have hnormd : ‖((xiAnnulusDivisor R R' u : ℤ) : ℂ)‖ = xiAnnulusMass R R' u := by
    rw [Complex.norm_intCast, abs_of_nonneg hd, xiAnnulusDivisor_cast_eq hR u]
  have hnormp : ‖(1 / (s - u)) ^ n‖ = (1 / ‖s - u‖) ^ n := by
    rw [norm_pow, norm_div, norm_one]
  rw [norm_mul, hnormd, hnormp]

/-- The support of a divisor summand is contained in the support of the ball-`R'` divisor. -/
lemma xiAnnulusDivisor_summand_support_subset (n : ℕ) (s : ℂ) {R R' : ℝ} (hR : R ≤ R') :
    Function.support (fun u : ℂ =>
        ((xiAnnulusDivisor R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n)
      ⊆ Function.support (fun u : ℂ =>
          MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) R') u) := by
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro h0
  apply hu
  have hxi : xiAnnulusDivisor R R' u = 0 := by
    rw [xiAnnulusDivisor, h0]
    have hzero : MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall (0 : ℂ) R) u = 0 := by
      by_cases hb : u ∈ Metric.closedBall (0 : ℂ) R
      · have huR : ‖u‖ ≤ R := (xi_mem_closedBall_zero_iff_norm u R).mp hb
        have huR' : ‖u‖ ≤ R' := le_trans huR hR
        rw [Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le
          (f := Work.LinnikAreas.DhK.Xi) Work.LinnikAreas.DhK.Xi_meromorphicOn huR huR']
        exact h0
      · exact Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem hb
    rw [hzero, sub_zero]
  rw [hxi]; simp

/-- The support of a mass summand is contained in the support of the ball-`R'` divisor. -/
lemma xiAnnulusMass_summand_support_subset (n : ℕ) (s : ℂ) (R R' : ℝ) :
    Function.support (fun u : ℂ => xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ n)
      ⊆ Function.support (fun u : ℂ =>
          MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) R') u) := by
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro h0
  apply hu
  rw [xiAnnulusMass]
  split_ifs with h
  · rw [h0]; simp
  · simp

theorem xiAnnulusDivisor_norm_sum_le (n : ℕ) (s : ℂ) {R R' : ℝ} (hR : R ≤ R') :
    ‖∑ᶠ u : ℂ, ((xiAnnulusDivisor R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n‖
      ≤ ∑ᶠ u : ℂ, xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ n := by
  classical
  set S : Finset ℂ := (Work.LinnikAreas.DhK.Xi_divisor_support_finite R').toFinset with hS
  have hgmem : ∀ u : ℂ, u ∈ S ↔ MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
      (Metric.closedBall (0 : ℂ) R') u ≠ 0 := by
    intro u
    rw [hS, Set.Finite.mem_toFinset, Function.mem_support]
  have hg : Function.support (fun u : ℂ =>
      ((xiAnnulusDivisor R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n) ⊆ S :=
    fun u hu => (hgmem u).mpr
      (xiAnnulusDivisor_summand_support_subset n s hR hu)
  have hh : Function.support (fun u : ℂ => xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ n) ⊆ S :=
    fun u hu => (hgmem u).mpr (xiAnnulusMass_summand_support_subset n s R R' hu)
  rw [finsum_eq_sum_of_support_subset _ hg, finsum_eq_sum_of_support_subset _ hh]
  calc ‖∑ u ∈ S, ((xiAnnulusDivisor R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n‖
      ≤ ∑ u ∈ S, ‖((xiAnnulusDivisor R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ u ∈ S, xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ n :=
        Finset.sum_le_sum (fun u _ => xiAnnulusDivisor_term_norm_le n s hR u)

end Work.LinnikAreas.FarRepel
