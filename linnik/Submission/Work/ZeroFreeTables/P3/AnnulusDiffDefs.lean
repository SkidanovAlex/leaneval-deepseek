/-
# ZeroFreeTables/P3/AnnulusDiffDefs — the annulus divisor of the completed L-function

The `P₃` engine needs the bound (HB §8/§9) on the *annulus part* of the partial-fraction
expansion of `Λ'/Λ`,

`Σ_{R < ‖u‖ ≤ R'} mult(u) · (1/(s-u))^{k+1}`,

where the sum runs over the zeros of the completed L-function `Λ = completedLFunction χ`
lying in the annulus between the two balls `closedBall 0 R` and `closedBall 0 R'`.

This module collects the two definitions (`annulusDivisor`, the integer-valued difference
of the two ball divisors, and `annulusMass`, its absolute value written in the form in
which the counting bounds are consumed) together with the elementary pointwise facts:

* the annulus divisor vanishes on `‖u‖ ≤ R` and equals the divisor of the outer ball when
  `R < ‖u‖`;
* the annulus mass is nonnegative and finitely supported, and its real value is the cast of
  the annulus divisor;
* the indicator of a ball times the annulus mass is dominated by the divisor over that ball
  (the form in which the zero-count bounds of the completed L-function apply).
-/
import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

open scoped Classical BigOperators

noncomputable section
namespace Work.ZeroFreeTables.P3

variable {N : ℕ} [NeZero N]

/-- The divisor of the completed L-function over the *annulus* `R < ‖u‖ ≤ R'`, as the
difference of the divisors over the two closed balls. -/
def annulusDivisor (χ : DirichletCharacter ℂ N) (R R' : ℝ) (u : ℂ) : ℤ :=
  (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R')) u -
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u

/-- The mass of that annulus: the multiplicity of `u` as a zero of the completed L-function
when `R < ‖u‖`, and `0` otherwise.  For `R ≤ R'` this is the absolute value of
`annulusDivisor` (see `annulusDivisor_cast_eq`). -/
def annulusMass (χ : DirichletCharacter ℂ N) (R R' : ℝ) (u : ℂ) : ℝ :=
  if R < ‖u‖ then
    (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R')) u : ℤ) : ℝ)
  else 0

/-- Membership in a ball centred at the origin, in terms of the norm. -/
lemma mem_closedBall_zero_iff_norm (u : ℂ) (ρ : ℝ) :
    u ∈ Metric.closedBall (0 : ℂ) ρ ↔ ‖u‖ ≤ ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]

/-- The divisor coefficient vanishes away from its ball. -/
lemma divisor_eq_zero_of_not_mem {f : ℂ → ℂ} {a u : ℂ} {ρ : ℝ}
    (h : u ∉ Metric.closedBall a ρ) :
    MeromorphicOn.divisor f (Metric.closedBall a ρ) u = 0 := by
  rw [MeromorphicOn.divisor_def, if_neg]
  exact fun hh => h hh.2

/-- On the ball `closedBall 0 R` the annulus divisor vanishes. -/
lemma annulusDivisor_eq (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {R R' : ℝ} (hR : R ≤ R')
    (u : ℂ) :
    annulusDivisor χ R R' u =
      if R < ‖u‖ then
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R')) u
      else 0 := by
  by_cases h : R < ‖u‖
  · have hnotmem : u ∉ Metric.closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff_norm]; exact not_le.mpr h
    rw [annulusDivisor, divisor_eq_zero_of_not_mem hnotmem, if_pos h, sub_zero]
  · have huR : u ∈ Metric.closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff_norm]; exact not_lt.mp h
    have huR' : u ∈ Metric.closedBall (0 : ℂ) R' := by
      rw [mem_closedBall_zero_iff_norm] at huR ⊢; exact le_trans huR hR
    have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
      (f := DirichletCharacter.completedLFunction χ)
      (Commons.NumberTheory.Linnik.completedLFunction_analyticOnNhd χ hχ
        (Metric.closedBall (0 : ℂ) R ∪ Metric.closedBall (0 : ℂ) R')) huR huR'
    rw [annulusDivisor, heq, sub_self, if_neg h]

/-- The annulus mass is nonnegative. -/
lemma annulusMass_nonneg (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (R R' : ℝ) (u : ℂ) :
    0 ≤ annulusMass χ R R' u := by
  rw [annulusMass]
  by_cases h : R < ‖u‖
  · rw [if_pos h]
    by_cases hb : u ∈ Metric.closedBall (0 : ℂ) R'
    · exact Commons.NumberTheory.Linnik.divisor_real_nonneg_of_analyticOnNhd
        (Commons.NumberTheory.Linnik.completedLFunction_analyticOnNhd χ hχ _) hb
    · rw [divisor_eq_zero_of_not_mem hb]; simp
  · rw [if_neg h]

/-- The annulus mass is finitely supported. -/
lemma annulusMass_finiteSupport (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (R R' : ℝ) :
    Function.HasFiniteSupport (annulusMass χ R R') := by
  refine (Commons.NumberTheory.Linnik.divisor_real_finiteSupport χ hχ (0 : ℂ) R').subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  rw [annulusMass] at hu
  by_cases h : R < ‖u‖
  · rwa [if_pos h] at hu
  · rw [if_neg h] at hu
    exact absurd rfl hu

/-- The annulus divisor, cast to a real number, is the annulus mass. -/
lemma annulusDivisor_cast_eq (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {R R' : ℝ}
    (hR : R ≤ R') (u : ℂ) :
    ((annulusDivisor χ R R' u : ℤ) : ℝ) = annulusMass χ R R' u := by
  rw [annulusDivisor_eq χ hχ hR u, annulusMass]
  by_cases h : R < ‖u‖ <;> simp [h]

/-- The annulus mass is nonnegative on the ball `closedBall 0 ρ`. -/
lemma divisor_real_nonneg (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (ρ : ℝ) (u : ℂ) :
    0 ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 ρ)) u : ℤ) : ℝ) := by
  by_cases hb : u ∈ Metric.closedBall (0 : ℂ) ρ
  · exact Commons.NumberTheory.Linnik.divisor_real_nonneg_of_analyticOnNhd
      (Commons.NumberTheory.Linnik.completedLFunction_analyticOnNhd χ hχ _) hb
  · rw [divisor_eq_zero_of_not_mem hb]; simp

/-- The indicator of a ball times the annulus mass is dominated by the divisor over that
ball.  This is the form in which the zero-count bounds apply. -/
lemma indicator_annulusMass_le_divisor (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {R R' : ℝ}
    (hR : R ≤ R') (ρ : ℝ) (u : ℂ) :
    Set.indicator (Metric.closedBall (0 : ℂ) ρ) (annulusMass χ R R') u ≤
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 ρ)) u : ℤ) : ℝ) := by
  rw [Set.indicator_apply]
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) ρ
  · rw [if_pos hu, annulusMass]
    by_cases h : R < ‖u‖
    · rw [if_pos h]
      by_cases hb : u ∈ Metric.closedBall (0 : ℂ) R'
      · have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
          (f := DirichletCharacter.completedLFunction χ)
          (Commons.NumberTheory.Linnik.completedLFunction_analyticOnNhd χ hχ
            (Metric.closedBall (0 : ℂ) ρ ∪ Metric.closedBall (0 : ℂ) R')) hu hb
        rw [heq]
      · rw [divisor_eq_zero_of_not_mem hb]
        simp only [Int.cast_zero]
        exact divisor_real_nonneg χ hχ ρ u
    · rw [if_neg h]
      exact divisor_real_nonneg χ hχ ρ u
  · rw [if_neg hu]
    exact divisor_real_nonneg χ hχ ρ u

end Work.ZeroFreeTables.P3
