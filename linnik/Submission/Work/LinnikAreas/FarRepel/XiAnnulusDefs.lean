import Mathlib
import Submission.Work.LinnikAreas.DhK.XiAux

/-!
# `Work.LinnikAreas.FarRepel.XiAnnulusDefs`

Vocabulary for the annulus bound on the partial-fraction sum of `Ξ` (`DhK.Xi`):

* `xiAnnulusDivisor R R' u` — the divisor of `Ξ` over the annulus `R < ‖u‖ ≤ R'`, realised as
  the difference of the divisors over the two closed balls `closedBall 0 R'` and
  `closedBall 0 R`;
* `xiAnnulusMass R R' u` — the mass of that annulus, `0` for `‖u‖ ≤ R` and the (nonnegative)
  multiplicity of `u` as a zero of `Ξ` otherwise.

The elementary facts collected here are the exact analogues of the `P₃` file
`Work.ZeroFreeTables.P3.AnnulusDiffDefs` with the completed `L`-function replaced by `Ξ`.
-/

open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas.FarRepel

/-- The divisor of `Ξ` over the annulus `R < ‖u‖ ≤ R'`, as the difference of the two ball
divisors. -/
def xiAnnulusDivisor (R R' : ℝ) (u : ℂ) : ℤ :=
  MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) R') u -
    MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) R) u

/-- The mass of the annulus `R < ‖u‖`: the multiplicity of `u` as a zero of `Ξ` when `R < ‖u‖`,
and `0` otherwise.  For `R ≤ R'` this is the real cast of `xiAnnulusDivisor`. -/
def xiAnnulusMass (R R' : ℝ) (u : ℂ) : ℝ :=
  if R < ‖u‖ then
    (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) R')) u : ℤ) : ℝ)
  else 0

/-- Membership in a ball centred at the origin, in terms of the norm. -/
lemma xi_mem_closedBall_zero_iff_norm (u : ℂ) (ρ : ℝ) :
    u ∈ Metric.closedBall (0 : ℂ) ρ ↔ ‖u‖ ≤ ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]

/-- The divisor coefficient vanishes away from its ball. -/
lemma xi_divisor_eq_zero_of_not_mem {u : ℂ} {ρ : ℝ}
    (h : u ∉ Metric.closedBall (0 : ℂ) ρ) :
    MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) ρ) u = 0 :=
  Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem h

/-- The real cast of the ball divisor of `Ξ` is nonnegative. -/
lemma xi_divisor_real_nonneg (ρ : ℝ) (u : ℂ) :
    0 ≤ (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
      (Metric.closedBall (0 : ℂ) ρ)) u : ℤ) : ℝ) := by
  by_cases hb : u ∈ Metric.closedBall (0 : ℂ) ρ
  · exact Commons.NumberTheory.Linnik.divisor_real_nonneg_of_analyticOnNhd
      (Work.LinnikAreas.DhK.Xi_analyticOnNhd _) hb
  · rw [xi_divisor_eq_zero_of_not_mem hb]; simp

/-- The real-valued ball divisor of `Ξ` has finite support. -/
lemma xiDivisorReal_finiteSupport (ρ : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall (0 : ℂ) ρ)) u : ℤ) : ℝ)) := by
  refine (Work.LinnikAreas.DhK.Xi_divisor_support_finite ρ).subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro h0
  exact hu (by rw [h0]; simp)

/-- The annulus mass is nonnegative. -/
lemma xiAnnulusMass_nonneg (R R' : ℝ) (u : ℂ) : 0 ≤ xiAnnulusMass R R' u := by
  rw [xiAnnulusMass]
  by_cases h : R < ‖u‖
  · rw [if_pos h]
    by_cases hb : u ∈ Metric.closedBall (0 : ℂ) R'
    · exact Commons.NumberTheory.Linnik.divisor_real_nonneg_of_analyticOnNhd
        (Work.LinnikAreas.DhK.Xi_analyticOnNhd _) hb
    · rw [xi_divisor_eq_zero_of_not_mem hb]; simp
  · rw [if_neg h]

/-- The annulus mass has finite support. -/
lemma xiAnnulusMass_finiteSupport (R R' : ℝ) :
    Function.HasFiniteSupport (xiAnnulusMass R R') := by
  refine (Work.LinnikAreas.DhK.Xi_divisor_support_finite R').subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro h0
  apply hu
  rw [xiAnnulusMass]
  by_cases h : R < ‖u‖
  · rw [if_pos h, h0]; simp
  · rw [if_neg h]

/-- The annulus divisor, cast to a real number, is the annulus mass (for `R ≤ R'`). -/
lemma xiAnnulusDivisor_cast_eq {R R' : ℝ} (hR : R ≤ R') (u : ℂ) :
    ((xiAnnulusDivisor R R' u : ℤ) : ℝ) = xiAnnulusMass R R' u := by
  rw [xiAnnulusDivisor, xiAnnulusMass]
  by_cases h : R < ‖u‖
  · have hnotmem : u ∉ Metric.closedBall (0 : ℂ) R := by
      rw [xi_mem_closedBall_zero_iff_norm]; exact not_le.mpr h
    rw [xi_divisor_eq_zero_of_not_mem hnotmem, sub_zero, if_pos h]
  · rw [if_neg h]
    have huR : ‖u‖ ≤ R := not_lt.mp h
    have huR' : ‖u‖ ≤ R' := le_trans huR hR
    have heq := Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le
      (f := Work.LinnikAreas.DhK.Xi) Work.LinnikAreas.DhK.Xi_meromorphicOn huR huR'
    rw [← heq, sub_self]
    simp

end Work.LinnikAreas.FarRepel
