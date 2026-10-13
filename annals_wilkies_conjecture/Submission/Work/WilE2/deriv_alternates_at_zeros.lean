/-
  Work.WilE2 — the analytic content of the Khovanskii–Rolle step.

  Let `φ : ℝ → ℝ` be continuous and `T`-periodic, and suppose its zeros in the fundamental
  interval `[0, T)` are exactly the range of a strictly increasing `u : Fin p → ℝ`, with every zero
  simple (`deriv φ (u j) ≠ 0`).  Then consecutive zeros in the cyclic order are crossed in opposite
  directions: `deriv φ (u j) * deriv φ (u (cycSucc hp j)) < 0`.

  This is the one–dimensional fact behind "consecutive roots of the old system have opposite
  orientations" used in the Khovanskii elimination; it is the hypothesis `halt` of
  `Work.WilE2.exists_level_points_periodic`.

  The argument is: between two consecutive zeros `φ` has constant sign (any further zero would
  contradict the enumeration), and at a simple zero the sign of the derivative is the direction in
  which `φ` crosses; consecutive zeros therefore have opposite crossing directions.
-/
import Mathlib
import Submission.Work.WilE2.Rolle
import Submission.Work.WilE2.NextPoint
import Submission.Work.WilE2.deriv_mul_neg_of_simple_zeros
import Submission.Work.WilE2.nextPt_ne_zero

set_option autoImplicit false

namespace Work.WilE2

open Set

/-- Translation by a period does not change the derivative: if `φ` is `T`-periodic and
`HasDerivAt φ c x`, then also `HasDerivAt φ c (x + T)`. -/
theorem hasDerivAt_add_period {φ : ℝ → ℝ} {T c x : ℝ} (hper : ∀ t, φ (t + T) = φ t)
    (h : HasDerivAt φ c x) : HasDerivAt φ c (x + T) := by
  have hfun : (fun y : ℝ => φ (y + T)) = φ := funext hper
  have hdiff : DifferentiableAt ℝ φ (x + T) := by
    rw [differentiableAt_iff_comp_add_const (f := φ) (a := x + T) (b := T)]
    simp only [add_sub_cancel_right]
    rw [hfun]
    exact h.differentiableAt
  have hderiv : deriv φ (x + T) = c := by
    rw [show deriv φ (x + T) = deriv (fun y : ℝ => φ (y + T)) x from by
      rw [deriv_comp_add_const]]
    rw [hfun, h.deriv]
  rw [← hderiv]
  exact hasDerivAt_deriv_iff.mpr hdiff

theorem deriv_alternates_at_zeros {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hcont : Continuous φ)
    (hper : ∀ t, φ (t + T) = φ t) {p : ℕ} (hp : 0 < p) (u : Fin p → ℝ)
    (hmono : StrictMono u) (hrange : {t : ℝ | 0 ≤ t ∧ t < T ∧ φ t = 0} = Set.range u)
    (hdiff : ∀ j, DifferentiableAt ℝ φ (u j)) (hne : ∀ j, deriv φ (u j) ≠ 0) :
    ∀ j : Fin p, deriv φ (u j) * deriv φ (u (cycSucc hp j)) < 0 := by
  intro j
  -- the interval `(u j, nextPt hp T u j)` has endpoints that are zeros of `φ` and no other zeros
  obtain ⟨hab, hfb, hfa, hzero⟩ := nextPt_ne_zero hT hper hp u hmono hrange j
  have ha : HasDerivAt φ (deriv φ (u j)) (u j) := (hdiff j).hasDerivAt
  have hb : HasDerivAt φ (deriv φ (u (cycSucc hp j))) (nextPt hp T u j) := by
    rcases lt_or_ge ((j : ℕ) + 1) p with hlt | hge
    · -- the next zero lies inside `[0, T)`
      have hval : nextPt hp T u j = u (cycSucc hp j) := by
        rw [nextPt_of_lt hp T u j hlt]
        exact congrArg u (Fin.ext (cycSucc_of_lt hp j hlt)).symm
      rw [hval]
      exact (hdiff (cycSucc hp j)).hasDerivAt
    · -- wrap around: the next zero is `u 0 + T`, and the derivative is periodic
      have hnot : ¬ (j : ℕ) + 1 < p := by omega
      have hcyc : cycSucc hp j = ⟨0, hp⟩ := cycSucc_of_not_lt hp j hnot
      have hnp : nextPt hp T u j = u ⟨0, hp⟩ + T := nextPt_of_not_lt hp T u j hnot
      rw [hnp, hcyc]
      exact hasDerivAt_add_period hper (hdiff ⟨0, hp⟩).hasDerivAt
  exact deriv_mul_neg_of_simple_zeros hab hcont hfa hfb (fun x hx => hzero x hx.1 hx.2) ha hb
    (hne j) (hne (cycSucc hp j))

end Work.WilE2
