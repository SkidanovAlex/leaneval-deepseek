import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_ZSBase

/-!
# The critical strip for the zeros of `Ξ`

`Work.LinnikAreas.DhK.Xi` is the entire completion `Ξ(s) = 1/2 + (1/2)s(s-1)Λ₀(s)` of the Riemann
zeta function, so that `Ξ s = (1/2) s (s-1) Λ s` for `s ≠ 0, 1` (`Xi_eq_half_mul`), and
`Ξ (1 - s) = Ξ s`.  Here we record:

* `Xi_one : Ξ 1 = 1/2`;
* `Xi_ne_zero_of_one_le_re : Ξ` has no zeros with `1 ≤ Re s`;
* `Xi_eq_one_sub : Ξ (1 - s) = Ξ s` (functional equation, in the `Λ₀` normalisation);
* `Xi_zero_strip :` every zero of `Ξ` has `0 < Re u < 1`.
-/

open scoped Classical BigOperators
open Filter

noncomputable section

namespace Work.LinnikAreas.DhExplicit

open Work.LinnikAreas.DhK

/-- `Ξ 1 = 1/2`. -/
lemma Xi_one : Xi 1 = 1 / 2 := by
  simp [Xi]

/-- `Ξ` has no zeros in the closed half-plane `Re s ≥ 1`. -/
lemma Xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : Xi s ≠ 0 := by
  intro h
  by_cases hs1 : s = 1
  · rw [hs1, Xi_one] at h
    norm_num at h
  · have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hs
      norm_num at hs
    have hΛ : completedRiemannZeta s ≠ 0 := by
      intro hz
      exact riemannZeta_ne_zero_of_one_le_re hs
        (by rw [riemannZeta_def_of_ne_zero hs0, hz, zero_div])
    rw [Xi_eq_half_mul s hs0 hs1] at h
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0)
      (sub_ne_zero.mpr hs1)) hΛ) h

/-- Functional equation of `Ξ` in the `Λ₀` normalisation: `Ξ (1 - s) = Ξ s`. -/
lemma Xi_eq_one_sub (s : ℂ) : Xi (1 - s) = Xi s := by
  by_cases h0 : s = 0
  · subst h0
    rw [sub_zero, Xi_one, Xi_zero]
  by_cases h1 : s = 1
  · subst h1
    rw [sub_self, Xi_zero, Xi_one]
  have h0' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1' : 1 - s ≠ 1 := by
    intro h
    exact h0 (by linear_combination -h)
  rw [Xi_eq_half_mul (1 - s) h0' h1', Xi_eq_half_mul s h0 h1, completedRiemannZeta_one_sub]
  ring

/-- Every zero of `Ξ` lies in the open critical strip `0 < Re u < 1`. -/
lemma Xi_zero_strip {u : ℂ} (h : Xi u = 0) : 0 < u.re ∧ u.re < 1 := by
  have hlt : u.re < 1 := by
    by_contra hc
    exact Xi_ne_zero_of_one_le_re (not_lt.mp hc) h
  refine ⟨?_, hlt⟩
  by_contra hc
  have hge : 1 ≤ (1 - u).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [not_lt.mp hc]
  have hz : Xi (1 - u) = 0 := by rw [Xi_eq_one_sub, h]
  exact Xi_ne_zero_of_one_le_re hge hz

end Work.LinnikAreas.DhExplicit
