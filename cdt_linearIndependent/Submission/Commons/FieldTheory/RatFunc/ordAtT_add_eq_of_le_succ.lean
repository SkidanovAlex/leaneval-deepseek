import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_ge
import Submission.Commons.FieldTheory.RatFunc.ordAtT_eq_top_iff
import Submission.Commons.FieldTheory.RatFunc.ordAtT_neg
import Submission.Commons.FieldTheory.RatFunc.ordAt_add_of_lt

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- Strict dominance for `ordAtT`: a summand of strictly larger order does not change the order
of the sum. -/
theorem ordAtT_add_eq_of_le_succ {K : Type*} [Field K] {α : K} {x y : RatFunc K} {N : ℤ}
    (hx : ordAtT α x = (N : WithTop ℤ)) (hy : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α y) :
    ordAtT α (x + y) = (N : WithTop ℤ) := by
  have hxne : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp [ordAtT] at hx
  have hxord : ordAt α x = N := by
    have h := ordAtT_def α hxne
    rw [hx] at h
    exact_mod_cast h.symm
  rcases eq_or_ne y 0 with hy0 | hyne
  · subst hy0
    rw [add_zero]
    exact hx
  · have hyord : N + 1 ≤ ordAt α y := by
      have h := ordAtT_def α hyne
      rw [h] at hy
      exact_mod_cast hy
    have hsumne : x + y ≠ 0 := by
      intro h
      have hyneg : y = -x := eq_neg_of_add_eq_zero_right h
      have : ordAt α y = N := by rw [hyneg, ordAt_neg, hxord]
      linarith
    have hlt : ordAt α x < ordAt α y := by rw [hxord]; linarith
    rw [ordAtT_def α hsumne, ordAt_add_of_lt α hxne hyne hlt, hxord]

end Commons.FieldTheory.RatFunc
