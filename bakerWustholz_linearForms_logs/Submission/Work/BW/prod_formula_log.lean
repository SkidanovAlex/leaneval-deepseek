import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- **Logarithmic product formula for a number field.**
For `x ≠ 0`, the sum of `mult v · log |x|_v` over the infinite places plus the sum of
`log |x|_v` over the (finitely supported) finite places vanishes. This is the logarithm of
`NumberField.prod_abs_eq_one`. -/
theorem prod_formula_log {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    (∑ v : NumberField.InfinitePlace K, ((v.mult : ℕ) : ℝ) * Real.log (v x)) +
      ∑ᶠ v : NumberField.FinitePlace K, Real.log (v x) = 0 := by
  have hI : ∀ w : NumberField.InfinitePlace K, 0 < w x ^ w.mult :=
    fun w => pow_pos (NumberField.InfinitePlace.pos_iff.mpr hx) _
  have hF : ∀ w : NumberField.FinitePlace K, 0 < w x :=
    fun w => NumberField.FinitePlace.pos_iff.mpr hx
  have hprod : (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) *
      ∏ᶠ w : NumberField.FinitePlace K, w x = 1 := NumberField.prod_abs_eq_one hx
  have hlog := congrArg Real.log hprod
  rw [Real.log_one] at hlog
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun w _ => (hI w).ne')
      (finprod_ne_zero fun w => (hF w).ne'),
    Real.log_prod (s := Finset.univ)
      (f := fun w : NumberField.InfinitePlace K => (w x) ^ w.mult)
      (fun w _ => (hI w).ne'), Real.log_finprod hF] at hlog
  simpa using hlog

end Work.BW
