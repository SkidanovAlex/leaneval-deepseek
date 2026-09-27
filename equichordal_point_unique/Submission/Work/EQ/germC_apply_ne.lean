import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

/-- The local stable curve at a nonzero parameter, in explicit quotient form: for `h 0 = 0` and
`v ≠ 0`, `germC a h v = (a h(λv)/(h(λv) - h v) - a/2, a h v h(λv)/(h(λv) - h v))`, where
`λ = eqLam a`.  This is the substitution `v · dslope h 0 v = h v` and
`v · dslope (h ∘ (λ·) - h) 0 v = h(λv) - h v` in the definition of `germC` (which uses `dslope`
to fill the removable singularity at `v = 0`). -/
theorem germC_apply_ne {a : ℝ} {h : ℂ → ℂ} (h0 : h 0 = 0) {v : ℂ} (hv : v ≠ 0) :
    germC a h v =
      (a * h ((eqLam a : ℂ) * v) / (h ((eqLam a : ℂ) * v) - h v) - ((a / 2 : ℝ) : ℂ),
        a * h v * h ((eqLam a : ℂ) * v) / (h ((eqLam a : ℂ) * v) - h v)) := by
  -- At `v ≠ 0` the `dslope` at `0` is the ordinary difference quotient `(f v - f 0)/v`.
  have e1 : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 v
      = h ((eqLam a : ℂ) * v) / v := by
    rw [dslope_of_ne _ hv, slope_def_field]
    simp [h0]
  have e3 : dslope h 0 v = h v / v := by
    rw [dslope_of_ne _ hv, slope_def_field]
    simp [h0]
  have e2 : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 v
      = (h ((eqLam a : ℂ) * v) - h v) / v := by
    rw [dslope_of_ne _ hv, slope_def_field]
    simp [h0]
  have h1 : v * (h v / v) = h v := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ (h v) hv]
  simp only [germC, e1, e2, e3]
  refine Prod.ext ?_ ?_
  · rw [← mul_div_assoc, div_div_div_cancel_right₀ hv]
    push_cast
    ring
  · rw [mul_assoc (a : ℂ) v (h v / v), h1,
      ← mul_div_assoc (a * h v) (h ((eqLam a : ℂ) * v)) v,
      div_div_div_cancel_right₀ hv]

end Work.EQ
