import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.BoseB7.l2FormDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.l2Form_posDef` — positivity and definiteness of the ℓ² form

`l2Form ι f g = ∑_m f m * g m` is the ℓ² inner product on finitely supported real
sequences (`Work.BoseB7.l2FormDef`).  Here we prove that the associated quadratic
form is positive definite:

* `0 ≤ l2Form ι f f`, because it is a sum of squares;
* `l2Form ι f f = 0 → f = 0`, because a sum of nonnegative terms vanishing forces
  every term `f m * f m` on the support to vanish, and outside the support `f`
  vanishes by definition.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- The ℓ² form evaluated on a pair: `l2Form ι f g = ∑_{m ∈ f.support} f m * g m`. -/
private theorem l2Form_apply_sum (ι : Type*) (f g : ι →₀ ℝ) :
    Work.BoseB7.l2Form ι f g = ∑ m ∈ f.support, f m * g m := by
  simp only [l2Form, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul]

theorem l2Form_posDef (ι : Type*) (f : ι →₀ ℝ) :
    0 ≤ Work.BoseB7.l2Form ι f f ∧ (Work.BoseB7.l2Form ι f f = 0 → f = 0) := by
  have hform := l2Form_apply_sum ι f f
  constructor
  · rw [hform]
    exact Finset.sum_nonneg (fun m _ => mul_self_nonneg (f m))
  · intro h
    rw [hform] at h
    have hnn : ∀ m ∈ f.support, 0 ≤ f m * f m := fun m _ => mul_self_nonneg _
    have hz : ∀ m ∈ f.support, f m * f m = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
    refine Finsupp.ext (fun m => ?_)
    by_cases hm : m ∈ f.support
    · exact (mul_self_eq_zero).mp (hz m hm)
    · by_contra hc
      exact hm ((Finsupp.mem_support_iff).mpr hc)

end Work.BoseB7
