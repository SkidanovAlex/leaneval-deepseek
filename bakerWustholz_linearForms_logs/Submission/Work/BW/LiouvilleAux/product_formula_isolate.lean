import Mathlib
import Submission.Work.BW.prod_formula_log

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.LiouvilleAux

/-- **Isolated term of the logarithmic product formula.**
The product formula `∑_v mult(v) log|x|_v + ∑_{v finite} log|x|_v = 0` solved for
the contribution of a single infinite place `v₀`.  This is the form in which the
product formula is used to bound the archimedean contribution of `x` at `v₀` by
the contributions at all other places. -/
theorem product_formula_isolate {K : Type*} [Field K] [NumberField K]
    [DecidableEq (NumberField.InfinitePlace K)]
    (v₀ : NumberField.InfinitePlace K) {x : K} (hx : x ≠ 0) :
    (v₀.mult : ℝ) * Real.log (v₀ x) =
      -((∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.log (v x)) +
        ∑ᶠ v : NumberField.FinitePlace K, Real.log (v x)) := by
  -- The global product formula, in logarithmic form.
  have h := Work.BW.prod_formula_log hx
  -- Split off the `v₀` term from the sum over all infinite places.
  have hsplit : (∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.log (v x)) +
      (v₀.mult : ℝ) * Real.log (v₀ x)
      = ∑ v : NumberField.InfinitePlace K, (v.mult : ℝ) * Real.log (v x) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ v₀)
  linarith

end Work.BW.LiouvilleAux
