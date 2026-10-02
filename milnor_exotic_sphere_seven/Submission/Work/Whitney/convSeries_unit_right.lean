import Mathlib
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Whitney.ChernRelSeries

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The right unit law of the convolution of graded series

`Work.LerayHirsch.convSeries x y k = Σ_{i ≤ k} x_i ⌣ y_{k-i}` is the `k`-th coefficient of the
convolution of the two series `x`, `y : (i : ℕ) → H^{2i}(B;ℤ)`.  This module proves that the
**unit series** `(1, 0, 0, …)` is a right unit for it:

  `convSeries x y k = x k`   whenever `y 0 = 1` and `y j = 0` for `j ≥ 1`.

This is the bookkeeping that makes the `(i,j) = (k,0)` summand of the right-hand side of the
Whitney sum formula reduce to `c_k` of the first factor; together with
`Work.Whitney.ChernRel.convSeries_congr_right` it also identifies any series vanishing above `0`
with the unit.

The one non-trivial point is the summand `i = k`, where the second factor of the convolution is
`y (k - k)`: the expression `k - k` does **not** reduce definitionally to `0` for a variable `k`,
so (as everywhere in this development) the identification with `y 0` has to go through the degree
transport `Work.Thom.cohTransport`.  The bridge lemma is
`Work.Whitney.cohTransport_congrArg_series` below.
-/

namespace Work.Whitney

noncomputable section

open Work

variable {B : Type} [TopologicalSpace B]

/-- **The degree transport of the value of a graded series along an equality of indices**: for
`y : (i : ℕ) → H^{2i}(B;ℤ)` and `h : a = b`, transporting `y a` along the induced equality
`2*a = 2*b` of the degrees gives `y b`.  (This is the transport form of the tautology
`h ▸ y a = y b`; it is what converts `y (k - k)` into `y 0`.) -/
theorem cohTransport_congrArg_series {a b : ℕ} (h : a = b)
    (y : (i : ℕ) → Work.Thom.Coh ℤ (2 * i) B) :
    Work.Thom.cohTransport (congrArg (fun t : ℕ => 2 * t) h) (y a) = y b := by
  cases h
  exact Work.Thom.cohTransport_rfl _

/-- **The unit series `(1, 0, 0, …)` is a right unit of the convolution of graded series**:
`convSeries x y k = x k` if `y 0 = 1` and `y j = 0` for `j ≥ 1`. -/
theorem convSeries_unit_right {B : Type} [TopologicalSpace B]
    (x y : (i : ℕ) → Work.Thom.Coh ℤ (2 * i) B)
    (hy0 : y 0 = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))
    (hypos : ∀ j, 1 ≤ j → y j = 0) (k : ℕ) :
    Work.LerayHirsch.convSeries x y k = x k := by
  rw [Work.LerayHirsch.convSeries]
  rw [Finset.sum_range_succ]
  -- the summands with `i < k`: the second factor is `y (k - i)` with `k - i ≥ 1`, hence `0`
  have hzero : (∑ i ∈ Finset.range k, Work.LerayHirsch.convTerm x y k i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
    have h1 : 1 ≤ k - i := by have := Finset.mem_range.mp hi; omega
    rw [Work.LerayHirsch.convTerm_pos hik, hypos (k - i) h1, Work.Cohomology.cupH'_zero_right]
    exact Work.Whitney.ChernRel.cohTransport_zero _
  rw [hzero, zero_add]
  -- the summand `i = k`: the second factor is `y (k - k)`, which is `y 0 = 1`
  rw [Work.LerayHirsch.convTerm_pos (le_refl k)]
  have hkk : k - k = 0 := Nat.sub_self k
  have hser : y (k - k)
      = Work.Thom.cohTransport (congrArg (fun t : ℕ => 2 * t) hkk.symm) (y 0) :=
    (cohTransport_congrArg_series hkk.symm y).symm
  rw [hser, Work.LerayHirsch.cupH'_cast_right, hy0, Work.Cohomology.cupH'_one_right]
  rw [Work.Whitney.cohTransport_trans]
  exact Work.Whitney.ChernRel.cohTransport_self _ _

end

end Work.Whitney
