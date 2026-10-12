import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Span.Basic
import Submission.Work.BoseB7.l2FormDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.l2Form_symm` — symmetry of the ℓ² form

`l2Form ι f g = ∑_{m ∈ f.support} f m * g m` (see `Work.BoseB7.l2FormDef`).
Because the sum is taken over the support of the *first* argument only, symmetry
is not built into the definition: it is proved here by exhibiting both sides as
the same sum over the common superset `f.support ∪ g.support`.

The two auxiliary lemmas below are `private`: they are implementation details of
this file and are deliberately kept out of the shared namespace.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- Computation rule for `l2Form`: it is the sum of the pointwise products over
the support of the first argument. -/
private lemma l2Form_apply_aux (ι : Type*) (f g : ι →₀ ℝ) :
    l2Form ι f g = f.support.sum (fun m => f m * g m) := by
  simp only [l2Form, Finsupp.lsum_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.toSpanSingleton_apply, Finsupp.lapply_apply,
    smul_eq_mul]

/-- `l2Form ι f g` is also the sum of the pointwise products over the union of
the supports of `f` and `g` (the terms outside `f.support` vanish). -/
private lemma l2Form_eq_sum_union_aux (ι : Type*) [DecidableEq ι] (f g : ι →₀ ℝ) :
    l2Form ι f g = (f.support ∪ g.support).sum (fun m => f m * g m) := by
  rw [l2Form_apply_aux]
  exact Finset.sum_subset Finset.subset_union_left
    (fun x _ hx => by rw [Finsupp.notMem_support_iff.mp hx, zero_mul])

theorem l2Form_symm (ι : Type*) (f g : ι →₀ ℝ) :
    Work.BoseB7.l2Form ι f g = Work.BoseB7.l2Form ι g f := by
  classical
  rw [l2Form_eq_sum_union_aux ι f g, l2Form_eq_sum_union_aux ι g f,
    Finset.union_comm g.support f.support]
  exact Finset.sum_congr rfl (fun m _ => mul_comm (f m) (g m))

end Work.BoseB7
