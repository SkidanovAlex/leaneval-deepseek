import Mathlib.Algebra.Group.Finsupp
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Submission.Work.SSGRoute.prop5.core.gen_span
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The weight-`k` commutator monomials span `Λ_{k-1}`

The class in `Λ_{k-1} = γ_{k-1}/γ_k` of an element `y ∈ γ_{k-1}` of the free group lies in the
`ℤ`-span of the classes of the commutator monomials attached to the binary trees with `k` leaves,
i.e. in the range of `treeToLam X k`.

This is the statement proved in `Work.SSGRoute.prop5.core.gen_span` (which does the induction along
the lower central series, using `γ_{n+1} = ⁅γ_n, ⊤⁆` and the graded bilinearity of the commutator,
with `Λ_0` spanned by the free generators);  here we only restate it in the `adjacent` namespace,
where downstream files consume it.
-/

namespace Work.SSGRoute.prop5.adjacent

theorem lam_span_tree (X : Type) (k : ℕ) (hk : 1 ≤ k) (y : FreeGroup X)
    (hy : y ∈ Work.SSGRoute.prop5.core.Gam X (k - 1)) :
    Work.SSGRoute.prop5.core.cls X (k - 1) ⟨y, hy⟩ ∈
      LinearMap.range (Work.SSGRoute.prop5.core.treeToLam X k) :=
  Work.SSGRoute.prop5.core.gen_span X k hk y hy

end Work.SSGRoute.prop5.adjacent
