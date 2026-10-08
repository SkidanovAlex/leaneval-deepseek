import Mathlib
import Submission.Work.Fitting.mem_sectionCentralizer_iff_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- `X` is contained in the centralizer of the section `K/H` if and only if every
`x ∈ X` has all its commutators with elements of `K` lying in `H`. -/
theorem le_sectionCentralizer_iff {G : Type*} [Group G] {H K X : Subgroup G} [H.Normal] :
    X ≤ Work.Fitting.sectionCentralizer H K ↔
      ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ H := by
  rw [SetLike.le_def]
  constructor
  · intro h x hx k hk
    exact (Work.Fitting.mem_sectionCentralizer_iff_commutator.mp (h hx)) k hk
  · intro h x hx
    exact Work.Fitting.mem_sectionCentralizer_iff_commutator.mpr (h x hx)

end Work.Fitting
