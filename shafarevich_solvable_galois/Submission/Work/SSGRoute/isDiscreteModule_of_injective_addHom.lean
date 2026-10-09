import Mathlib
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If `N` carries a `G`-action whose stabilisers are open and `e : M →+ N` is an injective
`G`-equivariant additive map, then the same holds for `M`: for every `m : M` the stabiliser of
`m` equals the stabiliser of `e m` (as subsets of `G`), because `g • m = m ↔ g • e m = e m`
by equivariance and injectivity; the latter is open by hypothesis. -/
theorem isDiscreteModule_of_injective_addHom {G : Type} [Group G] [TopologicalSpace G] {M N : Type} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N] (e : M →+ N) (he : Function.Injective e) (heq : ∀ (g : G) (m : M), e (g • m) = g • e m) (hN : Work.AbsoluteKummer.IsDiscreteModule G N) : Work.AbsoluteKummer.IsDiscreteModule G M := by
  intro m
  have hset : (MulAction.stabilizer G m : Set G) = (MulAction.stabilizer G (e m) : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      rw [← heq g m, hg]
    · intro hg
      apply he
      rw [heq g m, hg]
  rw [hset]
  exact hN (e m)

end Work.SSGRoute
