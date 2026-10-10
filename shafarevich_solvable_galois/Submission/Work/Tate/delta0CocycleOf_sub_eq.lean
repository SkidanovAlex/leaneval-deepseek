import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.Delta0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- If two elements `b`, `b'` of `B` have fixed image in `C` and differ by `S.f a₀`, then the
`1`-cocycles of `A` obtained by lifting them differ by the coboundary `γ • a₀ - a₀`. -/
theorem delta0CocycleOf_sub_eq {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) {b b' : B}
    (hb : ∀ γ : G, S.g (γ • b - b) = 0) (hb' : ∀ γ : G, S.g (γ • b' - b') = 0) {a₀ : A}
    (ha : b - b' = S.f a₀) (γ : G) :
    S.delta0CocycleOf b hb γ - S.delta0CocycleOf b' hb' γ = γ • a₀ - a₀ := by
  apply S.f_injective
  rw [map_sub, S.f_delta0CocycleOf b hb γ, S.f_delta0CocycleOf b' hb' γ, map_sub, S.f_equiv,
    ← ha, smul_sub]
  abel

end Work.Tate
