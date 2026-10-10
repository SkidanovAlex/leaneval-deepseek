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

/-- `δ₀` is additive on the level of cocycles: the cocycle attached to the sum `b₁ + b₂` of two
elements whose images in `C` are fixed is the sum of the cocycles attached to `b₁` and `b₂`.
Indeed both sides have the same image under the injective map `f`. -/
theorem delta0CocycleOf_add {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) {b₁ b₂ : B}
    (h₁ : ∀ γ : G, S.g (γ • b₁ - b₁) = 0) (h₂ : ∀ γ : G, S.g (γ • b₂ - b₂) = 0)
    (h : ∀ γ : G, S.g (γ • (b₁ + b₂) - (b₁ + b₂)) = 0) (γ : G) :
    S.delta0CocycleOf (b₁ + b₂) h γ = S.delta0CocycleOf b₁ h₁ γ + S.delta0CocycleOf b₂ h₂ γ := by
  apply S.f_injective
  rw [map_add, S.f_delta0CocycleOf, S.f_delta0CocycleOf, S.f_delta0CocycleOf, smul_add]
  abel

end Work.Tate
