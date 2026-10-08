import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open MulAction

namespace Commons.GroupTheory.GroupAction

/-- If the action of `G` on `α` is `n`-pretransitive, and the action of `H`
is compatible with that of `G` through a group homomorphism `σ : G →* H`
(in the sense that `σ g • x = g • x` for all `g`, `x`), then the action
of `H` on `α` is `n`-pretransitive as well. -/
theorem isMultiplyPretransitive_of_surjective_hom {G H α : Type*} [Group G] [Group H]
    [MulAction G α] [MulAction H α] (σ : G →* H)
    (hsmul : ∀ (g : G) (x : α), σ g • x = g • x) {n : ℕ}
    [hG : IsMultiplyPretransitive G α n] : IsMultiplyPretransitive H α n := by
  let f : α →ₑ[σ] α := ⟨id, by intro g x; exact (hsmul g x).symm⟩
  change IsPretransitive H (Fin n ↪ α)
  exact IsPretransitive.of_embedding (f := f) (n := Fin n) Function.surjective_id

end Commons.GroupTheory.GroupAction