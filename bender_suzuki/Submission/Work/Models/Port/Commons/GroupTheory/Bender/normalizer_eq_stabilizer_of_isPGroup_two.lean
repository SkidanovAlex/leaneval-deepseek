import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.fixedPoint_isFixedBy_normalizer_isPGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Bender

/-- In the "Bender action" situation (finite group `G` of even order acting pretransitively on a
finite set `Ω` such that every involution of `G` has a unique fixed point), let `U` be a nontrivial
`2`-subgroup contained in the stabilizer `H = Stab_G(α)` of a point `α`, with `H ≤ N_G(U)`.
Then `N_G(U) = H`.

Indeed `U` is a nontrivial `2`-subgroup, so it has a unique fixed point `z`; since `U ≤ H` we have
`z = α`.  Any `n ∈ N_G(U)` then fixes `z = α` by
`fixedPoint_isFixedBy_normalizer_isPGroup_two`, so `n ∈ H`. -/
theorem normalizer_eq_stabilizer_of_isPGroup_two {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] (htrans : MulAction.IsPretransitive G Ω) (hne : 1 < Nat.card Ω)
    (heven : Even (Nat.card G)) (hinv : ∀ t : G, orderOf t = 2 → ∃! x : Ω, t • x = x) (α : Ω)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hUne : U ≠ ⊥)
    (hUB : U ≤ MulAction.stabilizer G α)
    (hBn : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G)) :
    Subgroup.normalizer (U : Set G) = MulAction.stabilizer G α := by
  refine le_antisymm ?_ hBn
  intro g hg
  -- The point `α` is fixed by every element of `U`, since `U ≤ Stab_G(α)`.
  have hfix : ∀ u : U, (u : G) • α = α := by
    intro u
    have hu : (u : G) ∈ MulAction.stabilizer G α := hUB u.2
    rwa [MulAction.mem_stabilizer_iff] at hu
  -- Since `U` is a nontrivial `2`-subgroup it has a unique fixed point, namely `α`; hence any
  -- normalizer element fixes `α`.
  rw [MulAction.mem_stabilizer_iff]
  exact fixedPoint_isFixedBy_normalizer_isPGroup_two heven hinv hU hUne hfix hg

end Commons.GroupTheory.Bender
