import Mathlib
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.exists_smul_t_eq` — the orbit of `t • ∞` under `H`

In the split rank-one situation the group `G` is doubly transitive on the cosets
`Ω = G ⧸ H` (`IsSplitRankOne.twoTransitive`), so the stabiliser `H` of the point
`∞ = pt H` is transitive on `Ω ∖ {∞}`; equivalently `G = H ⊔ H t H` (the rank-one
Bruhat decomposition).  Concretely: for every `ω ≠ ∞` there is `a ∈ H` with
`a • (t • ∞) = ω`, which is what makes the points `qPt H t x = x • (t • ∞)` (`x ∈ Q`)
exhaust `Ω ∖ {∞}`.

The proof is a direct application of `2`-transitivity to the two ordered pairs
`(∞, t • ∞)` and `(∞, ω)` of distinct points; the group element produced stabilises
`∞`, hence lies in `H`.
-/

set_option autoImplicit false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem exists_smul_t_eq {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {ω : G ⧸ H}
    (hω : ω ≠ Work.RankOneUniqueness.pt H) :
    ∃ a ∈ H, a • (t • Work.RankOneUniqueness.pt H) = ω := by
  -- `G` acts 2-transitively on `Ω = G ⧸ H`; read that as the "move two distinct points
  -- to two distinct points" form.
  have h2 : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := h.twoTransitive
  rw [MulAction.is_two_pretransitive_iff] at h2
  -- Apply it to `(∞, t • ∞) ↦ (∞, ω)`; both pairs consist of distinct points.
  obtain ⟨g, hg1, hg2⟩ := h2 (t_smul_pt_ne h).symm hω.symm
  -- `g` fixes `∞`, so `g ∈ H`; and it sends `t • ∞` to `ω` by construction.
  exact ⟨g, mem_of_smul_pt H hg1, hg2⟩

end Work.RankOneUniqueness
