import Mathlib
import Submission.Work.ThmG.rankOne_isTI
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.RankOneUniqueness.exists_smul_t_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.doubleCoset_cover`

The rank-one Bruhat decomposition: in the split rank-one situation `IsSplitRankOne H Q t`,
every element of `G` lies in `H` or in the double coset `H t H`, i.e.

`G = H ∪ H t H`.

This is purely a restatement of the transitivity of `H` on the non-base points of
`Ω = G ⧸ H`, which follows from the `2`-transitivity of `G` on `Ω`: for `g ∉ H` the two
ordered pairs `(∞, t • ∞)` and `(∞, g • ∞)` of distinct points can be moved onto each other by
some `a ∈ G`; that `a` fixes `∞`, hence `a ∈ H`, and sends `t • ∞` to `g • ∞`, i.e.
`a t H = g H`, so `g = a t b` for some `b ∈ H`.
-/

set_option autoImplicit false

namespace Work.ZassenhausTwoGroup

theorem doubleCoset_cover {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a : G) * t * (b : G) := by
  intro g
  by_cases hg : g ∈ H
  · exact Or.inl hg
  · refine Or.inr ?_
    -- `g` moves the base point `∞ = pt H`, since `g ∉ H`.
    have hω : g • Work.RankOneUniqueness.pt H ≠ Work.RankOneUniqueness.pt H :=
      fun hc => hg ((Work.RankOneUniqueness.smul_pt_iff H g).mp hc)
    -- `H` is transitive on the non-base points: some `a ∈ H` sends `t • ∞` to `g • ∞`.
    obtain ⟨a, haH, ha⟩ :=
      Work.RankOneUniqueness.exists_smul_t_eq (H := H) (Q := Q) (t := t) h
        (ω := g • Work.RankOneUniqueness.pt H) hω
    -- Consequently `a t H = g H`.
    have h1 : (a * t) • Work.RankOneUniqueness.pt H = g • Work.RankOneUniqueness.pt H := by
      rw [mul_smul]; exact ha
    have hcoset : ((a * t : G) : G ⧸ H) = (g : G ⧸ H) := by
      rw [← Work.RankOneUniqueness.smul_pt H (a * t),
          ← Work.RankOneUniqueness.smul_pt H g]
      exact h1
    -- Hence `(a t)⁻¹ g ∈ H`, giving the Bruhat decomposition `g = a · t · ((a t)⁻¹ g)`.
    have hmem : (a * t)⁻¹ * g ∈ H := QuotientGroup.eq.mp hcoset
    exact ⟨⟨a, haH⟩, ⟨(a * t)⁻¹ * g, hmem⟩, by group⟩

end Work.ZassenhausTwoGroup
