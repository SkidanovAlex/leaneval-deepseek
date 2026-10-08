import Mathlib
import Submission.Work.Models.Port.BenderSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Abstract

/-- **The Borel subgroup of a Bender pair is a coatom** of the subgroup lattice of `G`.

`B ≠ ⊤` because `B` is strongly embedded.  For maximality: if `B < K` there is `x ∈ K \ B`; the
Bruhat decomposition `G = B ∪ BwB` writes `x = b₁ w b₂`, so conjugating by the elements of `B ≤ K`
puts `w` in `K`; now `G = B ∪ BwB ⊆ K` and hence `K = ⊤`. -/
theorem isCoatom_B {G : Type*} [Group G] [Finite G] (P : Submission.BenderPair G) :
    IsCoatom P.B := by
  refine ⟨P.B_ne_top, ?_⟩
  intro b hb
  -- `P.B < b` so there is `x ∈ b` with `x ∉ P.B`.
  obtain ⟨x, hxb, hxB⟩ : ∃ x ∈ b, x ∉ P.B := by
    by_contra h
    refine hb.2 fun y hy => ?_
    by_contra hyB
    exact h ⟨y, hy, hyB⟩
  -- The Bruhat decomposition forces the Weyl element `w` into `b`.
  have hw_mem : P.w ∈ b := by
    rcases P.bruhat x with h | ⟨b₁, b₂, hxw⟩
    · exact absurd h hxB
    · have h1 : (b₁ : G) ∈ b := hb.1 b₁.2
      have h2 : (b₂ : G) ∈ b := hb.1 b₂.2
      have hmem : (b₁ : G)⁻¹ * x * (b₂ : G)⁻¹ ∈ b :=
        b.mul_mem (b.mul_mem (b.inv_mem h1) hxb) (b.inv_mem h2)
      rw [hxw] at hmem
      convert hmem using 1
      group
  -- Hence `G = B ∪ BwB ⊆ b`.
  have htop : b = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rcases P.bruhat g with h | ⟨c₁, c₂, hgw⟩
    · exact hb.1 h
    · rw [hgw]
      exact b.mul_mem (b.mul_mem (hb.1 c₁.2) hw_mem) (hb.1 c₂.2)
  exact htop

end Work.Models.Abstract
