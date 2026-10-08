import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Basic

/-- If the order of `G` is coprime to `p`, then `G` itself is a normal `p`-complement of `G`:
`⊤` is normal, its order `|G|` is coprime to `p`, and the quotient `G ⧸ ⊤` is trivial, hence a
`p`-group. -/
theorem hasNormalPComplement_of_coprime {G : Type*} [Group G] [Finite G] {p : ℕ}
    (h : (Nat.card G).Coprime p) : Work.NPC.HasNormalPComplement p G := by
  refine ⟨⊤, Subgroup.normal_top, ?_, ?_⟩
  · simpa using h
  · exact @IsPGroup.of_subsingleton p (G ⧸ (⊤ : Subgroup G)) _
      QuotientGroup.subsingleton_quotient_top

end Work.NPC.Basic
