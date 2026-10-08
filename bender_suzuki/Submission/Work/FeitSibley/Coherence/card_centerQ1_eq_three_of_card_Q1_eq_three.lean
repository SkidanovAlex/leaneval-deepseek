import Mathlib
import Submission.Work.FeitSibley.GroupTheory.S_Q1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.card_centerQ1_eq_three_of_card_Q1_eq_three`

If `|Q₁| = 3` then `Q₁` has prime order, hence is cyclic and therefore abelian; so its centre
is all of `Q₁`, and the image of the centre under `Q₁ ↪ G` is `Q₁` itself.  Thus
`|Z(Q₁)| = |Q₁| = 3`.

This is the extreme case of `card_centerQ1_ge_card_D_add_one`: when `|Q₁| = 3` there is no room
for `D` to be large, and the centre is the whole group.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

/-- If `|Q₁| = 3` then `Q₁` is cyclic (it has prime order), hence commutative, so its centre is
everything and `Z(Q₁) = Q₁`. -/
theorem centerQ1_eq_Q1_of_card_Q1_eq_three {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (hq : Nat.card h.Q1 = 3) : h.centerQ1 = h.Q1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥h.Q1 := isCyclic_of_prime_card hq
  have hcenter : Subgroup.center ↥h.Q1 = ⊤ := Subgroup.center_eq_top
  show (Subgroup.center ↥h.Q1).map h.Q1.subtype = h.Q1
  rw [hcenter, Subgroup.map_top, Subgroup.range_subtype]

theorem card_centerQ1_eq_three_of_card_Q1_eq_three {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (hq : Nat.card h.Q1 = 3) :
    Nat.card h.centerQ1 = 3 := by
  rw [centerQ1_eq_Q1_of_card_Q1_eq_three h hq, hq]

end Work.FeitSibley.Coherence
