import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

/-- An element of `2`-power order is contained in a Sylow `2`-subgroup: its cyclic subgroup
`⟨x⟩` has order `orderOf x = 2 ^ k`, hence is a `2`-group, and Sylow's first theorem places it in
some Sylow `2`-subgroup. -/
theorem exists_sylow_of_powTwoOrder {G : Type} [Group G] [Finite G] {x : G}
    (hx : Work.ZassenhausSuzuki.Odd.PowTwoOrder x) : ∃ P : Sylow 2 G, x ∈ P := by
  obtain ⟨k, hk⟩ := hx
  have hcard : Nat.card ↥(Subgroup.zpowers x) = 2 ^ k := by
    rw [Nat.card_zpowers, hk]
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers x)⟩

end Work.ZassenhausSuzuki.Odd
