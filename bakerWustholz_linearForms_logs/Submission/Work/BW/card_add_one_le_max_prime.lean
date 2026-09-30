import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem card_add_one_le_max_prime (s : Finset ℕ) (hne : s.Nonempty) (hs : ∀ p ∈ s, p.Prime) :
    s.card + 1 ≤ s.max' hne := by
  have h2 : 2 ≤ s.max' hne := (hs _ (Finset.max'_mem s hne)).two_le
  have hsub : s ⊆ Finset.Icc 2 (s.max' hne) := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(hs p hp).two_le, Finset.le_max' s p hp⟩
  have hcard : s.card ≤ (s.max' hne) - 1 := by
    calc s.card ≤ (Finset.Icc 2 (s.max' hne)).card := Finset.card_le_card hsub
      _ = (s.max' hne) + 1 - 2 := Nat.card_Icc 2 _
      _ = (s.max' hne) - 1 := by omega
  omega

end Work.BW
