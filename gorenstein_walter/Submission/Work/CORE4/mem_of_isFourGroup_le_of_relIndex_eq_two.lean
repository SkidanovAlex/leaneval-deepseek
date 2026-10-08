import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.cyclic_order_two_unique

namespace Work.CORE4

/-- **A Klein four subgroup of `S` contains the involution of a cyclic index-two subgroup `S₀`.**

Let `S₀ ≤ S` be a cyclic subgroup of relative index two in `S`, and let `W ≤ S` be a Klein four
group (`Work.GW2.IsFourGroup W`, i.e. `|W| = 4` and every element of `W` is an involution).  Then
`W` contains the unique involution `t` of `S₀`.

Indeed `relIndex S₀ W ≤ relIndex S₀ S = 2`, so by `S₀.relIndex W * |S₀ ⊓ W| = |W| = 4` the
intersection `S₀ ⊓ W` is non-trivial.  Pick `1 ≠ b ∈ S₀ ⊓ W`; then `b = b⁻¹`, and since `S₀` is
cyclic it has a unique involution (`cyclic_order_two_unique`), so `b = t`. -/
theorem mem_of_isFourGroup_le_of_relIndex_eq_two {G : Type} [Group G] [Finite G]
    {S S0 W : Subgroup G} (hS0 : S0 ≤ S) (hidx : S0.relIndex S = 2) (hcyc : IsCyclic S0)
    {t : G} (htS0 : t ∈ S0) (ht2 : orderOf t = 2) (hW : W ≤ S)
    (h4 : Work.GW2.IsFourGroup W) : t ∈ W := by
  -- ## 1. The intersection `S₀ ⊓ W` is non-trivial.
  have hne : S0 ⊓ W ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (S0 ⊓ W : Subgroup G) = 1 := by
      rw [hbot]; exact Subgroup.card_bot
    have hle : S0.relIndex W ≤ S0.relIndex S :=
      Subgroup.relIndex_le_of_le_right hW (by rw [hidx]; norm_num)
    have hmul := Subgroup.relIndex_mul_card (H := S0) (K := W)
    rw [hcard, mul_one, h4.1] at hmul
    omega
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ (S0 ⊓ W : Subgroup G), b ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (le_antisymm (fun x hx => by rw [Subgroup.mem_bot]; exact h x hx) bot_le)
  -- ## 2. `b` and `t` are two involutions of the cyclic group `S₀`, hence equal.
  have hbS0 : b ∈ S0 := (Subgroup.mem_inf.mp hb).1
  have hbW : b ∈ W := (Subgroup.mem_inf.mp hb).2
  have hb2 : b ^ 2 = 1 := h4.2 b hbW
  have ht2' : t ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have htb : t = b := cyclic_order_two_unique hcyc htS0 hbS0 ht2' hb2 ht1 hb1
  rw [htb]
  exact hbW

end Work.CORE4
