import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- A divisor of an odd natural number is odd. -/
private theorem odd_of_dvd_odd {m n : ℕ} (h : m ∣ n) (hn : Odd n) : Odd m := by
  rw [← Nat.not_even_iff_odd] at hn ⊢
  intro hm
  exact hn (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hm).trans h))

/-- Lagrange's theorem in relative form: `|H ∩ N| * [H : H ∩ N] = |H|`. -/
private theorem natCard_inf_mul_relIndex {G : Type*} [Group G] (H N : Subgroup G) :
    Nat.card ↥(H ⊓ N) * (H ⊓ N).relIndex H = Nat.card ↥H := by
  have h := Subgroup.card_mul_index ((H ⊓ N).subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h

/-- If `N` is a normal subgroup of odd index and `H` has even order, then `H ∩ N` has even
order. Indeed `[H : H ∩ N]` divides `[G : N]` (it is the order of the image of `H` in `G/N`),
hence is odd, and `|H| = |H ∩ N| * [H : H ∩ N]`. -/
private theorem even_natCard_inf_of_odd_index {G : Type*} [Group G]
    {N H : Subgroup G} (hN : N.Normal) (hodd : Odd N.index) (hH : Even (Nat.card H)) :
    Even (Nat.card ↥(H ⊓ N)) := by
  have hrel : Odd ((H ⊓ N).relIndex H) := by
    have hdvd : N.relIndex H ∣ N.index :=
      @Subgroup.relIndex_dvd_index_of_normal G _ N H hN
    rw [Subgroup.inf_relIndex_left]
    exact odd_of_dvd_odd hdvd hodd
  have hcard := natCard_inf_mul_relIndex H N
  rw [← hcard] at hH
  rw [Nat.even_mul] at hH
  rcases hH with h | h
  · exact h
  · exact absurd h (Nat.not_even_iff_odd.mpr hrel)

/-- If `N ◁ G` has odd index and `H ≤ G` has even order, then `H ∩ N` contains an involution.
This is Cauchy's theorem applied to the even-order group `H ∩ N`. -/
theorem involution_mem_inf_of_odd_index {G : Type*} [Group G] [Finite G]
    {N H : Subgroup G} (hN : N.Normal) (hodd : Odd N.index) (hH : Even (Nat.card H)) :
    ∃ t : G, t ∈ H ⊓ N ∧ orderOf t = 2 := by
  have hK := even_natCard_inf_of_odd_index hN hodd hH
  have h2 : 2 ∣ Nat.card ↥(H ⊓ N) := even_iff_two_dvd.mp hK
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ N)) 2 h2
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

end Work.PSU3.StageA
