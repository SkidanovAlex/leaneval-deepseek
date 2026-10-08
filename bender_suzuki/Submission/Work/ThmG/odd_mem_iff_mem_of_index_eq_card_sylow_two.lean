import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmG

/-- Let `Q` be a finite group with a Sylow `2`-subgroup `P` and a normal subgroup `N` whose
index equals `|P|`.  Then `N` is the odd part of `Q`: it has odd order, and an element of `Q`
has odd order iff it lies in `N`.

The order computation is Lagrange's theorem: `|Q| = |N| · [Q : N] = |N| · |P|` and also
`|Q| = [Q : P] · |P|`, so `|N| = [Q : P]`, which is odd because `P` is Sylow.  For the second
part, `Q ⧸ N` has order `[Q : N] = |P|`, a power of `2`; hence the order of the image of any
`x` divides both `orderOf x` and a power of `2`, so it is `1` when `orderOf x` is odd, i.e.
`x ∈ N`.  Conversely an element of `N` has order dividing the odd number `|N|`. -/
theorem odd_mem_iff_mem_of_index_eq_card_sylow_two {Q : Type*} [Group Q] [Finite Q]
    (P : Sylow 2 Q) (N : Subgroup Q) (hN : N.Normal) (hidx : N.index = Nat.card P) :
    Odd (Nat.card N) ∧ ∀ x : Q, Odd (orderOf x) ↔ x ∈ N := by
  haveI := hN
  -- `|P|` is a power of `2` because `P` is a `2`-group.
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  -- Lagrange's theorem in the two forms we need.
  have hQ1' : Nat.card Q = Nat.card P * Nat.card N := by
    rw [← Subgroup.index_mul_card N, hidx]
  have hQ2' : Nat.card Q = Nat.card P * (P : Subgroup Q).index := by
    rw [← Subgroup.index_mul_card (P : Subgroup Q), mul_comm]
  -- Cancel `|P|` to identify `|N|` with the index of `P`.
  have hcard_N : Nat.card N = (P : Subgroup Q).index :=
    Nat.mul_left_cancel (Nat.card_pos (α := ↥(P : Subgroup Q))) (hQ1'.symm.trans hQ2')
  -- The index of a Sylow subgroup is coprime to `p`, so it is odd here.
  have hNodd : Odd (Nat.card N) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd, hcard_N]
    exact P.not_dvd_index
  refine ⟨hNodd, fun x => ⟨?_, ?_⟩⟩
  · -- If `x` has odd order then its image in `Q ⧸ N` has order dividing both an odd number
    -- and a power of `2`, hence is trivial.
    intro hodd
    have h1 : orderOf ((QuotientGroup.mk' N) x) ∣ orderOf x :=
      orderOf_map_dvd (QuotientGroup.mk' N) x
    have h2 : orderOf ((QuotientGroup.mk' N) x) ∣ 2 ^ k := by
      have h := orderOf_dvd_natCard ((QuotientGroup.mk' N) x)
      rw [← Subgroup.index_eq_card N, hidx, hk] at h
      exact h
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hodd).pow_right k
    have hg := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at hg
    have : (QuotientGroup.mk' N) x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  · -- An element of `N` has order dividing the odd number `|N|`.
    intro hx
    have hcoe : orderOf (⟨x, hx⟩ : N) = orderOf x := by
      rw [← Subgroup.orderOf_coe (⟨x, hx⟩ : N)]
    exact Odd.of_dvd_nat hNodd (hcoe ▸ orderOf_dvd_natCard (⟨x, hx⟩ : N))

end Work.ThmG
