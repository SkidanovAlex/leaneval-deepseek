import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

/-- Setup for Peterfalvi I Ch. II §4 Prop. 4 (b): a non-trivial subgroup `W` of odd order contains
a non-trivial maximal `p`-subgroup `X` for some odd prime `p`.  Take `y ∈ W`, `y ≠ 1`; a prime `p`
dividing `orderOf y` is odd (as `|W|` is odd); then a maximal `p`-subgroup of `W` containing a
subgroup of order `p` inside `⟨y⟩` (via `IsPGroup.exists_le_sylow` in the group `↥W`, translated
with `Subgroup.map W.subtype`) has the required properties. -/
theorem exists_odd_sylow_sub_of_ne_bot {G : Type} [Group G] [Finite G] {W : Subgroup G}
    (hW : W ≠ ⊥) (hodd : Odd (Nat.card W)) :
    ∃ (p : ℕ) (X : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsPGroup p X ∧ X ≠ ⊥ ∧ X ≤ W ∧
      (∀ Y : Subgroup G, X ≤ Y → Y ≤ W → IsPGroup p Y → Y = X) := by
  rcases Subgroup.bot_or_exists_ne_one W with hbot | ⟨y, hy, hy1⟩
  · exact absurd hbot hW
  -- work inside the group `↥W`
  let g : ↥W := ⟨y, hy⟩
  have hg1 : g ≠ 1 := by
    intro h
    exact hy1 (by simpa [g] using congrArg Subtype.val h)
  have hord : orderOf g ∣ Nat.card ↥W := by
    simpa [Nat.card_zpowers] using Subgroup.card_subgroup_dvd_card (Subgroup.zpowers g)
  have hordne : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  -- an odd prime `p` dividing `orderOf g`
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hordne
  have hpodd : Odd p := Odd.of_dvd_nat (Odd.of_dvd_nat hodd hord) hpdvd
  have hpne2 : p ≠ 2 := by
    intro h2
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hpos : 0 < orderOf g / p :=
    Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hpdvd) hpprime.pos
  have hmul : p * (orderOf g / p) = orderOf g := Nat.mul_div_cancel' hpdvd
  have hdvdk : (orderOf g / p) ∣ orderOf g := ⟨p, by rw [mul_comm, hmul]⟩
  have hgcd : Nat.gcd (orderOf g) (orderOf g / p) = orderOf g / p := Nat.gcd_eq_right hdvdk
  -- an element `z` of order `p` inside `W`
  let z : ↥W := g ^ (orderOf g / p)
  have hzord : orderOf z = p := by
    show orderOf (g ^ (orderOf g / p)) = p
    rw [orderOf_pow, hgcd]
    nth_rewrite 1 [show orderOf g = p * (orderOf g / p) from hmul.symm]
    exact Nat.mul_div_cancel p hpos
  have hH0pg : IsPGroup p ↥(Subgroup.zpowers z) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hzord, pow_one]
  -- a Sylow `p`-subgroup of `W` containing `⟨z⟩`
  obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow hH0pg
  have hz_ne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    exact hpprime.ne_one hzord.symm
  have hH0ne : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    exact hz_ne (Subgroup.zpowers_eq_bot.mp h)
  have hQne : (Q : Subgroup ↥W) ≠ ⊥ := by
    intro h
    exact hH0ne (le_bot_iff.mp (h ▸ hQle))
  refine ⟨p, (Q : Subgroup ↥W).map W.subtype, hpprime, hpne2, ?_, ?_, ?_, ?_⟩
  · exact IsPGroup.map Q.isPGroup' W.subtype
  · intro hX
    apply hQne
    apply Subgroup.map_injective W.subtype_injective
    rw [hX, Subgroup.map_bot]
  · exact Subgroup.map_subtype_le (Q : Subgroup ↥W)
  · intro Y hXY hYW hYpg
    have hY'pg : IsPGroup p ↥(Y.subgroupOf W) :=
      (Subgroup.comap_subtype Y W) ▸
        IsPGroup.comap_of_injective hYpg W.subtype W.subtype_injective
    have hQleY : (Q : Subgroup ↥W) ≤ Y.subgroupOf W := by
      rw [← Subgroup.comap_subtype Y W]
      exact Subgroup.map_le_iff_le_comap.mp hXY
    have hQeq : Y.subgroupOf W = (Q : Subgroup ↥W) := Sylow.is_maximal' Q hY'pg hQleY
    rw [← hQeq, Subgroup.subgroupOf_map_subtype Y W, inf_eq_left.mpr hYW]

end Work.ThreePoints
