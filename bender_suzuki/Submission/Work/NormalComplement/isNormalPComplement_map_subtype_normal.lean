import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Basic.isNormalPComplement_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NormalComplement

/-- Conjugation preserves the order of an element.  (Private: `sec5_prop2` has a lemma of the same
name and both are reachable from `Main`.) -/
private lemma orderOf_conj_eq {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  have h : g * x * g⁻¹ = (MulAut.conj g) x := (MulAut.conj_apply g x).symm
  rw [h]
  exact orderOf_injective (MulAut.conj g : G →* G) (MulAut.conj g).injective x

/-- An element of a normal `p`-complement `N ≤ ↥W` has order coprime to `p`.  Conversely, if
`w : ↥W` has order coprime to `p` then its image in the `p`-group `↥W ⧸ N` has order dividing
both `orderOf w` and a power of `p`, hence is `1`, so `w ∈ N`. -/
lemma mem_isNormalPComplement_iff {G : Type*} [Group G] [Finite G] {W : Subgroup G} {p : ℕ}
    [Fact p.Prime] {N : Subgroup ↥W} (hN : Work.NPC.IsNormalPComplement p N) {w : ↥W} :
    w ∈ N ↔ ¬ p ∣ orderOf w := by
  constructor
  · intro hw
    have h1 : orderOf w ∣ Nat.card N := by
      have h := orderOf_dvd_natCard (⟨w, hw⟩ : ↥N)
      rw [← orderOf_injective N.subtype N.subtype_injective ⟨w, hw⟩] at h
      exact h
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (hN.coprime_card.coprime_dvd_left h1).symm
  · intro hw
    haveI : N.Normal := hN.normal
    set d : ℕ := orderOf ((QuotientGroup.mk' N) w) with hd
    have h1 : d ∣ orderOf w := by
      rw [hd]; exact orderOf_map_dvd (QuotientGroup.mk' N) w
    obtain ⟨k, hk⟩ := hN.isPGroup_quotient.exists_orderOf_dvd_pow ((QuotientGroup.mk' N) w)
    have hk' : d ∣ p ^ k := by rw [hd]; exact hk
    have hcop : (orderOf w).Coprime (p ^ k) :=
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hw).symm.pow_right k
    have hd1 : d = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 hk'
    have hq : ((QuotientGroup.mk' N) w) = 1 := by
      rw [← orderOf_eq_one_iff, ← hd]; exact hd1
    exact (QuotientGroup.eq_one_iff w).mp hq

/-- **Characterisation of `N.map W.subtype`**: for a normal `p`-complement `N` of `↥W`, the
image of `N` in `G` consists exactly of the elements of `W` whose order is not divisible by
`p`. -/
lemma mem_map_subtype_isNormalPComplement_iff {G : Type*} [Group G] [Finite G] {W : Subgroup G}
    {p : ℕ} [Fact p.Prime] {N : Subgroup ↥W} (hN : Work.NPC.IsNormalPComplement p N) {x : G} :
    x ∈ N.map W.subtype ↔ x ∈ W ∧ ¬ p ∣ orderOf x := by
  constructor
  · intro hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx
    refine ⟨hwx ▸ w.2, ?_⟩
    have h1 : orderOf (W.subtype w) = orderOf w :=
      orderOf_injective W.subtype W.subtype_injective w
    rw [← hwx, h1]
    exact (mem_isNormalPComplement_iff hN).mp hw
  · rintro ⟨hxW, hx⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxW⟩, ?_, rfl⟩
    rw [mem_isNormalPComplement_iff hN]
    have h2 : orderOf ((⟨x, hxW⟩ : ↥W) : G) = orderOf (⟨x, hxW⟩ : ↥W) :=
      orderOf_injective W.subtype W.subtype_injective ⟨x, hxW⟩
    rw [← h2]
    exact hx

/-- **A normal `p`-complement of `W` is normalised by every subgroup normalising `W`** (it is
characteristic in `W`): `N ⊴ ↥W` with `|N|` coprime to `p` and `↥W ⧸ N` a `p`-group satisfies
`N.map W.subtype = {x ∈ W | ¬ p ∣ orderOf x}` (an element of `N` has `p'`-order; conversely the
image of `x` in the quotient has order dividing both `orderOf x` and a power of `p`), and
conjugation by any `h ∈ N_G(W)` preserves `W` and the order of an element, hence this set. -/
theorem isNormalPComplement_map_subtype_normal {G : Type*} [Group G] [Finite G] {W H : Subgroup G}
    {p : ℕ} [Fact p.Prime] {N : Subgroup ↥W} (hN : Work.NPC.IsNormalPComplement p N)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) :
    H ≤ Subgroup.normalizer ((N.map W.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hhW : h ∈ Subgroup.normalizer (W : Set G) := hHW hh
  rw [Subgroup.mem_normalizer_iff] at hhW
  rw [mem_map_subtype_isNormalPComplement_iff hN, mem_map_subtype_isNormalPComplement_iff hN,
    hhW x, orderOf_conj_eq]

end Work.NormalComplement
