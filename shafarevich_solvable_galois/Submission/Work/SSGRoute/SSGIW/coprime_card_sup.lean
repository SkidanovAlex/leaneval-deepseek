import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring.RingNF
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option linter.style.haveILetI false

/-!
# Joins of subgroups of order coprime to `p`

A product of two normal subgroups of a finite group of order coprime to `p` again has order coprime
to `p`; this is what makes the family of normal subgroups of order coprime to `p` *directed*, so
that its join is the maximal such subgroup.
-/

open scoped Pointwise

namespace Work.SSGRoute

/-- **The join of two subgroups of order coprime to `p`, one of them normal, has order coprime to
`p`.**  With `Q₂ ◁ G` one has `Q₁ ⊔ Q₂ = Q₁ · Q₂`, and `Q₁ ⧸ (Q₁ ⊓ Q₂) ≃* (Q₁ ⊔ Q₂) ⧸ Q₂`, so
`|Q₁ ⊔ Q₂|` divides `|Q₁| * |Q₂|`. -/
theorem coprime_card_sup {G : Type*} [Group G] (p : ℕ) (Q₁ Q₂ : Subgroup G) [Q₂.Normal]
    (h₁ : Nat.Coprime p (Nat.card ↥Q₁)) (h₂ : Nat.Coprime p (Nat.card ↥Q₂)) :
    Nat.Coprime p (Nat.card ↥(Q₁ ⊔ Q₂)) := by
  classical
  set Q₂' : Subgroup ↥(Q₁ ⊔ Q₂) := Q₂.subgroupOf (Q₁ ⊔ Q₂) with hQ₂'
  haveI : Q₂'.Normal := Subgroup.Normal.subgroupOf inferInstance _
  have hcard2 : Nat.card ↥Q₂' = Nat.card ↥Q₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Q₂ ≤ Q₁ ⊔ Q₂)).toEquiv
  let φ : ↥Q₁ →* (↥(Q₁ ⊔ Q₂)) ⧸ Q₂' :=
    (QuotientGroup.mk' Q₂').comp (Subgroup.inclusion (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q₂' y
    have hx : (x : G) ∈ (↑Q₁ : Set G) * (↑Q₂ : Set G) := by
      rw [← Subgroup.mul_normal Q₁ Q₂]
      exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    refine ⟨⟨a, ha⟩, ?_⟩
    refine (QuotientGroup.mk'_eq_mk' Q₂').mpr
      ⟨⟨b, le_sup_right (a := Q₁) (b := Q₂) hb⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hb
    · apply Subtype.ext
      exact hab
  have hidx : Q₂'.index = φ.ker.index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv.symm
  have hdiv : Nat.card ↥(Q₁ ⊔ Q₂) ∣ Nat.card ↥Q₁ * Nat.card ↥Q₂ := by
    calc Nat.card ↥(Q₁ ⊔ Q₂)
        = Nat.card ↥Q₂' * Q₂'.index := (Subgroup.card_mul_index Q₂').symm
      _ = Nat.card ↥Q₂ * φ.ker.index := by rw [hcard2, hidx]
      _ ∣ Nat.card ↥Q₂ * Nat.card ↥Q₁ := Nat.mul_dvd_mul_left _ (Subgroup.index_dvd_card φ.ker)
      _ = Nat.card ↥Q₁ * Nat.card ↥Q₂ := by ring
  exact Nat.Coprime.coprime_dvd_right hdiv (h₁.mul_right h₂)

end Work.SSGRoute
