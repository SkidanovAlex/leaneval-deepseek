import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
set_option linter.style.haveILetI false

namespace Work.LocalPrelim

theorem smul_eq_self_of_card_eq_prime {Q α : Type*} [Group Q] [MulAction Q α] [Finite α]
    {p : ℕ} (hp : p.Prime) (hQ : IsPGroup p Q) (hcard : Nat.card α = p) {a : α}
    (ha : a ∈ MulAction.fixedPoints Q α) : ∀ (q : Q) (x : α), q • x = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype (MulAction.fixedPoints Q α) := Fintype.ofFinite _
  have hmod := hQ.card_modEq_card_fixedPoints α
  have h1 : Nat.card α ≡ 0 [MOD p] := by
    rw [hcard]
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)
  have hpf : p ∣ Nat.card (MulAction.fixedPoints Q α) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h1)
  have hpos : 0 < Nat.card (MulAction.fixedPoints Q α) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨a, ha⟩⟩, inferInstance⟩
  have hle : Nat.card (MulAction.fixedPoints Q α) ≤ Nat.card α :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hcardFix : Nat.card (MulAction.fixedPoints Q α) = p :=
    le_antisymm (hle.trans hcard.le) (Nat.le_of_dvd hpos hpf)
  have hcardFix' : Fintype.card (MulAction.fixedPoints Q α) = Fintype.card α := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardFix.trans hcard.symm
  have huniv : MulAction.fixedPoints Q α = Set.univ :=
    (set_fintype_card_eq_univ_iff _).mp hcardFix'
  intro q x
  have hx : x ∈ MulAction.fixedPoints Q α := by
    rw [huniv]
    exact Set.mem_univ x
  exact (MulAction.mem_fixedPoints.mp hx) q

end Work.LocalPrelim
