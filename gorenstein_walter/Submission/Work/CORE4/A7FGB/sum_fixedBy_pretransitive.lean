import Mathlib

set_option linter.style.haveILetI false

namespace Work.CORE4.A7FGB

theorem sum_fixedBy_pretransitive (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] [Fintype X] [Nonempty X] [MulAction.IsPretransitive G X]
    [∀ g : G, Fintype (MulAction.fixedBy X g)] :
    (∑ g : G, Fintype.card (MulAction.fixedBy X g)) = Fintype.card G := by
  classical
  haveI : Fintype (Quotient (MulAction.orbitRel G X)) := Fintype.ofFinite _
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X]
  have hcard : Fintype.card (Quotient (MulAction.orbitRel G X)) = 1 := by
    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    refine Fintype.card_eq_one_iff.mpr ⟨Quotient.mk'' x₀, ?_⟩
    intro y
    induction y using Quotient.inductionOn' with
    | h x =>
      rw [Quotient.eq'']
      exact MulAction.orbitRel_apply.mpr
        (MulAction.mem_orbit_iff.mpr (MulAction.exists_smul_eq G x₀ x))
  rw [hcard, one_mul]

end Work.CORE4.A7FGB
