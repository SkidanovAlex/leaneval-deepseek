import Mathlib

namespace Work.CFTLib.PGroupConjTrivial

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **Commutators of a `p`-group with a normal subgroup of index `p` lie in a normal subgroup `H`.**

Let `G` be a `p`-group, `N ◁ G`, `H ◁ G` with `H ≤ N`, and suppose the quotient `N/H` has `p`
elements. Then for every `g : G` and `n : N`, the commutator `g⁻¹ n g n⁻¹` lies in `H`.

(Equivalently: the conjugation action of `G` on the group `N/H` of order `p` is trivial. The
action factors through `G/N`, which is a `p`-group, while `Aut(N/H) = Aut(ℤ/p) ≅ (ℤ/p)^×` has
order `p - 1`, coprime to `p`; a homomorphism from a `p`-group to a group of order `p - 1` is
trivial. `Nat.card (N ⧸ H.subgroupOf N) = p` says that `N/H` has order `p`; `N/H` is then a
cyclic group of order `p`, so `IsCyclic.card_mulAut` computes the order of its automorphism
group.) -/
theorem commutator_mem_of_isPGroup {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (N H : Subgroup G) [N.Normal] [H.Normal] (hHN : H ≤ N)
    (hcard : Nat.card (N ⧸ H.subgroupOf N) = p) :
    ∀ (g : G) (n : N), g⁻¹ * (↑n : G) * g * (↑n)⁻¹ ∈ H := by
  -- The conjugation action of `ConjAct G` on `N` descends to the quotient `N ⧸ H.subgroupOf N`,
  -- because conjugation preserves the normal subgroup `H`.
  haveI : MulAction.QuotientAction (ConjAct G) (H.subgroupOf N) := by
    refine ⟨fun b a a' h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at h ⊢
    have hmem := (inferInstance : H.Normal).conj_mem (↑(a⁻¹ * a') : G) h (ConjAct.ofConjAct b)
    convert hmem using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ConjAct.Subgroup.val_conj_smul,
      ConjAct.smul_eq_mulAut_conj, MulAut.conj_apply]
    group
  haveI : Finite (N ⧸ H.subgroupOf N) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).ne_zero)
  -- The action of the `p`-group `ConjAct G` on the `p`-element set `N ⧸ H.subgroupOf N` is
  -- trivial: the number of fixed points is congruent to `p` mod `p` and at least `1`, hence `p`.
  have key : ∀ (b : ConjAct G) (x : N ⧸ H.subgroupOf N), b • x = x := by
    intro b x
    have hmod : Nat.card (MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N)) ≡ 0 [MOD p] := by
      have h1 := (hG.of_equiv ConjAct.toConjAct).card_modEq_card_fixedPoints (N ⧸ H.subgroupOf N)
      rw [hcard] at h1
      exact h1.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p))
    have hdvd : p ∣ Nat.card (MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N)) :=
      Nat.modEq_zero_iff_dvd.mp hmod
    have hone : (1 : N ⧸ H.subgroupOf N) ∈
        MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N) := by
      rw [MulAction.mem_fixedPoints]
      intro c
      rw [← QuotientGroup.mk_one (H.subgroupOf N), MulAction.Quotient.smul_mk, smul_one,
        QuotientGroup.mk_one]
    have hpos : 0 < Nat.card (MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N)) :=
      Nat.card_pos_iff.mpr ⟨⟨1, hone⟩, inferInstance⟩
    have hle : Nat.card (MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N)) ≤ p := by
      have h2 := Nat.card_le_card_of_injective
        (Subtype.val : MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N) → N ⧸ H.subgroupOf N)
        Subtype.coe_injective
      rwa [hcard] at h2
    have hEq : Nat.card (MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N)) = p :=
      le_antisymm hle (Nat.le_of_dvd hpos hdvd)
    letI : Fintype (N ⧸ H.subgroupOf N) := Fintype.ofFinite _
    letI : Fintype (MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N)) := Fintype.ofFinite _
    have huniv : MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N) = Set.univ := by
      rw [← set_fintype_card_eq_univ_iff]
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEq, hcard]
    have hx : x ∈ MulAction.fixedPoints (ConjAct G) (N ⧸ H.subgroupOf N) := by
      rw [huniv]; trivial
    exact (MulAction.mem_fixedPoints.mp hx) b
  intro g n
  -- Apply triviality of the action to `ConjAct.toConjAct g⁻¹` and the class of `n⁻¹`.
  have hkey := key (ConjAct.toConjAct g⁻¹) (QuotientGroup.mk (⟨n⁻¹, N.inv_mem n.2⟩ : N))
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hkey
  convert hkey using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ConjAct.Subgroup.val_conj_smul,
    ConjAct.smul_eq_mulAut_conj, MulAut.conj_apply, ConjAct.ofConjAct_toConjAct]
  group

end Work.CFTLib.PGroupConjTrivial
