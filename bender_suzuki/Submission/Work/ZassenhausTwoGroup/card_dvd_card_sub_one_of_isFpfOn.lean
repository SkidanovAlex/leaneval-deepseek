import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.card_dvd_card_sub_one_of_isFpfOn`

If `D ≤ N_G(A)` acts fixed point freely by conjugation on the subgroup `A` (that is, every
`1 ≠ d ∈ D` fixes only `1` of `A`), then `|D|` divides `|A| - 1`.

This is the abstract Burnside count underlying
`Work.ZassenhausTwoGroup.card_twoPoint_dvd_card_Q_sub_one`: with the conjugation action of `D`
on `A`, the involution `1` contributes the whole of `A` to `∑_d |Fix d|`, while every other
`d` contributes the single point `1`.  Burnside's lemma
(`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) identifies that sum with
`#orbits · |D|`, so `|A| + |D| - 1 = #orbits · |D|` and hence `|D| ∣ |A| - 1`.
-/
set_option autoImplicit false

namespace Work.ZassenhausTwoGroup

theorem card_dvd_card_sub_one_of_isFpfOn {G : Type} [Group G] [Finite G] {D A : Subgroup G}
    (hN : D ≤ Subgroup.normalizer (A : Set G))
    (hf : Work.ZassenhausTwoGroup.IsFpfOn D A) :
    Nat.card D ∣ Nat.card A - 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- the conjugation action of `D` on `A` is well defined because `D ≤ N_G(A)`
  have hsmul : ∀ (d : D) (x : A), (d : G) * (x : G) * (d : G)⁻¹ ∈ A := fun d x =>
    (Subgroup.mem_normalizer_iff.mp (hN d.2) (x : G)).mp x.2
  letI : MulAction D A :=
    { smul := fun d x => ⟨(d : G) * (x : G) * (d : G)⁻¹, hsmul d x⟩
      one_smul := fun x => by
        apply Subtype.ext
        show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
        simp
      mul_smul := fun d e x => by
        apply Subtype.ext
        show ((d : G) * (e : G)) * (x : G) * ((d : G) * (e : G))⁻¹
          = (d : G) * ((e : G) * (x : G) * (e : G)⁻¹) * (d : G)⁻¹
        group }
  -- `1` fixes every point of `A`
  have hfix1 : Fintype.card (MulAction.fixedBy A (1 : D)) = Nat.card A := by
    have he : (MulAction.fixedBy A (1 : D)) ≃ A :=
      (Equiv.subtypeEquivRight (fun x => by rw [MulAction.mem_fixedBy]; simp)).trans
        (Equiv.Set.univ A)
    calc Fintype.card (MulAction.fixedBy A (1 : D)) = Fintype.card A := Fintype.card_congr he
      _ = Nat.card A := Nat.card_eq_fintype_card.symm
  -- every nontrivial `d` fixes only `1`
  have hfixne : ∀ d : D, d ≠ 1 → Fintype.card (MulAction.fixedBy A d) = 1 := by
    intro d hd
    have he : (MulAction.fixedBy A d) ≃ {x : A // (d : G) * (x : G) * (d : G)⁻¹ = (x : G)} :=
      Equiv.subtypeEquivRight (fun x => by
        rw [MulAction.mem_fixedBy]
        exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩)
    rw [Fintype.card_congr he, Fintype.card_eq_one_iff]
    refine ⟨⟨1, by simp⟩, fun y => ?_⟩
    refine Subtype.ext (Subtype.ext ?_)
    exact hf (d : G) d.2 (fun h1 => hd (Subtype.ext h1)) (y : G) y.1.2 y.2
  -- the sum of the numbers of fixed points
  have hsum : (∑ d : D, Fintype.card (MulAction.fixedBy A d))
      = Nat.card A + (Nat.card D - 1) := by
    have h2 : (∑ d ∈ Finset.univ.erase (1 : D),
        Fintype.card (MulAction.fixedBy A d)) = Nat.card D - 1 := by
      trans (∑ d ∈ Finset.univ.erase (1 : D), (1 : ℕ))
      · exact Finset.sum_congr rfl (fun d hd => hfixne d (Finset.mem_erase.mp hd).1)
      · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
          ← Nat.card_eq_fintype_card]
        simp
    rw [← Finset.add_sum_erase Finset.univ
      (fun d : D => Fintype.card (MulAction.fixedBy A d)) (Finset.mem_univ 1),
      hfix1, h2]
  -- Burnside's lemma
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group D A
  have hmain : Nat.card A + (Nat.card D - 1)
      = Fintype.card (Quotient (MulAction.orbitRel D A)) * Nat.card D := by
    rw [← hsum, hB, Nat.card_eq_fintype_card]
  have hDpos : 1 ≤ Nat.card D := by
    haveI : Nonempty D := ⟨⟨1, D.one_mem⟩⟩
    exact Nat.card_pos
  have hApos : 1 ≤ Nat.card A := by
    haveI : Nonempty A := ⟨⟨1, A.one_mem⟩⟩
    exact Nat.card_pos
  have h1 : Nat.card A - 1
      = Fintype.card (Quotient (MulAction.orbitRel D A)) * Nat.card D - Nat.card D := by
    omega
  have h2 : Fintype.card (Quotient (MulAction.orbitRel D A)) * Nat.card D - Nat.card D
      = (Fintype.card (Quotient (MulAction.orbitRel D A)) - 1) * Nat.card D := by
    rw [Nat.sub_mul, one_mul]
  rw [h1, h2]
  exact dvd_mul_left _ _

end Work.ZassenhausTwoGroup
