import Mathlib
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.FeitSibley.GroupTheory.FPF_orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley`: `|D| ∣ |A| - 1` for a `D`-invariant `A ≤ Q₁`

`D` acts by conjugation on `Q₁` (`Q₁ ⊴ H`) and the action is fixed-point-free away from `1`
(`h.D_fpf_Q1`).  Restricting to a `D`-invariant subgroup `A ≤ Q₁`, the action of `D` on `↥A`
is free except for the trivial orbit: the fixed-point set of `1` is all of `A`, and the
fixed-point set of every other `d ∈ D` is `{1}`.

Burnside's lemma (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) then reads

`|A| + (|D| - 1) = #{orbits} · |D|`,

which rearranges to `|A| - 1 = (#{orbits} - 1) · |D|`.  In particular `|D| ∣ |A| - 1`.

The conjugation action of `D` on `A` is `h.conjAct A hAn` (from `FPF_orbit`), and the count of
fixed points of a nontrivial element is `h.fixedBy_card_eq_one`.
-/

set_option linter.style.haveILetI false

namespace Work.FeitSibley.GroupTheory

open Classical

theorem D_dvd_card_sub_one {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (A : Subgroup G) (hA : A ≤ h.Q1) (hAn : h.D ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card h.D ∣ Nat.card ↥A - 1 := by
  letI := h.conjAct A hAn
  -- The `fixedBy` of `MulAction` is the set of points fixed by the conjugation action.
  have hbridge : ∀ d : ↥h.D, Fintype.card (MulAction.fixedBy ↥A d)
      = Nat.card {x : ↥A // (d : G) * (x : G) * (d : G)⁻¹ = (x : G)} := by
    intro d
    have he : (MulAction.fixedBy ↥A d) ≃ {x : ↥A // (d : G) * (x : G) * (d : G)⁻¹ = (x : G)} :=
      Equiv.subtypeEquivRight (fun x => by
        rw [MulAction.mem_fixedBy]
        exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩)
    calc Fintype.card (MulAction.fixedBy ↥A d)
        = Fintype.card {x : ↥A // (d : G) * (x : G) * (d : G)⁻¹ = (x : G)} :=
          Fintype.card_congr he
      _ = Nat.card {x : ↥A // (d : G) * (x : G) * (d : G)⁻¹ = (x : G)} :=
          Nat.card_eq_fintype_card.symm
  -- `1` fixes everything.
  have hfix1 : Fintype.card (MulAction.fixedBy ↥A (1 : ↥h.D)) = Nat.card ↥A := by
    have he : (MulAction.fixedBy ↥A (1 : ↥h.D)) ≃ ↥A :=
      (Equiv.subtypeEquivRight (fun x => by rw [MulAction.mem_fixedBy]; simp)).trans
        (Equiv.Set.univ ↥A)
    calc Fintype.card (MulAction.fixedBy ↥A (1 : ↥h.D)) = Fintype.card ↥A :=
          Fintype.card_congr he
      _ = Nat.card ↥A := Nat.card_eq_fintype_card.symm
  -- Every nontrivial `d` fixes only `1`.
  have hfixne : ∀ d : ↥h.D, d ≠ 1 → Fintype.card (MulAction.fixedBy ↥A d) = 1 := by
    intro d hd
    rw [hbridge d]
    exact h.fixedBy_card_eq_one A hA hAn d (fun h1 => hd (Subtype.ext h1))
  -- The sum of the numbers of fixed points.
  have hsum : (∑ d : ↥h.D, Fintype.card (MulAction.fixedBy ↥A d))
      = Nat.card ↥A + (Nat.card h.D - 1) := by
    have h2 : (∑ d ∈ Finset.univ.erase (1 : ↥h.D), Fintype.card (MulAction.fixedBy ↥A d))
        = Nat.card h.D - 1 := by
      trans (∑ d ∈ Finset.univ.erase (1 : ↥h.D), (1 : ℕ))
      · exact Finset.sum_congr rfl (fun d hd => hfixne d (Finset.mem_erase.mp hd).1)
      · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
          ← Nat.card_eq_fintype_card]
        simp
    rw [← Finset.add_sum_erase Finset.univ
      (fun d : ↥h.D => Fintype.card (MulAction.fixedBy ↥A d)) (Finset.mem_univ 1), hfix1, h2]
  -- Burnside's lemma.
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥h.D ↥A
  have hmain : Nat.card ↥A + (Nat.card h.D - 1)
      = Fintype.card (Quotient (MulAction.orbitRel ↥h.D ↥A)) * Nat.card h.D := by
    rw [← hsum, hB, Nat.card_eq_fintype_card]
  have hn : 1 ≤ Nat.card h.D := by
    haveI : Nonempty ↥h.D := ⟨⟨1, h.D.one_mem⟩⟩
    exact Nat.card_pos
  have ha : 1 ≤ Nat.card ↥A := by
    haveI : Nonempty ↥A := ⟨⟨1, A.one_mem⟩⟩
    exact Nat.card_pos
  -- `|A| - 1 = (#orbits) · |D| - |D| = (#orbits - 1) · |D|`.
  have h1 : Nat.card ↥A - 1
      = Fintype.card (Quotient (MulAction.orbitRel ↥h.D ↥A)) * Nat.card h.D - Nat.card h.D := by
    omega
  have h2 : Fintype.card (Quotient (MulAction.orbitRel ↥h.D ↥A)) * Nat.card h.D - Nat.card h.D
      = (Fintype.card (Quotient (MulAction.orbitRel ↥h.D ↥A)) - 1) * Nat.card h.D := by
    rw [Nat.sub_mul, one_mul]
  rw [h1, h2]
  exact dvd_mul_left _ _

end Work.FeitSibley.GroupTheory
