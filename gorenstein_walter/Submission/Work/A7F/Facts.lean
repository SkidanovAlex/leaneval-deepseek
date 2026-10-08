/-
Area A7F of the Gorenstein--Walter project: basic facts about the model `A₇`.

This file derives the "all involutions are conjugate" and "the centralizer of every involution has
order `24`" facts from the two counting lemmas `a7InvSet_card` and `a7ConjClass_card` (proved
elsewhere in the area) and the model computation `card_centralizer_a7Invol`.
-/
import Mathlib
import Submission.Work.A7F.Defs
import Submission.Work.A7F.a7S0_structure
import Submission.Work.A7F.a7InvSet_card
import Submission.Work.A7F.a7ConjClass_card
import Submission.Work.A7F.card_centralizer_a7Invol
import Submission.Work.A7F.card_centralizer_conj

open scoped MatrixGroups

namespace Work.A7F

open Subgroup

/-- Every element of the conjugacy class of the model involution `t = (01)(23)` is a nontrivial
involution of `A₇`. -/
theorem a7ConjClass_subset_a7InvSet : a7ConjClass a7Invol ⊆ a7InvSet := by
  intro x hx
  rw [a7ConjClass, Finset.mem_image] at hx
  obtain ⟨g, -, rfl⟩ := hx
  rw [a7InvSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro h
    have hconj : a7Invol = g⁻¹ * (g * a7Invol * g⁻¹) * g := by group
    rw [h] at hconj
    simp at hconj
    exact Work.A7.a7Invol_ne_one hconj
  · calc (g * a7Invol * g⁻¹) * (g * a7Invol * g⁻¹)
        = g * (a7Invol * a7Invol) * g⁻¹ := by group
      _ = 1 := by rw [a7Invol_mul_self, mul_one, mul_inv_cancel]

/-- **All involutions of `A₇` are conjugate to the model involution `t = (01)(23)`.**

The conjugacy class of `t` consists of involutions, and both the class and the set of nontrivial
involutions have `105` elements. -/
theorem isConj_a7Invol_of_involution (t : alternatingGroup (Fin 7)) (h1 : t ≠ 1)
    (h2 : t * t = 1) : IsConj a7Invol t := by
  have heq : a7ConjClass a7Invol = a7InvSet :=
    Finset.eq_of_subset_of_card_le a7ConjClass_subset_a7InvSet
      (by rw [a7InvSet_card, a7ConjClass_card])
  have hmem : t ∈ a7ConjClass a7Invol := by
    rw [heq, a7InvSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h1, h2⟩
  rw [a7ConjClass, Finset.mem_image] at hmem
  obtain ⟨g, -, hg⟩ := hmem
  exact isConj_iff.mpr ⟨g, hg⟩

/-- An element of order two in `A₇` is conjugate to the model involution `t = (01)(23)`. -/
theorem isConj_a7Invol_of_orderOf_two (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    IsConj a7Invol t := by
  have h1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have h2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  exact isConj_a7Invol_of_involution t h1 h2

/-- **The centralizer in `A₇` of every involution has order `24`** (Bender 1.8). -/
theorem card_centralizer_of_involution (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) = 24 := by
  have h1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have h2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_a7Invol_of_involution t h1 h2)
  rw [← hg, card_centralizer_conj, card_centralizer_a7Invol]

end Work.A7F
