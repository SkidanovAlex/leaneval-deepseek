import Mathlib
import Submission.Commons.Combinatorics.Counting.card_fun_image_card_le

namespace Commons.Combinatorics.Counting

open Finset
open scoped BigOperators

/-- If every value of `w : Fin 6 → Fin H` occurs at least twice, then its image has at most
`3` elements: the six fibres each have at least `2` elements. -/
private lemma card_image_le_three_of_forall_exists_eq {H : ℕ} (w : Fin 6 → Fin H)
    (hw : ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧ w j = w i) :
    (Finset.univ.image w).card ≤ 3 := by
  classical
  have hsum := Finset.card_eq_sum_card_image w (Finset.univ : Finset (Fin 6))
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hfib : ∀ c ∈ Finset.univ.image w,
      2 ≤ #{i ∈ (Finset.univ : Finset (Fin 6)) | w i = c} := by
    intro c hc
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hc
    obtain ⟨j, hji, hj⟩ := hw i
    have hi' : i ∈ (Finset.univ : Finset (Fin 6)).filter (fun i => w i = c) := by
      simp [hi]
    have hj' : j ∈ (Finset.univ : Finset (Fin 6)).filter (fun i => w i = c) := by
      simp [hj, hi]
    have h1 : 1 < #{i ∈ (Finset.univ : Finset (Fin 6)) | w i = c} := by
      rw [Finset.one_lt_card]
      exact ⟨i, hi', j, hj', fun h => hji h.symm⟩
    omega
  have h2 : 2 * (Finset.univ.image w).card
      ≤ ∑ c ∈ Finset.univ.image w, #{i ∈ (Finset.univ : Finset (Fin 6)) | w i = c} := by
    calc 2 * (Finset.univ.image w).card
        = ∑ _c ∈ Finset.univ.image w, 2 := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
      _ ≤ ∑ c ∈ Finset.univ.image w, #{i ∈ (Finset.univ : Finset (Fin 6)) | w i = c} :=
          Finset.sum_le_sum hfib
  omega

/-- The number of functions `w : Fin 6 → Fin H` such that every value `w i` occurs at least
twice (equivalently: no value occurs exactly once, i.e. `∀ i, ∃ j ≠ i, w j = w i`) is at most
`2916 * H^3`. Indeed the image of such a `w` has at most `3` elements, and the number of
functions `Fin 6 → Fin H` with image of card at most `3` is at most `4 * H^3 * 3^6 = 2916 H^3`
by `Commons.Combinatorics.Counting.card_fun_image_card_le`. -/
theorem card_forall_exists_eq_le (H : ℕ) :
    (Finset.univ.filter (fun w : Fin 6 → Fin H =>
        ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧ w j = w i)).card ≤ 2916 * H ^ 3 := by
  classical
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst hH
    haveI : IsEmpty (Fin 6 → Fin 0) := ⟨fun f => (f 0).elim0⟩
    simp
  · have hsub : (Finset.univ.filter (fun w : Fin 6 → Fin H =>
          ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧ w j = w i))
        ⊆ (Finset.univ.filter (fun B : Fin 6 → Fin H => (Finset.univ.image B).card ≤ 3)) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact card_image_le_three_of_forall_exists_eq w hw
    calc (Finset.univ.filter (fun w : Fin 6 → Fin H =>
            ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧ w j = w i)).card
        ≤ (Finset.univ.filter (fun B : Fin 6 → Fin H =>
            (Finset.univ.image B).card ≤ 3)).card := Finset.card_le_card hsub
      _ ≤ (3 + 1) * H ^ 3 * 3 ^ 6 := card_fun_image_card_le 6 H 3 hH
      _ = 2916 * H ^ 3 := by ring

end Commons.Combinatorics.Counting
