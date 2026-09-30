import Mathlib
import Submission.Work.BW.extract_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-- Counting lemma for the `foldr` used in `wordOf`: appending one replicate block per
element of `L`, the `p`-count of the result is the `p`-count of the initial segment plus the
sum of the `p`-counts of the individual blocks. -/
lemma wordOf_foldr_countP {ℓ : ℕ} (g : Fin ℓ → ℕ) (p : Fin ℓ → Bool) (l₀ : List (Fin ℓ)) :
    ∀ L : List (Fin ℓ),
    (L.foldr (fun i acc => acc ++ List.replicate (g i) i) l₀).countP p
      = l₀.countP p + (L.map (fun i => (List.replicate (g i) i).countP p)).sum := by
  intro L
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons, List.countP_append, List.map_cons, List.sum_cons, ih]
    omega

/-- Length lemma for the `foldr` used in `wordOf`. -/
lemma wordOf_foldr_length {ℓ : ℕ} (g : Fin ℓ → ℕ) (l₀ : List (Fin ℓ)) :
    ∀ L : List (Fin ℓ),
    (L.foldr (fun i acc => acc ++ List.replicate (g i) i) l₀).length
      = l₀.length + (L.map g).sum := by
  intro L
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons, List.length_append, List.length_replicate, List.map_cons, List.sum_cons, ih]
    omega

/-- The word attached to a multi-index `α` contains exactly `α i` occurrences of `i`, and its length is `∑ i, α i`. -/
theorem wordof_facts {ℓ : ℕ} (α : Fin ℓ → ℕ) :
    (∀ i : Fin ℓ, cnt (wordOf α) i = α i) ∧ ((wordOf α).length = ∑ i, α i) := by
  constructor
  · intro i
    rw [cnt, wordOf, wordOf_foldr_countP (g := α) (p := fun j => decide (j = i)) (l₀ := [])]
    simp only [List.countP_nil, zero_add]
    have hnod := List.nodup_finRange ℓ
    rw [← List.sum_toFinset (fun j => (List.replicate (α j) j).countP (fun k => decide (k = i))) hnod,
        List.toFinset_finRange]
    rw [Finset.sum_eq_single i]
    · rw [List.countP_replicate]; simp
    · intro b _ hb
      rw [List.countP_replicate]; simp [hb]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · rw [wordOf, wordOf_foldr_length (g := α) (l₀ := [])]
    simp only [List.length_nil, zero_add]
    rw [← List.sum_toFinset α (List.nodup_finRange ℓ), List.toFinset_finRange]

end Work.BW
