import Mathlib
import Submission.Work.OROneRel.weinbaumDefs

/-!
# Counting letters and the exponent sum, at the level of words

Auxiliary vocabulary for `Work.OROneRel.letterCountNot_lt_of_isSubwordOf_half`.

For a word `L : List (α × Bool)` and a generator `t : α` we define

* `tcount t L` -- the number of letters of `L` whose generator is `t` (either orientation);
* `ssum t L` -- the exponent sum of `t` in `L`, as an integer (`+1` for `(t, true)`,
  `-1` for `(t, false)`, `0` for any other letter).

Both are stated with `Classical` decidability inside the definition so that no `DecidableEq`
hypothesis leaks into any statement.

The main results here are

* `letterCountNot_mk_of_isReduced` : for a reduced word `L`, the number of letters of `mk L`
  other than `t` is `L.length - tcount t L`;
* `tcount_eq_length_iff` : all letters of `L` have generator `t` iff `tcount t L = L.length`;
* `ssum_replicate` : the exponent sum of a constant word.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The indicator, as a `Bool`, of "the generator of the letter `p` is `t`". -/
noncomputable def tp (t : α) : α × Bool → Bool := by
  classical exact fun p => decide (p.1 = t)

/-- The number of letters of the word `L` whose generator is `t`. -/
noncomputable def tcount (t : α) (L : List (α × Bool)) : ℕ := L.countP (tp t)

/-- The contribution of a single letter to the exponent sum of `t`. -/
noncomputable def gfun (t : α) (p : α × Bool) : ℤ := by
  classical exact if p.1 = t then (if p.2 then (1 : ℤ) else -1) else 0

/-- The exponent sum of the generator `t` in the word `L`, as an integer. -/
noncomputable def ssum (t : α) (L : List (α × Bool)) : ℤ := (L.map (gfun t)).sum

theorem tp_eq_true_iff (t : α) (p : α × Bool) : tp t p = true ↔ p.1 = t := by
  classical simp [tp]

theorem tcount_eq_length_iff (t : α) (L : List (α × Bool)) :
    tcount t L = L.length ↔ ∀ p ∈ L, p.1 = t := by
  classical
  rw [tcount, List.countP_eq_length]
  exact ⟨fun h p hp => (tp_eq_true_iff t p).mp (h p hp),
    fun h p hp => (tp_eq_true_iff t p).mpr (h p hp)⟩

theorem tcount_le_length (t : α) (L : List (α × Bool)) : tcount t L ≤ L.length :=
  List.countP_le_length

theorem countP_add_countP_not (t : α) (L : List (α × Bool)) :
    L.countP (tp t) + L.countP (fun p => !tp t p) = L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.countP_cons, List.countP_cons]
    by_cases h : tp t a = true <;> simp [h] <;> omega

/-- The number of letters of `L` other than `t`, expressed in terms of `tcount`. -/
theorem countP_not_eq (t : α) (L : List (α × Bool)) :
    L.countP (fun p => !tp t p) = L.length - tcount t L := by
  have := countP_add_countP_not t L
  rw [← this]
  simp [tcount]

theorem tcount_append (t : α) (L₁ L₂ : List (α × Bool)) :
    tcount t (L₁ ++ L₂) = tcount t L₁ + tcount t L₂ := by
  simp [tcount, List.countP_append]

theorem tcount_rotate (t : α) (L : List (α × Bool)) (j : ℕ) :
    tcount t (L.rotate j) = tcount t L := by
  rw [tcount, tcount, List.countP_eq_length_filter, List.countP_eq_length_filter]
  exact ((List.rotate_perm L j).filter (tp t)).length_eq

theorem ssum_append (t : α) (L₁ L₂ : List (α × Bool)) :
    ssum t (L₁ ++ L₂) = ssum t L₁ + ssum t L₂ := by
  simp [ssum, List.map_append, List.sum_append]

theorem ssum_nil (t : α) : ssum t ([] : List (α × Bool)) = 0 := by simp [ssum]

theorem ssum_rotate (t : α) (L : List (α × Bool)) (j : ℕ) :
    ssum t (L.rotate j) = ssum t L := by
  have h : (L.rotate j).map (gfun t) |>.Perm (L.map (gfun t)) :=
    (List.rotate_perm L j).map (gfun t)
  exact h.sum_eq

theorem ssum_replicate (t : α) (n : ℕ) (b : Bool) :
    ssum t (List.replicate n (t, b)) = if b then (n : ℤ) else -(n : ℤ) := by
  classical
  rw [ssum, List.map_replicate]
  cases b <;> simp [gfun, List.sum_replicate]

/-- For a reduced word `L`, the number of letters of `mk L` other than `t` is
`L.length - tcount t L`. -/
theorem letterCountNot_mk_of_isReduced (t : α) {L : List (α × Bool)}
    (hL : FreeGroup.IsReduced L) :
    letterCountNot t (FreeGroup.mk L) = L.length - tcount t L := by
  classical
  have h1 : letterCountNot t (FreeGroup.mk L) = L.countP (fun p => !tp t p) := by
    rw [letterCountNot, FreeGroup.toWord_mk, hL.reduce_eq]
    apply List.countP_congr
    intro p hp
    by_cases h : p.1 = t <;> simp [tp, h]
  rw [h1, countP_not_eq]

end Work.OROneRel
