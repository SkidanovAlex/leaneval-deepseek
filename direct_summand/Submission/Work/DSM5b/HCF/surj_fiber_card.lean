import Mathlib

/-!
# Fibres of a surjection `Fin (n+2) → Fin (n+1)`

A surjection `v : Fin (n + 2) → Fin (n + 1)` has a unique fibre of cardinality two, and every
other fibre is a singleton.  Indeed the fibres partition `Fin (n+2)` into `n+1` nonempty parts
with `n+2` elements in total, so the multiset of fibre cardinalities is `{2, 1, 1, …, 1}`.

The counting content is isolated in the auxiliary lemma `fin_sum_one_structure`.
-/

namespace Work.DSM5b.HCF

/-- **Counting lemma.** If `c : Fin m → ℕ` is everywhere positive and `∑ c = m + 1`, then `c`
takes the value `2` at exactly one point and the value `1` everywhere else. -/
lemma fin_sum_one_structure {m : ℕ} (c : Fin m → ℕ)
    (hpos : ∀ y, 1 ≤ c y) (hsum : ∑ y : Fin m, c y = m + 1) :
    ∃ y : Fin m, c y = 2 ∧ ∀ y' : Fin m, y' ≠ y → c y' = 1 := by
  -- the "excess over one", `c y - 1`, is nonnegative and sums to `1`
  have hd : ∑ y : Fin m, (c y - 1) = 1 := by
    rw [Finset.sum_tsub_distrib (s := Finset.univ) (f := c) (g := fun _ : Fin m => (1 : ℕ))
      (fun y _ => hpos y)]
    have h1 : ∑ _y : Fin m, (1 : ℕ) = m := by simp
    rw [h1, hsum]
    omega
  -- some coordinate carries a positive excess
  obtain ⟨a, ha⟩ : ∃ a : Fin m, c a - 1 ≠ 0 := by
    by_contra h
    have hz : ∑ y : Fin m, (c y - 1) = 0 :=
      Finset.sum_eq_zero (fun y _ => by
        by_contra hh
        exact h ⟨y, hh⟩)
    omega
  -- that coordinate carries the whole excess
  have hda : c a - 1 = 1 := by
    have hle : c a - 1 ≤ ∑ y : Fin m, (c y - 1) :=
      Finset.single_le_sum (f := fun y => c y - 1) (fun y _ => Nat.zero_le _) (Finset.mem_univ a)
    omega
  -- and all the remaining coordinates contribute nothing
  have hrest : ∀ y' : Fin m, y' ≠ a → c y' - 1 = 0 := by
    intro y' hy'
    have hposy' : 1 ≤ c y' := hpos y'
    have hmem : y' ∈ (Finset.univ : Finset (Fin m)).erase a := by
      simp [hy']
    have hle : c y' - 1 ≤ ∑ y ∈ (Finset.univ : Finset (Fin m)).erase a, (c y - 1) :=
      Finset.single_le_sum (f := fun y => c y - 1) (fun y _ => Nat.zero_le _) hmem
    have hzero : ∑ y ∈ (Finset.univ : Finset (Fin m)).erase a, (c y - 1) = 0 := by
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
        (fun y => c y - 1) (Finset.mem_univ a)
      omega
    omega
  exact ⟨a, by omega, fun y' hy' => by have := hrest y' hy'; have := hpos y'; omega⟩

theorem surj_fiber_card {n : ℕ} (v : Fin (n + 2) → Fin (n + 1))
    (hv : Function.Surjective v) :
    ∃ y : Fin (n + 1),
      (Finset.univ.filter (fun i : Fin (n + 2) => v i = y)).card = 2 ∧
      ∀ y' : Fin (n + 1), y' ≠ y →
        (Finset.univ.filter (fun i : Fin (n + 2) => v i = y')).card = 1 := by
  -- the fibres partition `Fin (n+2)`, so their cardinalities sum to `n + 2 = (n+1) + 1`
  have hsum : ∑ y : Fin (n + 1),
      (Finset.univ.filter (fun i : Fin (n + 2) => v i = y)).card = (n + 1) + 1 := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (n + 2))))
      (t := (Finset.univ : Finset (Fin (n + 1)))) (f := v) (fun x _ => Finset.mem_univ _)
    simpa using h.symm
  -- each fibre is nonempty because `v` is surjective
  have hpos : ∀ y : Fin (n + 1),
      1 ≤ (Finset.univ.filter (fun i : Fin (n + 2) => v i = y)).card := by
    intro y
    obtain ⟨i, hi⟩ := hv y
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  obtain ⟨y, hy2, hy1⟩ := fin_sum_one_structure
    (fun y : Fin (n + 1) => (Finset.univ.filter (fun i : Fin (n + 2) => v i = y)).card) hpos hsum
  exact ⟨y, hy2, hy1⟩

end Work.DSM5b.HCF
