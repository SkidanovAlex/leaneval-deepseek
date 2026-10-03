import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

set_option autoImplicit false

/-!
# `cellSum Λ = 2 ^ s` with `Λ.length = 2 ^ s` forces every leaf to have depth `s`

`cellSum Λ = ∑_{l ∈ Λ} 2 ^ (s - l.dep)`.  Since every leaf satisfies `l.dep ≤ s`, each summand is
`≥ 2 ^ 0 = 1`, with equality exactly when `l.dep = s`.  If the list has `2 ^ s` leaves, the sum is
at least `2 ^ s`, and equality holds only if *every* summand is `1`.

This is the "the subdivision is complete" half of the bookkeeping of the depth-first process: it
requires no hypothesis on `Λ` beyond the two numerical ones (in particular no `IsSubdiv`).

The proof uses the elementary list fact `eq_one_of_sum_eq_length`: a list of natural numbers all
`≥ 1` whose sum equals its length consists of `1`s.
-/

/-- A list of natural numbers, all `≥ 1`, whose sum equals its length, consists of `1`s. -/
private lemma eq_one_of_sum_eq_length : ∀ (L : List ℕ),
    (∀ x ∈ L, 1 ≤ x) → L.sum = L.length → ∀ x ∈ L, x = 1 := by
  intro L
  induction L with
  | nil => intro _ _ x hx; simp at hx
  | cons a t ih =>
    intro h1 h x hx
    have ha : 1 ≤ a := h1 a (List.mem_cons_self ..)
    have ht1 : ∀ y ∈ t, 1 ≤ y := fun y hy => h1 y (List.mem_cons_of_mem a hy)
    have htlen : t.length ≤ t.sum := List.length_le_sum_of_one_le t ht1
    simp only [List.sum_cons, List.length_cons] at h
    have haeq : a = 1 := by omega
    have hteq : t.sum = t.length := by omega
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact haeq
    · exact ih ht1 hteq x hx

/-- **The depth is forced by the cell sum and the cardinality.**  If the cell sizes of the leaves
of `Λ` sum to `2 ^ s` and there are `2 ^ s` leaves, then every leaf has depth `s` (so every cell is
a single point of `{0,1}^s`). -/
theorem depEqOfCellSumEqCard {s : ℕ} {Λ : List (Work.Peluse.SwapC.CLeaf s)}
    (hc : Work.Peluse.SwapC.cellSum Λ = 2 ^ s) (hl : Λ.length = 2 ^ s) :
    ∀ l ∈ Λ, l.dep = s := by
  intro l hlmem
  have hg1 : ∀ x ∈ Λ.map (fun l => 2 ^ (s - l.dep)), 1 ≤ x := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨m, _, rfl⟩ := hx
    exact Nat.one_le_two_pow
  have hsum : (Λ.map (fun l => 2 ^ (s - l.dep))).sum
      = (Λ.map (fun l => 2 ^ (s - l.dep))).length := by
    rw [List.length_map, hl, ← hc]
    rfl
  have hval : 2 ^ (s - l.dep) = 1 :=
    eq_one_of_sum_eq_length _ hg1 hsum _ (List.mem_map_of_mem hlmem)
  have hle : l.dep ≤ s := l.dep_le
  have hs : s - l.dep = 0 := by
    by_contra hne
    have hpos : 1 ≤ s - l.dep := by omega
    have h2 : 2 ≤ 2 ^ (s - l.dep) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (s - l.dep) := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  omega

end Work.Peluse.SwapC
