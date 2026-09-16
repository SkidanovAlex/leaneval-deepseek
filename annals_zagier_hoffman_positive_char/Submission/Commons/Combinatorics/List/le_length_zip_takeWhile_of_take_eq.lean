import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.TakeWhile

namespace Commons.Combinatorics.List

/-- If `x` is an element of `l.zip l`, then its two components are equal. -/
lemma fst_eq_snd_of_mem_zip_self {α : Type*} {l : List α} {x : α × α}
    (hx : x ∈ l.zip l) : x.1 = x.2 := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact ih hx

/-- If the first `n` elements of `l` all satisfy `p`, then `l.takeWhile p` is at least
as long as `l.take n`. -/
lemma length_take_le_length_takeWhile {α : Type*} {l : List α} {p : α → Bool} (n : ℕ)
    (h : ∀ x ∈ l.take n, p x = true) :
    (l.take n).length ≤ (l.takeWhile p).length := by
  have hself : (l.take n).takeWhile p = l.take n :=
    (List.takeWhile_eq_self_iff (p := p) (l := l.take n)).mpr h
  calc (l.take n).length = ((l.take n).takeWhile p).length := by rw [hself]
    _ = (List.take n (l.takeWhile p)).length := by rw [← List.take_takeWhile]
    _ ≤ (l.takeWhile p).length := by
        rw [List.length_take]
        exact Nat.min_le_right _ _

/-- If two lists coincide on their first `k` entries but are distinct, then each of them
has length at least `k`. -/
lemma le_length_of_take_eq_of_ne {α : Type*} {s s₀ : List α} {k : ℕ}
    (h : s.take k = s₀.take k) (hne : s ≠ s₀) : k ≤ s.length := by
  by_contra hk
  rw [not_le] at hk
  have hs : s.take k = s := (List.take_eq_self_iff s).mpr (le_of_lt hk)
  have h1 : s₀.take k = s := h.symm.trans hs
  have hlen : (s₀.take k).length = s.length := by rw [h1]
  have hs₀le : s₀.length ≤ k := by
    by_contra hlt
    rw [not_le] at hlt
    rw [List.length_take, Nat.min_eq_left (le_of_lt hlt)] at hlen
    omega
  have hs₀ : s₀.take k = s₀ := (List.take_eq_self_iff s₀).mpr hs₀le
  exact hne (h1.symm.trans hs₀)

theorem le_length_zip_takeWhile_of_take_eq {α : Type*} [DecidableEq α] {s s₀ : List α} {k : ℕ}
    (h : s.take k = s₀.take k) (hne : s ≠ s₀) :
    k ≤ ((s.zip s₀).takeWhile (fun p => p.1 = p.2)).length := by
  have hk₁ : k ≤ s.length := le_length_of_take_eq_of_ne h hne
  have hk₂ : k ≤ s₀.length := le_length_of_take_eq_of_ne h.symm (Ne.symm hne)
  have hkzip : k ≤ (s.zip s₀).length := by
    rw [List.length_zip]
    exact le_min hk₁ hk₂
  have htake : (s.zip s₀).take k = (s.take k).zip (s.take k) := by
    rw [List.zip_eq_zipWith, List.take_zipWith, List.zip_eq_zipWith, ← h]
  have hall : ∀ x ∈ (s.zip s₀).take k, (fun p : α × α => decide (p.1 = p.2)) x = true := by
    intro x hx
    rw [htake] at hx
    rw [decide_eq_true_eq]
    exact fst_eq_snd_of_mem_zip_self hx
  have hlenk : ((s.zip s₀).take k).length = k := by
    rw [List.length_take]
    exact Nat.min_eq_left hkzip
  have main : k ≤ (List.takeWhile (fun p : α × α => decide (p.1 = p.2)) (s.zip s₀)).length := by
    calc k = ((s.zip s₀).take k).length := hlenk.symm
      _ ≤ _ := length_take_le_length_takeWhile k hall
  exact main

end Commons.Combinatorics.List