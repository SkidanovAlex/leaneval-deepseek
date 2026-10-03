import Mathlib

/-!
# Rotating a word built from repeated copies

Let `A` be a list (a "word") over an alphabet `σ`, and let `k s : ℕ`.  The word
`(List.replicate k A).flatten` is the concatenation of `k` copies of `A`, so it is a periodic
word of period `A.length` and total length `k * A.length`.  Rotating this periodic word by `s`
amounts to reading it starting at the offset `s mod A.length`; doing the same inside every copy
of `A` yields the concatenation of `k` copies of `A.rotate s`.  This is the content of the main
theorem

`(List.replicate k A).flatten.rotate s = (List.replicate k (A.rotate s)).flatten`.

The proof compares the two words entrywise (they have the same length), using
`List.getElem?_rotate` together with the entry formula for a concatenation of copies.
-/

namespace Work.OROneRel

/-- The length of a word obtained by repeating `W` exactly `n` times is `n * W.length`. -/
theorem rfr_length_flatten_replicate {σ : Type*} (n : ℕ) (W : List σ) :
    (List.replicate n W).flatten.length = n * W.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

/-- In the word obtained by repeating `W` exactly `n` times, the entry at index `i` is
`W[i % W.length]`, whenever the index is in range. -/
theorem rfr_getElem?_flatten_replicate {σ : Type*} (n : ℕ) (W : List σ) (i : ℕ)
    (h : i < (List.replicate n W).flatten.length) :
    (List.replicate n W).flatten[i]? = W[i % W.length]? := by
  induction n generalizing i with
  | zero => exact absurd h (by simp)
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    by_cases hi : i < W.length
    · rw [List.getElem?_append_left hi, Nat.mod_eq_of_lt hi]
    · rw [List.getElem?_append_right (le_of_not_gt hi)]
      have h' : i - W.length < (List.replicate n W).flatten.length := by
        rw [rfr_length_flatten_replicate] at h ⊢
        have : (n + 1) * W.length = n * W.length + W.length := by ring
        omega
      rw [ih (i - W.length) h', Nat.mod_eq_sub_mod (le_of_not_gt hi)]

theorem rotate_flatten_replicate {σ : Type*} (k s : ℕ) (A : List σ) :
    (List.replicate k A).flatten.rotate s = (List.replicate k (A.rotate s)).flatten := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k * A.length
  · have hlenA : (List.replicate k A).flatten.length = k * A.length :=
      rfr_length_flatten_replicate k A
    have hlenB : (List.replicate k (A.rotate s)).flatten.length = k * A.length := by
      rw [rfr_length_flatten_replicate, List.length_rotate]
    have hP : i < (List.replicate k A).flatten.length := by rw [hlenA]; exact hi
    have hQ : i < (List.replicate k (A.rotate s)).flatten.length := by rw [hlenB]; exact hi
    have hpos : 0 < A.length := Nat.pos_of_mul_pos_left (lt_of_le_of_lt (Nat.zero_le i) hi)
    have hlenPpos : 0 < (List.replicate k A).flatten.length := by rw [hlenA]; omega
    rw [List.getElem?_rotate (l := (List.replicate k A).flatten) (n := s) (m := i) hP]
    rw [rfr_getElem?_flatten_replicate k A ((i + s) % (List.replicate k A).flatten.length)
      (Nat.mod_lt _ hlenPpos)]
    rw [hlenA]
    rw [rfr_getElem?_flatten_replicate k (A.rotate s) i hQ]
    rw [List.length_rotate]
    rw [List.getElem?_rotate (l := A) (n := s) (m := i % A.length) (Nat.mod_lt _ hpos)]
    congr 1
    rw [Nat.mod_mul_left_mod (i + s) k A.length]
    rw [Nat.add_mod (i % A.length) s A.length, Nat.mod_mod]
    exact Nat.add_mod i s A.length
  · rw [List.getElem?_eq_none (by
          rw [List.length_rotate, rfr_length_flatten_replicate]; exact le_of_not_gt hi),
        List.getElem?_eq_none (by
          rw [rfr_length_flatten_replicate, List.length_rotate]; exact le_of_not_gt hi)]

end Work.OROneRel
