import Mathlib
import Submission.Work.Layout.Take.Basic

namespace Work.Layout.Take

/-! ## Helpers for the amortised bound

`oneB l` is the popcount of an LSB-first bit list `l`.  The key identity relating it to `tzB`
(the number of trailing zeros, i.e. leading `false`s) is proved by strong induction on `n`,
splitting on the parity of `n` (which is exactly the binary expansion `n = 2*m` / `n = 2*m+1`).
-/

/-- `oneB l` counts the `true` bits of the LSB-first bit list `l`, i.e. the popcount of the
number it encodes. -/
def oneB (l : List Bool) : ℕ := l.countP id

@[simp] theorem oneB_true_cons (t : List Bool) : oneB (true :: t) = oneB t + 1 :=
  List.countP_cons_of_pos (p := id) (a := true) (l := t) rfl

@[simp] theorem oneB_false_cons (t : List Bool) : oneB (false :: t) = oneB t :=
  List.countP_cons_of_neg (p := id) (a := false) (l := t) (by simp)

@[simp] theorem oneB_nil : oneB ([] : List Bool) = 0 := rfl

@[simp] theorem tzB_cons_false' (t : List Bool) :
    Work.Layout.tzB (false :: t) = Work.Layout.tzB t + 1 := rfl

@[simp] theorem tzB_cons_true' (t : List Bool) : Work.Layout.tzB (true :: t) = 0 := rfl

/-- Popcount plus trailing zeros: passing from `n > 0` to `n - 1` loses one `true` and gains
`tzB n.bits` more `true`s.  In other words `oneB n.bits + tzB n.bits = oneB (n-1).bits + 1`. -/
theorem oneB_bits_pred (n : ℕ) (hn : 0 < n) :
    oneB n.bits + Work.Layout.tzB n.bits = oneB (n - 1).bits + 1 := by
  revert hn
  refine Nat.strong_induction_on n fun n ih hn => ?_
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `n = 2 * m`, low bit `false`
    have hn2 : n = 2 * m := by omega
    have hm0 : m ≠ 0 := by omega
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    rw [hn2] at hn ⊢
    have hsub : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [Nat.bit0_bits m hm0, hsub, Nat.bit1_bits]
    simp only [oneB_false_cons, oneB_true_cons, tzB_cons_false']
    have ih' := ih m (by omega) hmpos
    omega
  · -- `n = 2 * m + 1`, low bit `true`
    have hn2 : n = 2 * m + 1 := by omega
    rw [hn2] at hn ⊢
    rw [Nat.bit1_bits]
    simp only [oneB_true_cons, tzB_cons_true']
    have hsub : 2 * m + 1 - 1 = 2 * m := by omega
    rw [hsub]
    by_cases hm0 : m = 0
    · subst m
      simp [oneB]
    · rw [Nat.bit0_bits m hm0]
      simp only [oneB_false_cons]

/-- Telescoping the key identity over `m` successive decrements: the total `tzB` cost plus the
final popcount equals `m` plus the popcount of the last counter. -/
theorem tzB_sum_add_oneB (k : ℕ) : ∀ m, m ≤ k →
    (∑ i ∈ Finset.range m, Work.Layout.tzB ((k - i).bits)) + oneB k.bits
      = m + oneB ((k - m).bits) := by
  intro m
  induction m with
  | zero =>
      intro _
      rw [Finset.sum_range_zero]
      simp
  | succ m ih =>
      intro hk
      have hmk : m ≤ k := by omega
      have hstep := ih hmk
      have hpos : 0 < k - m := by omega
      have hkey := oneB_bits_pred (k - m) hpos
      have hkm : k - m - 1 = k - (m + 1) := by omega
      have hsucc : (∑ i ∈ Finset.range (m + 1), Work.Layout.tzB ((k - i).bits))
          = (∑ i ∈ Finset.range m, Work.Layout.tzB ((k - i).bits))
              + Work.Layout.tzB ((k - m).bits) :=
        Finset.sum_range_succ _ _
      calc (∑ i ∈ Finset.range (m + 1), Work.Layout.tzB ((k - i).bits)) + oneB k.bits
          = ((∑ i ∈ Finset.range m, Work.Layout.tzB ((k - i).bits))
              + oneB k.bits) + Work.Layout.tzB ((k - m).bits) := by rw [hsucc]; ring
        _ = (m + oneB ((k - m).bits)) + Work.Layout.tzB ((k - m).bits) := by rw [hstep]
        _ = m + (oneB ((k - m).bits) + Work.Layout.tzB ((k - m).bits)) := by ring
        _ = m + (oneB (k - m - 1).bits + 1) := by rw [hkey]
        _ = m + 1 + oneB ((k - (m + 1)).bits) := by rw [hkm]; ring

/-- Amortised bound for the total `tzB` cost of `m` successive decrements starting from `k`.
Here `tzB l` (defined in `Submission/Work/Layout/Take/Defs.lean`, namespace `Work.Layout`) counts
the leading `false`s of an LSB-first bit list `l`, i.e. the trailing zeros of the natural number it
encodes; one decrement of the binary counter `k` costs `20 * (tzB k.bits + 2)` (see `DecStep`), so
`m` successive decrements with counters `k, k-1, …, k-m+1` cost `∑_{i<m} tzB ((k-i).bits)`; the
amortised bound `≤ m + (k-m).size` is the content of this statement.  (Proof sketch: with
`oneB l = l.countP id` counting the `true`s, the key identity is
`oneB n.bits + tzB n.bits = oneB (n-1).bits + 1` for `n > 0`, by induction on the binary expansion
`Nat.binaryRec'`: for `n = 2*m+1`, `n.bits = true :: m.bits`, `tzB n.bits = 0` and
`(n-1).bits = (2*m).bits = false :: m.bits`; for `n = 2*m` with `m ≠ 0`, `n.bits = false :: m.bits`,
`tzB n.bits = tzB m.bits + 1` and `(n-1).bits = (2*(m-1)+1).bits = true :: (m-1).bits`, the
induction hypothesis at `m`.  Telescoping this over `i < m` — all counters `k-i` are `> 0` since
`m ≤ k` — gives `(∑_{i<m} tzB ((k-i).bits)) + oneB k.bits = m + oneB (k-m).bits`, and
`oneB (k-m).bits ≤ (k-m).size` follows from `List.countP_le_length` and `Nat.size_eq_bits_len`.
Namespace `Work.Layout.Take`.) -/
theorem tzB_sum_le (m k : ℕ) (h : m ≤ k) :
    (∑ i ∈ Finset.range m, Work.Layout.tzB ((k - i).bits)) ≤ m + (k - m).size := by
  have hsum := tzB_sum_add_oneB k m h
  have h1 : (∑ i ∈ Finset.range m, Work.Layout.tzB ((k - i).bits))
      ≤ m + oneB ((k - m).bits) := by
    rw [← hsum]
    exact Nat.le_add_right _ _
  have h2 : oneB ((k - m).bits) ≤ (k - m).size := by
    have hlen := List.countP_le_length (p := id) (l := (k - m).bits)
    simpa [oneB, Nat.size_eq_bits_len] using hlen
  exact le_trans h1 (Nat.add_le_add_left h2 m)

end Work.Layout.Take
