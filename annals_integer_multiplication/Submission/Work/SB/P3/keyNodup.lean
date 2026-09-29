import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared
import Submission.Work.Layout.unslicesIdx

namespace Work.SB.P3

open HvdH
open Work.Layout

/-!
# Distinctness of the output keys of the second labelling

The second labelling of `applyAlong` sends the element at flat position `f` of the flattened
output slices to the flat index `tgtIdx n B (f/n) (f%n)` of the `A × n × B` output array.
Sorting by these keys is only meaningful if the keys are pairwise distinct, which is the content
of `keyNodup`: the map `f ↦ tgtIdx n B (f/n) (f%n)` is injective.

The reason is that `tgtIdx` is injective on pairs `(s,j)` with `j < n` (and `B > 0`), with no
bound on `s` required: from `r = (s/B*n + j)*B + s%B` one reads back `s%B = r % B` and
`s/B*n + j = r / B`, whence `s/B = (r/B)/n` and `j = (r/B) % n`.  Injectivity for `f` then
follows from `f = n*(f/n) + f%n`.
-/

/-- The remainder of `tgtIdx n B s j` modulo `B` only depends on `s`. -/
private lemma tgtIdx_mod (n B s j : ℕ) (hB : 0 < B) : tgtIdx n B s j % B = s % B := by
  simp only [tgtIdx]
  rw [Nat.mul_comm (s / B * n + j) B, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.mod_lt s hB)]

/-- The quotient of `tgtIdx n B s j` by `B` is `s/B*n + j`, the middle index in `[0, n*B)`. -/
private lemma tgtIdx_div (n B s j : ℕ) (hB : 0 < B) : tgtIdx n B s j / B = s / B * n + j := by
  simp only [tgtIdx]
  rw [Nat.mul_comm (s / B * n + j) B, Nat.mul_add_div hB, Nat.div_eq_of_lt (Nat.mod_lt s hB),
    Nat.add_zero]

/-- `tgtIdx n B` is injective on pairs whose second component is `< n`. -/
private lemma tgtIdx_inj {n B : ℕ} (hn : 0 < n) (hB : 0 < B) {s j s' j' : ℕ}
    (hj : j < n) (hj' : j' < n) (h : tgtIdx n B s j = tgtIdx n B s' j') : s = s' ∧ j = j' := by
  have hm : s % B = s' % B := by rw [← tgtIdx_mod n B s j hB, ← tgtIdx_mod n B s' j' hB, h]
  have hd : s / B * n + j = s' / B * n + j' := by
    rw [← tgtIdx_div n B s j hB, ← tgtIdx_div n B s' j' hB, h]
  have hq : s / B = s' / B := by
    have h1 : (s / B * n + j) / n = s / B := by
      rw [Nat.mul_comm (s / B) n, Nat.mul_add_div hn, Nat.div_eq_of_lt hj, Nat.add_zero]
    have h2 : (s' / B * n + j') / n = s' / B := by
      rw [Nat.mul_comm (s' / B) n, Nat.mul_add_div hn, Nat.div_eq_of_lt hj', Nat.add_zero]
    rw [← h1, ← h2, hd]
  have hjj : j = j' := by
    rw [hq] at hd
    exact Nat.add_left_cancel hd
  have hs : s = s' := by
    calc s = B * (s / B) + s % B := (Nat.div_add_mod s B).symm
      _ = B * (s' / B) + s' % B := by rw [hq, hm]
      _ = s' := Nat.div_add_mod s' B
  exact ⟨hs, hjj⟩

/-- `f ↦ tgtIdx n B (f/n) (f%n)` is injective on `ℕ`. -/
private lemma key_pair_inj {n B : ℕ} (hn : 0 < n) (hB : 0 < B) {f f' : ℕ}
    (h : tgtIdx n B (f / n) (f % n) = tgtIdx n B (f' / n) (f' % n)) : f = f' := by
  have hpair := tgtIdx_inj hn hB (Nat.mod_lt f hn) (Nat.mod_lt f' hn) h
  have h1 : f / n = f' / n := hpair.1
  have h2 : f % n = f' % n := hpair.2
  calc f = n * (f / n) + f % n := (Nat.div_add_mod f n).symm
    _ = n * (f' / n) + f' % n := by rw [h1, h2]
    _ = f' := Nat.div_add_mod f' n

theorem keyNodup (n B M : ℕ) (hn : 0 < n) (hB : 0 < B) :
    (((List.range M).map fun f => ((tgtIdx n B (f / n) (f % n) : ℕ) : ℤ))).Nodup := by
  exact List.Nodup.map
    (fun a b hab => key_pair_inj hn hB (Int.natCast_inj.mp hab)) List.nodup_range

end Work.SB.P3
