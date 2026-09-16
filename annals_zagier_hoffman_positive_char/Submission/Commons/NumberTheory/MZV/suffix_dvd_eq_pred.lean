import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.SuccPred

namespace Commons.NumberTheory.MZV

/-
The combinatorial core of Step 3 of Ngo Dac's proof of Zagier–Hoffman in positive
characteristic (Annals 194 (2021), §5.3): if all suffixes (starting from index `m` on) of a
finite sequence `s 0, …, s (r-1)` of integers in `[1, q-1]` have sum divisible by `q-1`,
then every entry from index `m` on equals `q-1`.

Proof: for each index `j`, either `j = r-1`, in which case the suffix is the single term
`s j`, or `j < r - 1`, in which case the suffix at `j` is the suffix at `j+1` plus the extra
term `s j`.  Either way `(q-1) ∣ s j`; combined with `1 ≤ s j ≤ q-1` this forces
`s j = q - 1`.
-/
theorem suffix_dvd_eq_pred {q : ℕ} (hq : 2 ≤ q) {s : ℕ → ℕ} {r m : ℕ}
    (hpos : ∀ j < r, 1 ≤ s j) (hle : ∀ j < r, s j ≤ q - 1)
    (hdiv : ∀ j, m ≤ j → j < r → (q - 1) ∣ ∑ i ∈ Finset.Icc j (r - 1), s i) :
    ∀ j, m ≤ j → j < r → s j = q - 1 := by
  intro j hmj hjr
  have hdvd : (q - 1) ∣ s j := by
    rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt hjr) with hlt | heq
    · -- j < r - 1 : compare the suffix at j with the suffix at j+1
      have hsplit : ∑ i ∈ Finset.Icc j (r - 1), s i
          = s j + ∑ i ∈ Finset.Icc (j + 1) (r - 1), s i := by
        rw [← Finset.insert_Icc_succ_left_eq_Icc (by omega : j ≤ r - 1),
          Order.succ_eq_add_one, Finset.sum_insert (by simp)]
      have h2 : (q - 1) ∣ ∑ i ∈ Finset.Icc (j + 1) (r - 1), s i :=
        hdiv (j + 1) (by omega) (by omega)
      have h1 : (q - 1) ∣ s j + ∑ i ∈ Finset.Icc (j + 1) (r - 1), s i := by
        rw [← hsplit]; exact hdiv j hmj hjr
      exact (Nat.dvd_add_iff_left
        (m := s j) (n := ∑ i ∈ Finset.Icc (j + 1) (r - 1), s i) h2).mpr h1
    · -- j = r - 1 : the suffix is the single term s j
      have hjeq : j = r - 1 := heq
      have hsum : ∑ i ∈ Finset.Icc j (r - 1), s i = s j := by
        rw [← hjeq, Finset.Icc_self]; simp
      have h1 := hdiv j hmj hjr
      rwa [hsum] at h1
  have h0 : 0 < s j := by have h1 := hpos j hjr; have h2 := hq; omega
  have hle' : s j ≤ q - 1 := hle j hjr
  have hge : q - 1 ≤ s j := Nat.le_of_dvd h0 hdvd
  omega

end Commons.NumberTheory.MZV