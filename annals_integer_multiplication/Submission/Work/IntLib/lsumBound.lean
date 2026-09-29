import Mathlib
import Submission.Work.IntLib.chunkProg

/-!
# Cost of the main loop of the `chunk` word

`lsum b KC (b*N)` accumulates the cost bound `cstep b KC k` of the `b*N` iterations of the main
loop of the `chunk` word (plus one step for each loop test).  Inside every block of `b` consecutive
indices exactly two iterations are special: the first one of the block (`k % b = 0`) copies a chunk
and costs `KC*(b+1)` extra, and the last one of the block (`(k+1) % b = 0`) flushes the carry,
costing `3*b+30` extra.  Since the loop performs exactly `N = (b*N)/b` blocks, both special classes
occur exactly `N` times, whence

`lsum b KC (b*N) ≤ (KC + 134) * (N * (b+1))`.

The mathematical content is the counting lemma `modCount` (every residue class `c < b` occurs
exactly `N` times among `0 ≤ k < b*N`, for `b ≥ 1`) and `succModEqZero`
(`(k+1) % b = 0 ↔ k % b = b - 1`).
-/

namespace Work.IntLib

/-- Counting lemma: among `0 ≤ k < b*N` every residue class `c < b` occurs exactly `N` times
(`b ≥ 1`). -/
theorem modCount (b c N : ℕ) (hb : 1 ≤ b) (hc : c < b) :
    ∑ k ∈ Finset.range (b * N), (if k % b = c then 1 else 0) = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have h2 : ∀ i ∈ Finset.range b,
        (if (b * N + i) % b = c then 1 else 0) = (if i = c then 1 else 0) := by
      intro i hi
      have hi' : i < b := Finset.mem_range.mp hi
      have hmod : (b * N + i) % b = i := by
        rw [show b * N + i = i + b * N by omega, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hi']
      rw [hmod]
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hc)]

/-- For `b ≥ 1`, `k+1` is a multiple of `b` iff `k` has residue `b-1` modulo `b`. -/
theorem succModEqZero {b k : ℕ} (hb : 1 ≤ b) : (k + 1) % b = 0 ↔ k % b = b - 1 := by
  have key : (k + 1) % b = (k % b + 1) % b := by
    conv_lhs => rw [← Nat.div_add_mod k b]
    rw [show b * (k / b) + k % b + 1 = (k % b + 1) + b * (k / b) by ring,
      Nat.add_mul_mod_self_left]
  rw [key]
  constructor
  · intro h
    have hr : k % b < b := Nat.mod_lt k (show 0 < b by omega)
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hr : k % b + 1 ≤ b) with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · omega
  · intro h
    have hr : k % b < b := Nat.mod_lt k (show 0 < b by omega)
    rw [show k % b + 1 = b by omega, Nat.mod_self]

/-- `lsum` is the sum of the per-iteration bounds (each `cstep` plus one loop-test step). -/
theorem lsum_eq_sum (b KC m : ℕ) :
    lsum b KC m = ∑ k ∈ Finset.range m, (cstep b KC k + 1) := by
  induction m with
  | zero => simp [lsum]
  | succ m ih =>
    have h : lsum b KC (m + 1) = lsum b KC m + (cstep b KC m + 1) := rfl
    rw [h, ih, Finset.sum_range_succ]

/-- `cstep` unfolded, with the `1` of the loop-test step absorbed into its constant term. -/
theorem cstep_add_one (b KC k : ℕ) :
    cstep b KC k + 1 = 101 + (if k % b = 0 then KC * (b + 1) else 0)
      + (if (k + 1) % b = 0 then 3 * b + 30 else 0) := by
  by_cases h1 : k % b = 0 <;> by_cases h2 : (k + 1) % b = 0 <;>
    simp [cstep, h1, h2] <;> omega

/-- A constant sum over a range. -/
theorem sum_range_const (m c : ℕ) : ∑ k ∈ Finset.range m, c = c * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- The loop cost, estimated by charging each iteration the base cost `101` plus the (at most one
per block) extra costs for chunk copying and carry flushing. -/
theorem lsumBlock (b N KC : ℕ) (hb : 1 ≤ b) :
    lsum b KC (b * N) ≤ 101 * (b * N) + (KC * (b + 1)) * N + (3 * b + 30) * N := by
  rw [lsum_eq_sum]
  have hc1 : b - 1 < b := by omega
  have hA : ∑ k ∈ Finset.range (b * N), (if k % b = 0 then KC * (b + 1) else 0)
      = (KC * (b + 1)) * N := by
    calc ∑ k ∈ Finset.range (b * N), (if k % b = 0 then KC * (b + 1) else 0)
        = ∑ k ∈ Finset.range (b * N),
            (KC * (b + 1)) * (if k % b = 0 then 1 else 0) :=
          Finset.sum_congr rfl fun k _ => by by_cases h : k % b = 0 <;> simp [h]
      _ = (KC * (b + 1)) * ∑ k ∈ Finset.range (b * N), (if k % b = 0 then 1 else 0) := by
          rw [Finset.mul_sum]
      _ = (KC * (b + 1)) * N := by rw [modCount b 0 N hb hb]
  have hB : ∑ k ∈ Finset.range (b * N), (if (k + 1) % b = 0 then 3 * b + 30 else 0)
      = (3 * b + 30) * N := by
    calc ∑ k ∈ Finset.range (b * N), (if (k + 1) % b = 0 then 3 * b + 30 else 0)
        = ∑ k ∈ Finset.range (b * N),
            (3 * b + 30) * (if k % b = b - 1 then 1 else 0) :=
          Finset.sum_congr rfl fun k _ => by
            by_cases h : k % b = b - 1
            · rw [if_pos ((succModEqZero hb).mpr h), if_pos h, mul_one]
            · rw [if_neg (fun hc => h ((succModEqZero hb).mp hc)), if_neg h, mul_zero]
      _ = (3 * b + 30) * ∑ k ∈ Finset.range (b * N), (if k % b = b - 1 then 1 else 0) := by
          rw [Finset.mul_sum]
      _ = (3 * b + 30) * N := by rw [modCount b (b - 1) N hb hc1]
  calc ∑ k ∈ Finset.range (b * N), (cstep b KC k + 1)
      = ∑ k ∈ Finset.range (b * N), (101 + (if k % b = 0 then KC * (b + 1) else 0)
          + (if (k + 1) % b = 0 then 3 * b + 30 else 0)) :=
        Finset.sum_congr rfl fun k _ => cstep_add_one b KC k
    _ ≤ 101 * (b * N) + (KC * (b + 1)) * N + (3 * b + 30) * N :=
        le_of_eq (by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB,
          sum_range_const])

theorem lsumBound (b N KC : ℕ) (hb : 1 ≤ b) :
    Work.IntLib.lsum b KC (b * N) ≤ (KC + 134) * (N * (b + 1)) := by
  refine (lsumBlock b N KC hb).trans ?_
  have h1 : 101 * (b * N) + (KC * (b + 1)) * N + (3 * b + 30) * N
      = N * (101 * b + KC * (b + 1) + (3 * b + 30)) := by ring
  have h2 : (KC + 134) * (N * (b + 1)) = N * ((KC + 134) * (b + 1)) := by ring
  rw [h1, h2]
  exact Nat.mul_le_mul_left N (by nlinarith [hb])

end Work.IntLib
