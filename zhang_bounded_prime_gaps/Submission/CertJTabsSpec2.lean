import Submission.CertJTabsSpec1
import Submission.CertJTabs

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The group tables are the accumulated `J`-data
-/

namespace Commons.NumberTheory.MaynardSieve

/-- Accumulation of a list of weighted parts (`M`-valued weights). -/
def accumAux {M : Type*} [Add M] : List (ℕ × M) → (ℕ × M) → List (ℕ × M)
  | [], p => [p]
  | q :: t, p => if q.1 = p.1 then (q.1, q.2 + p.2) :: t else q :: accumAux t p

/-- Accumulate a list of `(ã, W)` pairs. -/
def accum {M : Type*} [Add M] (l : List (ℕ × M)) : List (ℕ × M) := l.foldl accumAux []

/-- The signed accumulated weights of a flat table, positionwise (zero entries dropped). -/
def accSigned (T : List (ℕ × ℕ × ℤ)) (i : ℕ) : List (ℕ × ℤ) :=
  List.insertionSort (fun a b : ℕ × ℤ => a.1 ≤ b.1)
    ((accum ((T.filter (fun t => decide (t.1 = i))).map (fun t => (t.2.1, t.2.2)))).filter
      (fun q => decide (q.2 ≠ 0)))

/-- The accumulated positive weights, positionwise. -/
def accPos (T : List (ℕ × ℕ × ℤ)) (i : ℕ) : List (ℕ × ℕ) :=
  ((accSigned T i).filter (fun q => decide (0 < q.2))).map (fun q => (q.1, q.2.natAbs))

/-- The accumulated negative weights, positionwise. -/
def accNeg (T : List (ℕ × ℕ × ℤ)) (i : ℕ) : List (ℕ × ℕ) :=
  ((accSigned T i).filter (fun q => decide (q.2 < 0))).map (fun q => (q.1, q.2.natAbs))

/-- Pre-filtering by a predicate implied by the position test does not change the fiber. -/
theorem filter_filter_of_imp {α : Type*} (T : List α) (P Q : α → Bool)
    (h : ∀ t ∈ T, Q t = true → P t = true) : (T.filter P).filter Q = T.filter Q := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro t ht
  by_cases hq : Q t = true
  · simp [hq, h t ht hq]
  · simp [hq]

/-- The accumulation at a position of the window `[off, off + 34)` only sees the window. -/
theorem accPos_wWin (off i : ℕ) (h1 : off ≤ i) (h2 : i < off + 34) :
    accPos (wWin off) i = accPos wTabP i := by
  unfold accPos accSigned wWin
  rw [filter_filter_of_imp]
  intro t _ ht
  simp only [decide_eq_true_eq] at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem accNeg_wWin (off i : ℕ) (h1 : off ≤ i) (h2 : i < off + 34) :
    accNeg (wWin off) i = accNeg wTabP i := by
  unfold accNeg accSigned wWin
  rw [filter_filter_of_imp]
  intro t _ ht
  simp only [decide_eq_true_eq] at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem gPosL_length : gPosL.length = 272 := by decide +kernel

theorem gNegL_length : gNegL.length = 272 := by decide +kernel

/-- **`mcL` is `mc 49 (mult β)` of the certificate's signatures.** -/
theorem mcL_spec : mcL = certGroupSigs.map (fun β => mc 49 (mult β)) := by decide

end Commons.NumberTheory.MaynardSieve
