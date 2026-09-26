import Mathlib
import Submission.Work.PTCert.GlueDefs

namespace Work.PTCert.ldlChainSound

open Submission.PTCert

/-- `dotZ` on a pair of conses: the head product plus the `dotZ` of the tails. -/
theorem dotZ_cons_cons (x y : ℤ) (a b : List ℤ) :
    dotZ (x :: a) (y :: b) = x * y + dotZ a b := by
  simp [Submission.PTCert.dotZ, List.zipWith_cons_cons, List.foldr_cons]

/-- `dotZ` as a sum over `range n` of the products of the `getD`-extension by zero, for any `n`
bounding both lengths from above. -/
theorem dotZ_eq_sum_range_aux : ∀ (a b : List ℤ) (n : ℕ), a.length ≤ n → b.length ≤ n →
    dotZ a b = Finset.sum (Finset.range n) (fun i => a.getD i 0 * b.getD i 0) := by
  intro a
  induction a with
  | nil =>
    intro b n _ _
    simp [Submission.PTCert.dotZ]
  | cons x a' ih =>
    intro b n ha hb
    rcases n with _ | m
    · simp at ha
    · rcases b with _ | ⟨y, b'⟩
      · simp [Submission.PTCert.dotZ]
      · rw [Finset.sum_range_succ', dotZ_cons_cons]
        rw [ih b' m (by simp at ha; omega) (by simp at hb; omega)]
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        ring

theorem dotZ_eq_sum_range {a b : List ℤ} {n : ℕ} (ha : a.length ≤ n) (hb : b.length ≤ n) :
    Submission.PTCert.dotZ a b = Finset.sum (Finset.range n) (fun i => a.getD i 0 * b.getD i 0) :=
  dotZ_eq_sum_range_aux a b n ha hb

end Work.PTCert.ldlChainSound
