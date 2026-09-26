import Mathlib
import Submission.Work.PTCert.GlueDefs

namespace Work.PTCert

open Submission.PTCert

/-- `chiS` on `(ℤ/2)^m` is the cast of an integer product of signs, one factor per element
of `S`.  This reduces the real-valued character to an integer computation that `decide`
can evaluate by kernel reduction. -/
private lemma chiS_cast_int {m : ℕ} (S : Finset (Fin m)) (a : Fin m → ZMod 2) :
    chiS S a = ((∏ i ∈ S, (if a i = 0 then (1 : ℤ) else -1)) : ℝ) := by
  rw [chiS]
  push_cast
  rfl

/-- The five-bit character identity, checked by kernel reduction over the `32 × 32` index pairs. -/
private lemma chiSFive_int : ∀ S < 32, ∀ sc < 32,
    (∏ i ∈ maskSet (m := 5) S,
        (if zOfSc (m := 5) sc i = 0 then (1 : ℤ) else -1)) = chiS5 S sc := by
  decide

theorem chiSFive (S sc : ℕ) (hS : S < 32) (hsc : sc < 32) :
    Submission.PTCert.chiS (Submission.PTCert.maskSet (m := 5) S) (Submission.PTCert.zOfSc (m := 5) sc)
      = (Submission.PTCert.chiS5 S sc : ℝ) := by
  rw [chiS_cast_int]
  exact_mod_cast chiSFive_int S hS sc hsc

end Work.PTCert
