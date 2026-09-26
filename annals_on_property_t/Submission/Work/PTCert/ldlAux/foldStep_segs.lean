import Mathlib
import Submission.Work.PTCert.ldlAux

namespace Work.PTCert.ldlAux

open Submission.PTCert (foldStep)

/-- Generalisation of `foldStep_segs` where the accumulator index starts at `n`
instead of `0`. -/
theorem foldStep_segs_aux (g : ℕ → List (List ℤ) → Option (List (List ℤ))) :
    ∀ (segs : List (List ℕ)) (n : ℕ) (accs : ℕ → List (List ℤ)),
      (∀ j < segs.length, foldStep g (segs.getD j []) (accs (n + j)) = some (accs (n + j + 1))) →
      foldStep g segs.flatten (accs n) = some (accs (n + segs.length)) := by
  intro segs
  induction segs with
  | nil => intro n accs _; simp
  | cons s rest ih =>
    intro n accs h
    rw [List.flatten_cons, Submission.PTCert.foldStep_append]
    have h0 : foldStep g s (accs n) = some (accs (n + 1)) := by
      have := h 0 (by simp); simpa using this
    rw [h0, Option.bind_some]
    have htail : ∀ j < rest.length,
        foldStep g (rest.getD j []) (accs ((n + 1) + j)) = some (accs ((n + 1) + j + 1)) := by
      intro j hj
      have := h (j + 1) (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1) accs htail

theorem foldStep_segs (g : ℕ → List (List ℤ) → Option (List (List ℤ))) (segs : List (List ℕ))
    (accs : ℕ → List (List ℤ))
    (h : ∀ j < segs.length, Submission.PTCert.foldStep g (segs.getD j []) (accs j) = some (accs (j + 1))) :
    Submission.PTCert.foldStep g segs.flatten (accs 0) = some (accs segs.length) := by
  simpa using foldStep_segs_aux g segs 0 accs (by simpa using h)

end Work.PTCert.ldlAux
