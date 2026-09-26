import Mathlib
import Submission.Work.PTCert.ApplyLetter
import Submission.Work.PTCert.LetterEval

namespace Work.PTCert

open Submission.PTCert

/-- The product of letters splits off its first factor. -/
theorem lprodProdImg_lprod_cons (r : ℕ) (k : ℕ) (ks : List ℕ) :
    Submission.PTCert.lprod r (k :: ks) = Submission.PTCert.b1 r k * Submission.PTCert.lprod r ks := by
  simp [Submission.PTCert.lprod]

/-- The image word construction unfolds one step. -/
theorem lprodProdImg_prodImg_cons (r : ℕ) (k : ℕ) (ks : List ℕ) (i : ℕ) :
    Submission.PTCert.prodImg r (k :: ks) i
      = Submission.PTCert.applyLetter r k (Submission.PTCert.prodImg r ks i) := by
  simp [Submission.PTCert.prodImg]

theorem lprodProdImg (r : ℕ) (ks : List ℕ) (hks : ∀ k ∈ ks, k < Submission.PTCert.NB1 r)
    (i : Fin r) :
    (Submission.PTCert.lprod r ks) (FreeGroup.of i)
      = Submission.PTCert.evalW (r := r) (Submission.PTCert.prodImg r ks i.val) := by
  induction ks with
  | nil => simp [Submission.PTCert.lprod, Submission.PTCert.prodImg, evalW_single]
  | cons k ks' ih =>
    rw [lprodProdImg_lprod_cons, lprodProdImg_prodImg_cons, MulAut.mul_apply]
    rw [ih (fun j hj => hks j (List.mem_cons_of_mem k hj))]
    rw [Submission.PTCert.applyLetterSound r k (hks k List.mem_cons_self)]

end Work.PTCert
