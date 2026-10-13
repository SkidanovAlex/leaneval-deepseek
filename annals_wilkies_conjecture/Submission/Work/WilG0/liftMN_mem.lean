import Mathlib
import Submission.Work.WilG0.Defs

namespace Work.WilG0

/-- Prepending one free coordinate to `liftMN n m A` is `liftMN (n+1) m A`: the new
coordinate is at index `0` and the old vector is `Fin.tail z`.  This is exactly the shape
produced by the axiom `SOMin.prod_left`. -/
theorem liftMN_succ (n m : ℕ) (A : Set (Fin m → ℝ)) :
    liftMN (n+1) m A = {z : Fin (m + n + 1) → ℝ | Fin.tail z ∈ liftMN n m A} := by
  ext z
  show (fun j : Fin m => z (j.addNat (n+1))) ∈ A ↔
      (fun j : Fin m => Fin.tail z (j.addNat n)) ∈ A
  have hfun : (fun j : Fin m => z (j.addNat (n+1))) =
      (fun j : Fin m => Fin.tail z (j.addNat n)) := by
    funext j
    show z (j.addNat (n+1)) = z ((j.addNat n).succ)
    rw [show (j.addNat (n+1) : Fin (m + n + 1)) = (j.addNat n).succ from by
      apply Fin.ext; rw [Fin.val_addNat, Fin.val_succ, Fin.val_addNat]; omega]
  rw [hfun]

/-- `liftMN n m A` keeps `A` in the last `m` coordinates and frees the first `n`; each of the
`n` free coordinates costs one format by `SOMin.prod_left`, and the degree is unchanged. -/
theorem liftMN_mem {S : WilkiesDesign.SOMin} {m F D : ℕ} {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m) (n : ℕ) :
    liftMN n m A ∈ S.Ω (F + n) D (m + n) := by
  induction n with
  | zero =>
    have h0 : liftMN 0 m A = A := by
      ext z
      show (fun j : Fin m => z (j.addNat 0)) ∈ A ↔ z ∈ A
      have : (fun j : Fin m => z (j.addNat 0)) = z := by
        funext j; exact congrArg z (Fin.addNat_zero m j)
      rw [this]
    rw [h0]
    exact hA
  | succ n ih =>
    rw [liftMN_succ n m A]
    exact S.prod_left ih

end Work.WilG0
