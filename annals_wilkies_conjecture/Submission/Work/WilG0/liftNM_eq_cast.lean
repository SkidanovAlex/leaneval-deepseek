import Mathlib
import Submission.Work.WilG0.Defs

namespace Work.WilG0

/-- Transporting a set of functions on `Fin a` along an equality `h : a = b` of the index
type reindexes the coordinates by the bijection `Fin.cast h`. -/
theorem cast_fin_set {a b : ℕ} (h : a = b) (S : Set (Fin a → ℝ)) :
    (h ▸ S : Set (Fin b → ℝ)) = {z : Fin b → ℝ | z ∘ Fin.cast h ∈ S} := by
  cases h
  ext z
  simp

/-- `liftNM` is `liftMN` transported across `Nat.add_comm m n`: the two glueing orders differ
only by the permutation of the index set. -/
theorem liftNM_eq_cast (n m : ℕ) (A : Set (Fin m → ℝ)) :
    liftNM n m A = (Nat.add_comm m n) ▸ liftMN n m A := by
  rw [cast_fin_set (Nat.add_comm m n) (liftMN n m A)]
  ext z
  simp only [liftNM, liftMN, Set.mem_ofPred_eq, Function.comp_apply]
  rw [show (fun j : Fin m => z (Fin.cast (Nat.add_comm m n) (Fin.addNat j n)))
        = (fun j : Fin m => z (Fin.natAdd n j)) from by
    funext j
    rw [show Fin.cast (Nat.add_comm m n) (Fin.addNat j n) = Fin.natAdd n j from by
      ext
      simp [Fin.cast, Fin.natAdd, Fin.addNat]
      omega]]

end Work.WilG0
