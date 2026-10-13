import Mathlib
import Submission.Work.WilG0.Defs

namespace Work.WilG0

/-- `snocIt n m x w` agrees with `w` on the last `m` coordinates: at the index
`Fin.natAdd n j` (i.e. coordinate `n + j`) it returns `w j`. -/
theorem snocIt_natAdd (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) (j : Fin m) :
    snocIt n m x w (Fin.natAdd n j) = w j := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    refine Fin.lastCases ?_ ?_ j
    · change Fin.snoc (α := fun _ => ℝ) (snocIt n m x (Fin.init w)) (w (Fin.last m))
        (Fin.natAdd n (Fin.last m)) = w (Fin.last m)
      rw [show Fin.natAdd n (Fin.last m) = Fin.last (n + m) from Fin.ext rfl, Fin.snoc_last]
    · intro i
      change Fin.snoc (α := fun _ => ℝ) (snocIt n m x (Fin.init w)) (w (Fin.last m))
        (Fin.natAdd n (Fin.castSucc i)) = w (Fin.castSucc i)
      rw [show Fin.natAdd n (Fin.castSucc i) = Fin.castSucc (Fin.natAdd n i) from Fin.ext rfl,
        Fin.snoc_castSucc]
      exact ih (Fin.init w) i

end Work.WilG0
