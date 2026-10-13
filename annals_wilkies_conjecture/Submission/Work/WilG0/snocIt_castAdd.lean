import Mathlib
import Submission.Work.WilG0.Defs

namespace Work.WilG0

open WilkiesDesign

theorem snocIt_castAdd (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) (i : Fin n) :
    snocIt n m x w (Fin.castAdd m i) = x i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show snocIt n (m + 1) x w
          = Fin.snoc (snocIt n m x (Fin.init w)) (w (Fin.last m)) from rfl]
    rw [show (Fin.castAdd (m + 1) i : Fin (n + (m + 1))) = Fin.castSucc (Fin.castAdd m i)
          from rfl]
    rw [Fin.snoc_castSucc]
    exact ih (Fin.init w)

end Work.WilG0
