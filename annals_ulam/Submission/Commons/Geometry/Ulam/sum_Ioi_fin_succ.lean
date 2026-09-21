import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace Commons.Geometry.Ulam

lemma sum_Ioi_fin_succ {d : ℕ} [NeZero d] (g : Fin d → ℝ) :
    (∑ i > (0 : Fin d), g i) =
      ∑ j : Fin (d - 1), g (Fin.cast (show (d - 1) + 1 = d by
        have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d); omega) j.succ)  := by
  let h : (d - 1) + 1 = d := by
    have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    omega
  simpa [h] using (Fin.sum_Ioi_cast h g (0 : Fin ((d - 1) + 1))).trans
    (Fin.sum_Ioi_zero (fun i : Fin ((d - 1) + 1) => g (Fin.cast h i)))

end Commons.Geometry.Ulam