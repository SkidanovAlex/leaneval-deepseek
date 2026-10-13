import Mathlib
import Submission.Work.WilE9G.Assembly.Defs

namespace Work.WilE9G.Assembly

/-- `lagPoint` agrees with `z` on the base coordinates, hence has the same `stratProj`. -/
theorem stratProj_lagPoint {n m j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ) :
    Work.WilE9.Sharp.stratProj (m := m + j + 1) (Work.WilE9G.lagPoint z mu mu0)
      = Work.WilE9.Sharp.stratProj (m := m) z := by
  funext i
  -- Unfold `stratProj` and `lagPoint` at the coordinate `i : Fin (n + 1)`.
  simp only [Work.WilE9.Sharp.stratProj, Work.WilE9G.lagPoint, finCongr_apply]
  -- Both `Fin.cast … (stratInj …)` and `Fin.castAdd (j+1) (stratInj …)` are value-preserving,
  -- so the argument of `Fin.append` is a left (base) coordinate.
  have hkey : ∀ (e : n + (1 + (m + j + 1)) = n + (1 + m) + (j + 1)),
      Fin.cast e (Work.WilE9.Sharp.stratInj (Fin.castAdd (m + j + 1) i))
        = Fin.castAdd (j + 1) (Work.WilE9.Sharp.stratInj (Fin.castAdd m i)) :=
    fun e => Fin.ext (by simp [Work.WilE9.Sharp.stratInj])
  rw [hkey]
  rw [Fin.append_left]

end Work.WilE9G.Assembly
