import Mathlib

namespace Work.LinnikAreas.FarRepel

/-- The abscissa of absolute convergence of the Dirichlet series `∑ Λ(n) n^{-s}` is at most `1`. -/
theorem abscissaVonMangoldtLeOne :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := by
  -- The abscissa is the infimum of the real parts where the series converges absolutely;
  -- it suffices to exhibit absolute convergence at every real `y > 1`.
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy => ?_
  -- `∑ Λ(n) n^{-y}` converges absolutely for `y > 1` (Mathlib: `LSeriesSummable_vonMangoldt`).
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (y : ℂ)) (by simpa using hy)

end Work.LinnikAreas.FarRepel
