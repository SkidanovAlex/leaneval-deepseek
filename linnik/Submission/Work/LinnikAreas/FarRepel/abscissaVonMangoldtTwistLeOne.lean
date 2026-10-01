import Mathlib

namespace Work.LinnikAreas.FarRepel

open LSeries

/-- The abscissa of absolute convergence of the twisted Dirichlet series `∑ Λ(n) χ(n) n^{-s}` is
at most `1`. -/
theorem abscissaVonMangoldtTwistLeOne {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ)) ≤ 1 := by
  -- It suffices to prove summability at every real point `y > 1`.
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  -- Mathlib knows the twist of `Λ` by `χ` is summable for `re s > 1`.
  have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := (y : ℂ))
    (by simpa using hy)
  -- The two coefficient sequences differ only by the order of the product.
  exact (LSeriesSummable_congr (↑y)
    (f := fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ))
    (g := ((fun n : ℕ => (χ (n : ZMod q) : ℂ)) *
      fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))
    (fun {n} _ => by simp [Pi.mul_apply, mul_comm])).mpr h

end Work.LinnikAreas.FarRepel
