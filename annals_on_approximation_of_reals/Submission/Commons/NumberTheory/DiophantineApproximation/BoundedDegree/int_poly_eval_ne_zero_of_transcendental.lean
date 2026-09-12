import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.Algebraic.Defs

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial

/-- Evaluating a nonzero integer polynomial at a real transcendental number gives a nonzero
real number: converting integer coefficients to real ones and evaluating is the same as
converting them to rational coefficients first. -/
private lemma int_poly_map_eq_rat_map_real (P : Polynomial ℤ) :
    P.map (Int.castRingHom ℝ) = (P.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) := by
  rw [Polynomial.map_map]
  apply congrArg (fun f : ℤ →+* ℝ => Polynomial.map f P)
  ext n
  rfl

theorem int_poly_eval_ne_zero_of_transcendental (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (P : Polynomial ℤ) (hP : P ≠ 0) :
    Polynomial.eval ξ (P.map (Int.castRingHom ℝ)) ≠ 0 := by
  intro hzero
  let Q : Polynomial ℚ := P.map (Int.castRingHom ℚ)
  have hQzero : aeval ξ Q = 0 := by
    dsimp [Q]
    rw [← eval_map_algebraMap]
    rw [Polynomial.map_map]
    rw [show (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ from by
      ext n
      rfl]
    exact hzero
  have hQ : Q = 0 := (transcendental_iff.mp hξ) Q hQzero
  have hPzero : P = 0 := by
    have hQ' : P.map (Int.castRingHom ℚ) = 0 := by
      simpa [Q] using hQ
    exact (Polynomial.map_eq_zero_iff (f := Int.castRingHom ℚ) Int.cast_injective).mp hQ'
  exact hP hPzero

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree