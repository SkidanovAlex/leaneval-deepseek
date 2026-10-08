import Mathlib
import Submission.Work.L2F.Props.OddSubDefs

/-!
# The characteristic polynomial of a semisimple element of `SL(2,F)` is separable

`Work.L2F.Props.SemisimpleSL m` (see `Props/OddSubDefs`) says that `m` is not a scalar matrix and
that its characteristic polynomial `X² - tr(m)·X + det(m)` has the "distinct eigenvalues"
property, phrased as `(tr m)² ≠ 4 det m` when `2 ≠ 0` and as `tr m ≠ 0` when `2 = 0`.

This file proves that the second conjunct alone already gives `m.charpoly.Separable`, i.e. that
the characteristic polynomial is coprime to its derivative.  The substantive input is the
elementary criterion for the polynomial `X² - t·X + d` over a field:

* if `2 ≠ 0` and `t² - 4d ≠ 0`, then the Bezout identity
  `4·(X² - tX + d) - (2X - t)² = 4d - t²` exhibits `X² - tX + d` as coprime to its derivative
  `2X - t` (multiply by the inverse of the nonzero constant `4d - t²`);
* if `2 = 0` and `t ≠ 0`, then the derivative of `X² - tX + d = X² + tX + d` is the nonzero
  constant `t`, so coprimality is immediate (Mathlib's
  `Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C`).

The characteristic-polynomial identity `m.charpoly = X² - tr(m)·X + det(m)` for `2 × 2` matrices
is `Matrix.charpoly_fin_two`.
-/

namespace Work.L2F.Props.oddsub

open Polynomial

/-- The quadratic `X² - t·X + d` over a field is separable provided either `2 ≠ 0` and its
discriminant `t² - 4d` is nonzero, or `2 = 0` and `t ≠ 0`.

In both cases the derivative `2X - t` is coprime to the polynomial: in the first case the
Bezout identity `4·(X² - tX + d) - (2X - t)² = 4d - t²` exhibits `4d - t²` as a nonzero
constant multiple of `1`, and in the second case `2 = 0` makes the derivative the nonzero
constant `t`. -/
theorem quadratic_separable {F : Type*} [Field F] (t d : F)
    (h : ((2 : F) ≠ 0 ∧ t ^ 2 - 4 * d ≠ 0) ∨ ((2 : F) = 0 ∧ t ≠ 0)) :
    (X ^ 2 - C t * X + C d : F[X]).Separable := by
  rcases h with ⟨h2, hd⟩ | ⟨h2, ht⟩
  · -- `2 ≠ 0`: use the Bezout identity coming from the discriminant.
    have hne : 4 * d - t ^ 2 ≠ 0 := by
      intro h0
      exact hd (by rw [show t ^ 2 - 4 * d = -(4 * d - t ^ 2) from by ring, h0, neg_zero])
    set k : F := (4 * d - t ^ 2)⁻¹ with hkdef
    have hkmul : k * (4 * d - t ^ 2) = 1 := by
      rw [hkdef]; exact inv_mul_cancel₀ hne
    have hder : derivative (X ^ 2 - C t * X + C d : F[X]) = (2 : F[X]) * X - C t := by
      simp only [derivative_sub, derivative_add, derivative_mul, derivative_X, derivative_C,
        derivative_pow]
      rw [C_eq_natCast]
      norm_num
    have hkey : (4 : F[X]) * (X ^ 2 - C t * X + C d)
        - ((2 : F[X]) * X - C t) * ((2 : F[X]) * X - C t) = C (4 * d - t ^ 2) := by
      have h1 : (4 : F[X]) * (X ^ 2 - C t * X + C d)
          - ((2 : F[X]) * X - C t) * ((2 : F[X]) * X - C t) = 4 * C d - C t * C t := by
        ring
      rw [h1, map_sub, map_mul, map_pow, pow_two]
      rw [C_ofNat]
    refine (separable_def' (X ^ 2 - C t * X + C d : F[X])).2
      ⟨C k * 4, -(C k) * ((2 : F[X]) * X - C t), ?_⟩
    rw [hder]
    calc C k * 4 * (X ^ 2 - C t * X + C d)
          + (-(C k) * ((2 : F[X]) * X - C t)) * ((2 : F[X]) * X - C t)
        = C k * ((4 : F[X]) * (X ^ 2 - C t * X + C d)
            - ((2 : F[X]) * X - C t) * ((2 : F[X]) * X - C t)) := by ring
      _ = C k * C (4 * d - t ^ 2) := by rw [hkey]
      _ = C (k * (4 * d - t ^ 2)) := by rw [← map_mul]
      _ = 1 := by rw [hkmul]; simp
  · -- `2 = 0`: the derivative is the nonzero constant `t`.
    have hcast : ((2 : ℕ) : F) = 0 := by rw [Nat.cast_ofNat]; exact h2
    have hunit : IsUnit (-t) := (isUnit_iff_ne_zero.mpr ht).neg
    have hsep := separable_C_mul_X_pow_add_C_mul_X_add_C (R := F) (a := (1 : F)) (b := -t)
      (c := d) (n := 2) hcast hunit
    simpa [C_1, C_neg, neg_mul, sub_eq_add_neg] using hsep

/-- The characteristic polynomial of a semisimple `2 × 2`-matrix (in the sense of
`Work.L2F.Props.SemisimpleSL`) is separable.

Only the "distinct eigenvalues" half of the definition of `SemisimpleSL` is used: the
characteristic polynomial is `X² - tr(m)·X + det(m)`, and `quadratic_separable` shows that it is
coprime to its derivative exactly under the corresponding discriminant / characteristic-two
conditions. -/
theorem charpoly_separable_of_semisimple (F : Type*) [Field F]
    (m : Matrix (Fin 2) (Fin 2) F) (h : Work.L2F.Props.SemisimpleSL m) :
    m.charpoly.Separable := by
  obtain ⟨-, hdisc⟩ := h
  rw [Matrix.charpoly_fin_two]
  exact quadratic_separable m.trace m.det hdisc

end Work.L2F.Props.oddsub
