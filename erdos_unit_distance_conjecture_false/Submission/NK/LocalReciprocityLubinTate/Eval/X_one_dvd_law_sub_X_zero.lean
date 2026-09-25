import Mathlib

/-!
# `F(X,Y) - X` is divisible by `Y` for a formal group law

For a one-dimensional formal group law `F` over a commutative ring `R` the associativity
axiom forces `F(X, 0) = X` (`FormalGroup.Xzero_eq_X`, `FormalGroup.add_zero`), and hence
`F(X, Y) - X` is divisible by `Y`.

The divisibility is verified through the coefficient criterion
`MvPowerSeries.X_dvd_iff`: a series is divisible by `X 1` exactly when all of its
coefficients at monomials in which the second variable does not occur vanish.  The
supporting computation is `coeff_subst_X_zero` below: substituting `0` for `X 1`
(`![X 0, 0]`) does not change those coefficients, so `FormalGroup.add_zero`
(`F(X, 0) = X`) computes them for the group law `F`.
-/

namespace NK.LocalReciprocityLubinTate.Eval

open MvPowerSeries

/-- Substituting `![X 0, 0]` into a two-variable formal power series `f` does not change
the coefficients of `f` at monomials in which the second variable does not occur.

In other words, the coefficient of `X 0 ^ n` in "`f(X, 0)`" is the coefficient of
`X 0 ^ n` in `f`. -/
theorem coeff_subst_X_zero {R : Type*} [CommRing R] (f : MvPowerSeries (Fin 2) R) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (MvPowerSeries.subst
          ![MvPowerSeries.X (0 : Fin 2), (0 : MvPowerSeries (Fin 2) R)] f) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n) f := by
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.HasSubst.X_zero) f
    (Finsupp.single (0 : Fin 2) n)]
  rw [finsum_eq_single _ (Finsupp.single (0 : Fin 2) n)]
  · -- the single contributing monomial `d = single 0 n`
    rw [Finsupp.prod_single_index (by simp), Matrix.cons_val_zero, MvPowerSeries.X_pow_eq]
    simp [smul_eq_mul]
  · -- every other monomial `d` contributes `0`
    intro d hd
    by_cases hd1 : d 1 = 0
    · -- `d` involves only the variable `X 0`, so `d = single 0 (d 0)`
      have hd' : d = Finsupp.single (0 : Fin 2) (d 0) := by
        ext i
        fin_cases i <;> simp [hd1]
      rw [hd', Finsupp.prod_single_index (by simp), Matrix.cons_val_zero,
        MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg]
      · simp
      · intro h
        exact hd (hd'.trans h.symm)
    · -- `d` contains a positive power of `X 1`, which is sent to `0`
      rw [Finsupp.prod, Finset.prod_eq_zero (by simpa [Finsupp.mem_support_iff] using hd1)
        (by simp [Matrix.cons_val_one, hd1])]
      simp

theorem X_one_dvd_law_sub_X_zero {R : Type*} [CommRing R] (G : FormalGroup R) :
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ∣
      ((G : MvPowerSeries (Fin 2) R) - MvPowerSeries.X 0) := by
  rw [MvPowerSeries.X_dvd_iff]
  intro m hm
  -- a monomial not involving `X 1` is a pure power of `X 0`
  have hm' : m = Finsupp.single (0 : Fin 2) (m 0) := by
    ext i
    fin_cases i <;> simp [hm]
  rw [hm']
  -- `F(X, 0) = X` computes these coefficients for the group law
  have hcoeff : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) (m 0))
        (G : MvPowerSeries (Fin 2) R) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) (m 0)) (MvPowerSeries.X (0 : Fin 2)) := by
    have hadd : (G : MvPowerSeries (Fin 2) R).subst
        ![MvPowerSeries.X (0 : Fin 2), (0 : MvPowerSeries (Fin 2) R)] =
        MvPowerSeries.X (0 : Fin 2) :=
      FormalGroup.add_zero G (PowerSeries.HasSubst.X (0 : Fin 2))
    exact (coeff_subst_X_zero (G : MvPowerSeries (Fin 2) R) (m 0)).symm.trans
      (congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) (m 0))) hadd)
  rw [map_sub, hcoeff, sub_self]

end NK.LocalReciprocityLubinTate.Eval
