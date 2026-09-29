import Mathlib
import Submission.Work.Holonomy3.comp_defs

/-!
# `embedVarC s f` is the one-variable lift `PowerSeries.toMvPowerSeries s f`

The definition `Work.Holonomy3.embedVarC` (in `comp_defs`) views a univariate power series `f`
as a multivariate power series in the variable `x_s` alone, by hand:
`embedVarC s f n = if n = Finsupp.single s (n s) then coeff (n s) f else 0`.

Mathlib's `PowerSeries.toMvPowerSeries s` is the same operation, obtained as the algebra map
`PowerSeries ℂ →ₐ[ℂ] MvPowerSeries (Fin d) ℂ` sending the single variable to `X_s`.  The two
coincide, which is what this file records; it lets us use the whole Mathlib API
(`toMvPowerSeries_C`, `toMvPowerSeries_X`, `toMvPowerSeries_injective`, ...) for `embedVarC`.

The proof goes through Mathlib's own normal form for `toMvPowerSeries` as a *substitution*,
`PowerSeries.toMvPowerSeries_eq_subst : f.toMvPowerSeries i = f.subst (X i)`, together with the
coefficient formula for substitution, `PowerSeries.coeff_subst`, and the coefficient of a monomial
`MvPowerSeries.coeff_X_pow`.
-/

namespace Work.Holonomy3

open MvPowerSeries

noncomputable section

/-- The coefficient of the one-variable lift `PowerSeries.toMvPowerSeries s f` at an exponent
`n : Fin d →₀ ℕ`: it is `coeff (n s) f` if `n` is supported only at `s`, and `0` otherwise.  This
is exactly the defining formula of `embedVarC`. -/
lemma coeff_toMvPowerSeries {d : ℕ} (s : Fin d) (h : PowerSeries ℂ) (n : Fin d →₀ ℕ) :
    MvPowerSeries.coeff n (PowerSeries.toMvPowerSeries s h) =
      if n = Finsupp.single s (n s) then PowerSeries.coeff (n s) h else 0 := by
  rw [PowerSeries.toMvPowerSeries_eq_subst,
    PowerSeries.coeff_subst (PowerSeries.HasSubst.X s)]
  simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul]
  by_cases hn : n = Finsupp.single s (n s)
  · -- `n` is supported at `s` (`n = single s (n s)`): only the term `e = n s` survives
    rw [if_pos hn]
    rw [finsum_eq_single
      (fun e => PowerSeries.coeff e h * (if n = Finsupp.single s e then 1 else 0)) (n s)]
    · rw [if_pos hn, mul_one]
    · intro x hx
      have hx' : n ≠ Finsupp.single s x := by
        intro hh
        refine hx ?_
        calc x = (Finsupp.single s x) s := Finsupp.single_eq_same.symm
          _ = n s := by rw [← hh]
      rw [if_neg hx', mul_zero]
  · -- some variable other than `s` occurs in `n`: every term vanishes
    rw [if_neg hn]
    have hzero : (fun e : ℕ => PowerSeries.coeff e h * (if n = Finsupp.single s e then 1 else 0))
        = fun _ => (0 : ℂ) := by
      funext e
      have : n ≠ Finsupp.single s e := fun hh => hn (by rw [hh, Finsupp.single_eq_same])
      rw [if_neg this, mul_zero]
    rw [hzero, finsum_zero]

theorem embedVarC_eq_liftV {d : ℕ} (s : Fin d) (h : PowerSeries ℂ) :
    embedVarC s h = PowerSeries.toMvPowerSeries s h := by
  funext n
  exact (coeff_toMvPowerSeries s h n).symm

end

end Work.Holonomy3
