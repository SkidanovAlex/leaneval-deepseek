import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.Holonomy3.comp_defs

/-!
# Vocabulary for the cleared-composite Taylor expansion (`Work.Holonomy3.taylor_cleared_comp`)

The analytic step (STEP 3) of the fine holonomy bound compares two multivariable power series:

* the coefficients of `uPoly P * diagComp Φ (auxSeriesC f Q)`, i.e. of the *composition* of the
  auxiliary series with the univariate series `Φ_s` of the maps `ψ_s`, multiplied by the
  pole-clearing polynomial `∏_s ∏_i P_{i,s}(z_s)` (in the *source* variable of the pullback);
* the Taylor coefficients of the explicit *holomorphic* expansion of the cleared composite
  `clearedFun Q ψ N P`, which uses the numerators `N i s` (whose Taylor series we call
  `ν i s`) and the same polynomials `P i s` (now evaluated at the pullback variable `z s`).

This file fixes the (small) vocabulary of that comparison, all of it built on the Mathlib
composition API `PowerSeries.subst` / `MvPowerSeries.subst`:

* `toC`/`toCQ` — the `ℂ`-versions of the `ℚ`-data `f`, `Q`;
* `poleV P s` — the `s`-th pole-clearing polynomial `∏_i P i s`, as a power series;
* `liftV s h` — the univariate series `h` viewed as a series in the single variable `s`
  (this is `PowerSeries.toMvPowerSeries s`; it coincides with `embedVarC s h`);
* `substFam Φ` — the family `s ↦ Φ_s(x_s)` used as the substitution family for `MvPowerSeries.subst`;
* `clearedFactor ν P i s` — the `s`-th factor of the `i`-th species of the cleared composite,
  `ν (i s) s · ∏_{i' ≠ i s} P i' s`;
* `clearedSeries Φ ν P Q` — the explicit expansion of the cleared composite, a finite sum over
  species vectors `i` of a polynomial part (`Q i` with `Φ_s` substituted) times, for each variable
  `s`, the product of the `clearedFactor`.

The two series are identified in `Work.Holonomy3.taylor_cleared_comp`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

noncomputable section

variable {m d : ℕ}

/-- The `ℂ`-version of a species `f : PowerSeries ℚ`. -/
def toC (f : PowerSeries ℚ) : PowerSeries ℂ := PowerSeries.map (algebraMap ℚ ℂ) f

/-- The `ℂ`-version of a template `Q`. -/
def toCQ (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) (i : Fin d → Fin m) :
    MvPolynomial (Fin d) ℂ := MvPolynomial.map (algebraMap ℚ ℂ) (Q i)

/-- The pole-clearing polynomial `R s = ∏_i P i s` of the `s`-th variable, as a power series. -/
def poleV (P : Fin m → Fin d → Polynomial ℂ) (s : Fin d) : PowerSeries ℂ :=
  ∏ i, ((P i s : Polynomial ℂ) : PowerSeries ℂ)

/-- The univariate series `h` viewed as a multivariate series depending only on the variable `s`. -/
def liftV (s : Fin d) (h : PowerSeries ℂ) : MvPowerSeries (Fin d) ℂ :=
  PowerSeries.toMvPowerSeries s h

/-- The substitution family `s ↦ Φ_s(x_s)` used for `MvPowerSeries.subst`. -/
def substFam (Φ : Fin d → PowerSeries ℂ) : Fin d → MvPowerSeries (Fin d) ℂ :=
  fun s => liftV s (Φ s)

/-- The `s`-th factor of the `i`-th species of the cleared composite:
`ν (i s) s · ∏_{i' ≠ i s} P i' s`. -/
def clearedFactor (ν : Fin m → Fin d → PowerSeries ℂ) (P : Fin m → Fin d → Polynomial ℂ)
    (i : Fin d → Fin m) (s : Fin d) : PowerSeries ℂ :=
  ν (i s) s * ∏ i' ∈ Finset.univ.erase (i s), ((P i' s : Polynomial ℂ) : PowerSeries ℂ)

/-- The explicit expansion of the cleared composite: a finite sum over species vectors of the
template (`Q i` with `Φ` substituted) times the product over `s` of `clearedFactor`. -/
def clearedSeries (Φ : Fin d → PowerSeries ℂ) (ν : Fin m → Fin d → PowerSeries ℂ)
    (P : Fin m → Fin d → Polynomial ℂ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ) :
    MvPowerSeries (Fin d) ℂ :=
  ∑ i, (MvPolynomial.aeval (substFam Φ) (Q i)) * ∏ s, liftV s (clearedFactor ν P i s)

end

end Work.Holonomy3
