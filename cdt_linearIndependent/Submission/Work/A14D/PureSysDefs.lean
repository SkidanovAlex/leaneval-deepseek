import Mathlib
import Submission.Work.A14.defs
import Submission.Work.Pure.pure_facts
import Submission.Work.CPull.defs

/-!
# Area A14D — shared definitions for the pure-system identity on the disc

`pure_sys_disc` is the substitution-evaluated form of the `D`-closure of the seven pure
functions `B₁,…,B₇` (`Submission.CDTPlan.pureB`, `Work.Pure.dclosed`) along the symmetrisation
coordinate `y = x²/(x−1)`.

This file collects the series-level objects appearing in the statement and in its proof:

* `PolyGrowth f` — polynomial growth of the coefficients of `f` (so that `evp f z` converges
  for `‖z‖ < 1`);
* `Sk k` — the substituted series `B_k ∘ y` (`Submission.CDTPlan.pureB k |>.subst sympY`),
  i.e. `Work.C7.g k`;
* `DQ`, `DA k m` — the substitution of the `D`-closure polynomials `Work.Pure.dq`,
  `Work.Pure.dA k m` along `y`;
* `SYd` — the derivative of the symmetrisation coordinate `y`.
-/

open scoped BigOperators

namespace Work.A14D

/-- Polynomial growth of the coefficients of a rational power series: `‖[Xⁿ]f‖ ≤ C·(n+1)^k`.
This is exactly the condition under which `Work.CPull.evp f z = Σₙ [Xⁿ]f · zⁿ` converges (and is
holomorphic) on the open unit disc, and under which `evp` is multiplicative and commutes with
`d/dX` (see `Work.A14D.summable_abs_coeff_of_poly_growth`, `Work.A14D.evp_deriv`). -/
def PolyGrowth (f : PowerSeries ℚ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ,
    ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k

/-- The substituted pure series `B_k ∘ y`, `y = x²/(x−1)`. -/
noncomputable def Sk (k : Fin 7) : PowerSeries ℚ :=
  (Submission.CDTPlan.pureB k).subst Submission.CDT.sympY

/-- `dq` substituted along the symmetrisation coordinate `y`. -/
noncomputable def DQ : PowerSeries ℚ :=
  (Work.Pure.dq : PowerSeries ℚ).subst Submission.CDT.sympY

/-- `dA k m` substituted along the symmetrisation coordinate `y`. -/
noncomputable def DA (k m : Fin 7) : PowerSeries ℚ :=
  (Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY

/-- The derivative of the symmetrisation coordinate `y = x²/(x−1)`. -/
noncomputable def SYd : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) Submission.CDT.sympY

end Work.A14D
