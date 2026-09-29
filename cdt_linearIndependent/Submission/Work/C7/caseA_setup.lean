import Mathlib
import Submission.Work.C7.seven_setup

/-!
# Area C7 — setup for the "case A" endgame (`Work.C7.caseA_end`)

With the derivation `∂ = x(x-1)²·d/dx` (`Work.C7.dsh`), the five functions
`f5 0 = 1`, `f5 1 = L = log(1-x)`, `f5 2 = L²`, `f5 3 = Li₂(x)`, `f5 4 = J(x)`, and the primitive
`g 6` whose `∂`-derivative is known (`hd6`), a relation
`d·(g 6) + Σⱼ Cⱼ·f5ⱼ = 0` with `d ≠ 0` cannot hold.

The elimination step: applying `∂` to the relation, multiplying by `d` and replacing `d·(g 6)`
by `-Σⱼ Cⱼ f5ⱼ` produces a relation `Σⱼ (Bv d C)ⱼ·f5ⱼ = 0` with **polynomial** coefficients, to
which `PolyIndependent f5` applies.  The coefficient of `Li₂ = f5 3` is the polynomial

  `(Bv d C) 3 = -(∂d)·(C 3) + d·(∂(C 3)) + 2·d²·x(x-2)²`,

and in `ℚ(x)` it reads `x(x-1)²·(d·(C 3)' - d'·(C 3)) + 2·d²(x-2)² = 0`, i.e.
`(C 3/d)' = -2(x-2)²/(x-1)²`, contradicting `Work.C7.rat_ode2`.
-/

noncomputable section

namespace Work.C7

open PowerSeries
open scoped BigOperators

/-! ## `∂` of the five basis functions, in `f5`-form -/

@[simp] lemma dsh_f5_zero : dsh (f5 0) = (0 : PowerSeries ℚ) := by simp [f5]

@[simp] lemma dsh_f5_one : dsh (f5 1) = PowerSeries.X * (PowerSeries.X - 1) := by
  simpa using dsh_Lps

@[simp] lemma dsh_f5_two : dsh (f5 2) = 2 * PowerSeries.X * (PowerSeries.X - 1) * Lps := by
  simpa using dsh_Lps_sq

@[simp] lemma dsh_f5_three : dsh (f5 3)
    = -((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2 * Lps := by
  simpa using dsh_Li2ps

/-! ## The derived coefficient vector -/

/-- The polynomial-coefficient vector obtained by applying `∂` to a relation
`d·(g 6) + Σⱼ Cⱼ·f5ⱼ = 0`, multiplying by `d` and eliminating `g 6` (`d·g 6 = -Σⱼ Cⱼ f5ⱼ`).
See `Work.C7.Bv_three` for the coefficient of `Li₂`. -/
def Bv (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) : Fin 5 → Polynomial ℚ :=
  ![ -(dshP d) * (C 0) + d * (dshP (C 0) + (C 1) * (Polynomial.X * (Polynomial.X - 1))),
     -(dshP d) * (C 1) + d * (dshP (C 1) + (C 2) * (2 * Polynomial.X * (Polynomial.X - 1))
        - (C 3) * ((Polynomial.X - 1) ^ 2) - (C 4) * ((Polynomial.X - 1) ^ 2)),
     -(dshP d) * (C 2) + d * (dshP (C 2))
        + (1 / 2) * d ^ 2 * Polynomial.X * (Polynomial.X - 2) ^ 2,
     -(dshP d) * (C 3) + d * (dshP (C 3)) + 2 * d ^ 2 * Polynomial.X * (Polynomial.X - 2) ^ 2,
     -(dshP d) * (C 4) + d * (dshP (C 4))
        + d * (C 4) * ((1 / 2) * Polynomial.X * (Polynomial.X - 1)) ]

@[simp] lemma Bv_zero (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) :
    Bv d C 0 = -(dshP d) * (C 0) + d * (dshP (C 0) + (C 1) * (Polynomial.X * (Polynomial.X - 1))) :=
  rfl

@[simp] lemma Bv_one (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) :
    Bv d C 1 = -(dshP d) * (C 1) + d * (dshP (C 1)
        + (C 2) * (2 * Polynomial.X * (Polynomial.X - 1))
        - (C 3) * ((Polynomial.X - 1) ^ 2) - (C 4) * ((Polynomial.X - 1) ^ 2)) :=
  rfl

@[simp] lemma Bv_two (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) :
    Bv d C 2 = -(dshP d) * (C 2) + d * (dshP (C 2))
        + (1 / 2) * d ^ 2 * Polynomial.X * (Polynomial.X - 2) ^ 2 :=
  rfl

@[simp] lemma Bv_three (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) :
    Bv d C 3 = -(dshP d) * (C 3) + d * (dshP (C 3))
        + 2 * d ^ 2 * Polynomial.X * (Polynomial.X - 2) ^ 2 :=
  rfl

@[simp] lemma Bv_four (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) :
    Bv d C 4 = -(dshP d) * (C 4) + d * (dshP (C 4))
        + d * (C 4) * ((1 / 2) * Polynomial.X * (Polynomial.X - 1)) :=
  rfl

/-- The `Li₂`-coefficient of the derived relation, in factored form: it is
`x·((x-1)²·(d·(C 3)' - d'·(C 3)) + 2d²(x-2)²)`. -/
lemma Bv_three_factored (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) :
    Bv d C 3 = Polynomial.X * ((Polynomial.X - 1) ^ 2 *
      ((C 3).derivative * d - (C 3) * d.derivative)
      + 2 * d ^ 2 * (Polynomial.X - 2) ^ 2) := by
  simp only [Bv_three, dshP]
  ring

end Work.C7
