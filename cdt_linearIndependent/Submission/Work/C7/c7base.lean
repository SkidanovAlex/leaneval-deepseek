import Mathlib
import Submission.Work.C7.xdefs

/-!
# Area C7 — the `x`-side of the independence of `1, L, L², Li₂, J`

Shared definitions for the proof that the five power series
`1, L = log(1-x), L², Li₂(x), J = x·₃F₂(1/2,1,1;3/2,3/2; y/4)` (`y = x²/(x-1)`) are
`ℚ[x]`-linearly independent.

They satisfy the first order relations

* `L' = 1/(x-1)`,  `Li₂' = -L/x`,  `(L²)' = 2L·L'`
* `2x(x-1)·J' - x·J = 2(1-x)·L`  (the ODE `hJ`, obtained from the order two ODE of `B₅∘y`).

Consequently the operator `θ = 2x(x-1)·d/dx` acts on the `ℚ(x)`-span of the five series with
*polynomial* coefficients: on a relation `Σ Pᵢ·fᵢ = 0` with `Pᵢ ∈ ℚ[x]` it produces the new
relation `Σ (thetaP P)ᵢ·fᵢ = 0` whose coefficients `thetaP P` are again polynomials (the factor
`2x(x-1)` clears the denominators `1/(x-1)` and `1/x`).
-/

noncomputable section

namespace Work.C7

open PowerSeries

/-- The four functions `1, L, L², Li₂` (the `D`-closed span whose independence is the hypothesis
`h4`). -/
def F4 : Fin 4 → PowerSeries ℚ := fun i => ![1, Lps, Lps ^ 2, Li2ps] i

/-- The five functions `1, L, L², Li₂, J`. -/
def F5 : Fin 5 → PowerSeries ℚ := fun i => ![1, Lps, Lps ^ 2, Li2ps, Jps] i

lemma F5_zero : F5 0 = (1 : PowerSeries ℚ) := rfl
lemma F5_one : F5 1 = Lps := rfl
lemma F5_two : F5 2 = Lps ^ 2 := rfl
lemma F5_three : F5 3 = Li2ps := rfl
lemma F5_four : F5 4 = Jps := rfl

/-- `((2 : ℚ[X]) : ℚ⟦X⟧) = 2` (the numeral coercions are not `simp`-normal by default). -/
lemma poly_coe_two : ((2 : Polynomial ℚ) : PowerSeries ℚ) = (2 : PowerSeries ℚ) := by
  rw [show (2 : Polynomial ℚ) = Polynomial.C (2 : ℚ) from rfl, Polynomial.coe_C, map_ofNat]

/-- `((4 : ℚ[X]) : ℚ⟦X⟧) = 4`. -/
lemma poly_coe_four : ((4 : Polynomial ℚ) : PowerSeries ℚ) = (4 : PowerSeries ℚ) := by
  rw [show (4 : Polynomial ℚ) = Polynomial.C (4 : ℚ) from rfl, Polynomial.coe_C, map_ofNat]

/-- First component of the derived vector `θP` (`θ = 2x(x-1)d/dx`): coefficient of `1`. -/
def th0 (P : Fin 5 → Polynomial ℚ) : Polynomial ℚ :=
  2 * Polynomial.X * (Polynomial.X - 1) * (P 0).derivative + 2 * Polynomial.X * (P 1)

/-- Second component of `θP`: coefficient of `L`. -/
def th1 (P : Fin 5 → Polynomial ℚ) : Polynomial ℚ :=
  2 * Polynomial.X * (Polynomial.X - 1) * (P 1).derivative + 4 * Polynomial.X * (P 2)
    - 2 * (Polynomial.X - 1) * (P 3 + P 4)

/-- Third component of `θP`: coefficient of `L²`. -/
def th2 (P : Fin 5 → Polynomial ℚ) : Polynomial ℚ :=
  2 * Polynomial.X * (Polynomial.X - 1) * (P 2).derivative

/-- Fourth component of `θP`: coefficient of `Li₂`. -/
def th3 (P : Fin 5 → Polynomial ℚ) : Polynomial ℚ :=
  2 * Polynomial.X * (Polynomial.X - 1) * (P 3).derivative

/-- Fifth component of `θP`: coefficient of `J`. -/
def th4 (P : Fin 5 → Polynomial ℚ) : Polynomial ℚ :=
  2 * Polynomial.X * (Polynomial.X - 1) * (P 4).derivative + Polynomial.X * (P 4)

/-- **The derived polynomial vector.**  If `Σ Pᵢ fᵢ = 0` then also `Σ (thetaP P)ᵢ fᵢ = 0`; see
`Work.C7.theta_rel`. -/
def thetaP (P : Fin 5 → Polynomial ℚ) : Fin 5 → Polynomial ℚ :=
  ![th0 P, th1 P, th2 P, th3 P, th4 P]

lemma th_zero (P : Fin 5 → Polynomial ℚ) : thetaP P 0 = th0 P := rfl
lemma th_one (P : Fin 5 → Polynomial ℚ) : thetaP P 1 = th1 P := rfl
lemma th_two (P : Fin 5 → Polynomial ℚ) : thetaP P 2 = th2 P := rfl
lemma th_three (P : Fin 5 → Polynomial ℚ) : thetaP P 3 = th3 P := rfl
lemma th_four (P : Fin 5 → Polynomial ℚ) : thetaP P 4 = th4 P := rfl

end Work.C7
