import Mathlib
import Submission.Work.C7.xdefs

/-!
# Area C7b — the four-term elimination identity for `{1, L, L², Li₂}`

`L = log(1-x)`, `Li₂ = Li₂(x)` satisfy `(1-x)L' = -1` and `x Li₂' = -L`, so the `ℚ(x)`-span of
`{1, L, L², Li₂}` is closed under `d/dx` and `Li₂` can be eliminated from any relation
`p₀ + p₁L + p₂L² + p₃Li₂ = 0` with polynomial coefficients: the combination
`x(1-x)·(p₃·R' − p₃'·R)` is again a `ℚ[x]`-combination of `1, L, L²` (the `Li₂` term cancels),
and it is displayed explicitly in `four_key`.
-/

namespace Work.C7b

open PowerSeries

/-- Auxiliary normalisation: the coercion of the numeral `2 ∈ ℚ[X]` to `ℚ⟦X⟧` is `2`. -/
private lemma coe_two_poly : (((2 : Polynomial ℚ)) : PowerSeries ℚ) = (2 : PowerSeries ℚ) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply]
  exact map_ofNat _ 2

/-- The elimination identity: the displayed combination equals `x(1-x) (p₃ R' − p₃' R)`
where `R = p₀ + p₁ L + p₂ L² + p₃ Li₂`. -/
lemma four_key (p0 p1 p2 p3 : Polynomial ℚ) :
    ((Polynomial.X * (1 - Polynomial.X) * (p3 * p0.derivative - p3.derivative * p0)
        - Polynomial.X * p1 * p3 : Polynomial ℚ) : PowerSeries ℚ)
      + ((Polynomial.X * (1 - Polynomial.X) * (p3 * p1.derivative - p3.derivative * p1)
          - 2 * Polynomial.X * p2 * p3 - (1 - Polynomial.X) * p3 ^ 2 : Polynomial ℚ) : PowerSeries ℚ)
        * Work.C7.Lps
      + ((Polynomial.X * (1 - Polynomial.X) * (p3 * p2.derivative - p3.derivative * p2) : Polynomial ℚ)
          : PowerSeries ℚ) * Work.C7.Lps ^ 2
    = PowerSeries.X * (1 - PowerSeries.X) *
        ((p3 : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ)
            ((p0 : PowerSeries ℚ) + (p1 : PowerSeries ℚ) * Work.C7.Lps
              + (p2 : PowerSeries ℚ) * Work.C7.Lps ^ 2 + (p3 : PowerSeries ℚ) * Work.C7.Li2ps)
         - (p3.derivative : PowerSeries ℚ) *
            ((p0 : PowerSeries ℚ) + (p1 : PowerSeries ℚ) * Work.C7.Lps
              + (p2 : PowerSeries ℚ) * Work.C7.Lps ^ 2 + (p3 : PowerSeries ℚ) * Work.C7.Li2ps)) := by
  push_cast
  simp only [coe_two_poly]
  simp only [map_add, Derivation.leibniz, PowerSeries.derivative_coe, PowerSeries.derivative_pow,
    smul_eq_mul]
  set dL := PowerSeries.derivative (R := ℚ) Work.C7.Lps with hdL
  set dLi := PowerSeries.derivative (R := ℚ) Work.C7.Li2ps with hdLi
  have h1 : PowerSeries.X * (1 - PowerSeries.X) * dL = -PowerSeries.X := by
    rw [hdL, mul_assoc, Work.C7.deriv_Lps]; ring
  have h2 : PowerSeries.X * (1 - PowerSeries.X) * dLi = -(1 - PowerSeries.X) * Work.C7.Lps := by
    rw [hdLi]
    rw [show PowerSeries.X * (1 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) Work.C7.Li2ps
          = (1 - PowerSeries.X) * (PowerSeries.X * PowerSeries.derivative (R := ℚ) Work.C7.Li2ps) by ring,
        Work.C7.deriv_Li2ps]
    ring
  linear_combination (-(↑p3 * ↑p1) - 2 * ↑p3 * ↑p2 * Work.C7.Lps) * h1 - (↑p3 ^ 2) * h2

theorem four_elim (p0 p1 p2 p3 : Polynomial ℚ)
    (h : (p0 : PowerSeries ℚ) + (p1 : PowerSeries ℚ) * Work.C7.Lps + (p2 : PowerSeries ℚ) * Work.C7.Lps ^ 2
      + (p3 : PowerSeries ℚ) * Work.C7.Li2ps = 0) :
    ((Polynomial.X * (1 - Polynomial.X) * (p3 * p0.derivative - p3.derivative * p0)
        - Polynomial.X * p1 * p3 : Polynomial ℚ) : PowerSeries ℚ)
      + ((Polynomial.X * (1 - Polynomial.X) * (p3 * p1.derivative - p3.derivative * p1)
          - 2 * Polynomial.X * p2 * p3 - (1 - Polynomial.X) * p3 ^ 2 : Polynomial ℚ) : PowerSeries ℚ)
        * Work.C7.Lps
      + ((Polynomial.X * (1 - Polynomial.X) * (p3 * p2.derivative - p3.derivative * p2) : Polynomial ℚ)
          : PowerSeries ℚ) * Work.C7.Lps ^ 2 = 0 := by
  rw [four_key]
  rw [h]
  simp

end Work.C7b
