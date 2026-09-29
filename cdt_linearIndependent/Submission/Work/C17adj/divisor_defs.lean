import Submission.Work.C17.adjoint_defs
import Submission.Work.C17.p2x_roots_simple
import Submission.Commons.FieldTheory.RatFunc.exists_leading_term
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_eq_of_le_succ

/-!
# Shared definitions for the adjoint divisor bound (`Work.C17adj.adjoint_divisor_boundC`)

The hypothesis of `Work.C17adj.adjoint_divisor_boundC` is the equation

`D²(P₂·β) − D(P₁·β) + P₀·β = Σ_{i<6} c_i · y^{i−4} · y'`     (`y = x²/(x−1)`),

i.e. the *adjoint* `P₂β'' + A·β' + C·β = R` of the order-two operator `M = P₂∂² + P₁∂ + P₀` of the
Calegari--Dimitrov--Tang paper (arXiv:2408.15403, `(ODE)`), with `P₂, P₁, P₀` the images in `ℂ[x]`
of `Work.C17.P2x, P1x, P0x` and

* `AadjL a b = 2·P₂' − P₁`  (the `Badj` of `Work.C17.adjoint_defs`),
* `CadjL a b = P₂'' − P₁' + P₀`  (the `Cadj` of `Work.C17.adjoint_defs`).

The objects here are the ones the local (indicial) analysis of that equation uses:

* `P2Cm, P1Cm, P0Cm, Q4Cm`: the `ℂ`-images of `P2x, P1x, P0x, Q4x`;
* `DadjL = x⁶(x−1)²(x+1)²`, the univeral denominator (divisor bound) of the equation, and
* `PhiNum a b W = D³·(P₂β'' + Aβ' + Cβ)` for `β = W/D`, `D = DadjL` — the cleared numerator;
* `PsiNum c`, the numerator of the right hand side `Σ_i c_i y^{i−4}y'` over `x⁷(x−1)³`.
-/

open Polynomial

namespace Work.C17adj

noncomputable section

/-- The `ℂ`-image of `P2x`. -/
def P2Cm (a b : ℚ) : Polynomial ℂ := (Work.C17.P2x a b).map (algebraMap ℚ ℂ)

/-- The `ℂ`-image of `P1x`. -/
def P1Cm (a b : ℚ) : Polynomial ℂ := (Work.C17.P1x a b).map (algebraMap ℚ ℂ)

/-- The `ℂ`-image of `P0x`. -/
def P0Cm (a b : ℚ) : Polynomial ℂ := (Work.C17.P0x a b).map (algebraMap ℚ ℂ)

/-- The `ℂ`-image of `Q4x`, the quartic whose roots are the four singularities. -/
def Q4Cm (a b : ℚ) : Polynomial ℂ := (Work.C17.Q4x a b).map (algebraMap ℚ ℂ)

/-- `A = 2·P₂' − P₁`, the `β'`-coefficient of the adjoint operator. -/
def AadjL (a b : ℚ) : Polynomial ℂ := 2 * (P2Cm a b).derivative - P1Cm a b

/-- `C = P₂'' − P₁' + P₀`, the `β`-coefficient of the adjoint operator. -/
def CadjL (a b : ℚ) : Polynomial ℂ := (P2Cm a b).derivative.derivative - (P1Cm a b).derivative
  + P0Cm a b

/-- `D = x⁶(x−1)²(x+1)² = x¹⁰ − 2x⁸ + x⁶`, the universal denominator of the divisor bound. -/
def DadjL : Polynomial ℂ := Work.C17.Dadj.map (algebraMap ℚ ℂ)

/-- `D³·(P₂·β'' + A·β' + C·β)` for `β = W/D`, `D = DadjL` — the cleared numerator of the
adjoint operator applied to `W/D`. -/
def PhiNum (a b : ℚ) (W : Polynomial ℂ) : Polynomial ℂ :=
  P2Cm a b * (W.derivative.derivative * DadjL ^ 2
      - 2 * W.derivative * DadjL * DadjL.derivative
      + W * (2 * DadjL.derivative ^ 2 - DadjL * DadjL.derivative.derivative))
    + AadjL a b * (W.derivative * DadjL - W * DadjL.derivative) * DadjL
    + CadjL a b * W * DadjL ^ 2

/-- The numerator `Σ_i c_i x^{2i}(x−2)(x−1)^{5−i}` of the right hand side
`Σ_i c_i y^{i−4}y'` over the common denominator `x⁷(x−1)³` (`y = x²/(x−1)`). -/
def PsiNum (c : Fin 6 → ℂ) : Polynomial ℂ :=
  ∑ i : Fin 6, Polynomial.C (c i) * Polynomial.X ^ (2 * (i : ℕ))
    * (Polynomial.X - Polynomial.C 2) * (Polynomial.X - Polynomial.C 1) ^ (5 - (i : ℕ))

/-- The right hand side of the adjoint equation, `Σ_i c_i·y^{i−4}·y'` with `y = x²/(x−1)`. -/
def RhsC (c : Fin 6 → ℂ) : RatFunc ℂ :=
  ∑ i : Fin 6, algebraMap ℂ (RatFunc ℂ) (c i) * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc

end

end Work.C17adj
