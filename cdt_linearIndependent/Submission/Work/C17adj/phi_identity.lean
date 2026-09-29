import Mathlib
import Submission.Work.C17adj.divisor_defs

/-!
# `PhiNum` is the cleared numerator of the adjoint operator

`Work.C17adj.PhiNum a b W` is *defined* as the denominator-cleared numerator
`D³·(P₂β'' + A·β' + C·β)` of the adjoint operator applied to `β = W/D`,
`D = DadjL = x⁶(x−1)²(x+1)²`.  The theorem `phi_identity` records that the definition
does compute that object:

`algebraMap (PhiNum a b W) = D³·(P₂·β'' + A·β' + C·β)`   in `ℂ(x)`.

The mathematical content is the quotient rule, applied twice:

* `β = nn/d`, `β' = (nn'·d − nn·d')/d²`,
* `β'' = (nn''·d² − 2·nn'·d·d' + nn·(2·d'² − d·d''))/d³`,

which after multiplying by `d³` gives exactly the polynomial

`P₂·(nn''·d² − 2·nn'·d·d' + nn·(2·d'² − d·d'')) + A·(nn'·d − nn·d')·d + C·nn·d²`.

We prove this for an arbitrary field `K` (`dRat_adj_clearing_general`), so that the
polynomial algebra is done once, and specialise to `K = ℂ`.
-/

open Polynomial

namespace Work.C17adj

noncomputable section

/-- `D = x⁶(x−1)²(x+1)²` is a nonzero polynomial (its `x¹⁰`-coefficient is `1`). -/
lemma DadjL_ne_zero : (DadjL : Polynomial ℂ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff 10) h
  simp [DadjL, Work.C17.Dadj] at hc

/-- **Clearing the denominators of the adjoint operator.**  For `β = nn/d` in `K(x)`
(`d ≠ 0`), multiplying the adjoint expression `P₂·β'' + A·β' + C·β` by `d³` gives the
image of the explicit polynomial
`P₂·(nn''·d² − 2·nn'·d·d' + nn·(2·d'² − d·d'')) + A·(nn'·d − nn·d')·d + C·nn·d²`. -/
theorem dRat_adj_clearing_general {K : Type*} [Field K]
    (P2 A C nn d : Polynomial K) (hd : d ≠ 0) :
    let β : RatFunc K := algebraMap (Polynomial K) (RatFunc K) nn
      / algebraMap (Polynomial K) (RatFunc K) d
    algebraMap (Polynomial K) (RatFunc K)
        (P2 * (nn.derivative.derivative * d ^ 2 - 2 * nn.derivative * d * d.derivative
              + nn * (2 * d.derivative ^ 2 - d * d.derivative.derivative))
         + A * (nn.derivative * d - nn * d.derivative) * d
         + C * nn * d ^ 2)
      = (algebraMap (Polynomial K) (RatFunc K) d) ^ 3
        * (algebraMap (Polynomial K) (RatFunc K) P2 * Submission.CDT.dRat (Submission.CDT.dRat β)
           + algebraMap (Polynomial K) (RatFunc K) A * Submission.CDT.dRat β
           + algebraMap (Polynomial K) (RatFunc K) C * β) := by
  dsimp only
  have hd' : (algebraMap (Polynomial K) (RatFunc K) d) ≠ 0 := fun h =>
    hd (IsFractionRing.injective (Polynomial K) (RatFunc K) (by rw [h, map_zero]))
  set β : RatFunc K := algebraMap (Polynomial K) (RatFunc K) nn
      / algebraMap (Polynomial K) (RatFunc K) d with hβ
  -- first derivative: the quotient rule
  have h1 : Submission.CDT.dRat β
      = algebraMap (Polynomial K) (RatFunc K) (nn.derivative * d - nn * d.derivative)
        / (algebraMap (Polynomial K) (RatFunc K) d) ^ 2 := by
    rw [hβ, Submission.CDT.dRat_div]
  -- second derivative: the quotient rule once more, on `nn'/d - nn·d'/d²`
  have h2 : Submission.CDT.dRat (Submission.CDT.dRat β)
      = algebraMap (Polynomial K) (RatFunc K)
          ((nn.derivative * d - nn * d.derivative).derivative * d^2
            - (nn.derivative * d - nn * d.derivative) * (d^2).derivative)
        / (algebraMap (Polynomial K) (RatFunc K) d) ^ 4 := by
    rw [h1]
    rw [show algebraMap (Polynomial K) (RatFunc K) (nn.derivative * d - nn * d.derivative)
          / (algebraMap (Polynomial K) (RatFunc K) d) ^ 2
        = algebraMap (Polynomial K) (RatFunc K) (nn.derivative * d - nn * d.derivative)
          / algebraMap (Polynomial K) (RatFunc K) (d^2) from by rw [map_pow]]
    rw [Submission.CDT.dRat_div]
    rw [show (algebraMap (Polynomial K) (RatFunc K) (d^2))^2
        = (algebraMap (Polynomial K) (RatFunc K) d)^4 from by rw [map_pow]; ring]
  rw [h2, h1, hβ]
  -- the numerator of the second derivative is `d` times the numerator of `β''` over `d³`
  have hM : derivative (derivative nn * d - nn * derivative d) * d ^ 2 -
          (derivative nn * d - nn * derivative d) * derivative (d ^ 2)
      = d * (derivative (derivative nn) * d ^ 2 - 2 * derivative nn * d * derivative d +
                nn * (2 * derivative d ^ 2 - d * derivative (derivative d))) := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_pow,
       Nat.reduceSub, pow_one, Nat.cast_ofNat, map_ofNat]
    ring
  rw [hM]
  simp only [map_add, map_mul, map_pow, map_sub]
  field_simp [hd']

/-- **`PhiNum` is the cleared numerator of the adjoint operator at `β = W/DadjL`.** -/
theorem phi_identity (a b : ℚ) (W : Polynomial ℂ) :
    let β : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) W
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17adj.DadjL
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17adj.PhiNum a b W)
      = (algebraMap (Polynomial ℂ) (RatFunc ℂ) Work.C17adj.DadjL) ^ 3
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17adj.P2Cm a b)
              * Submission.CDT.dRat (Submission.CDT.dRat β)
           + algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17adj.AadjL a b) * Submission.CDT.dRat β
           + algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17adj.CadjL a b) * β) := by
  unfold Work.C17adj.PhiNum
  exact dRat_adj_clearing_general (Work.C17adj.P2Cm a b) (Work.C17adj.AadjL a b)
    (Work.C17adj.CadjL a b) W Work.C17adj.DadjL DadjL_ne_zero

end

end Work.C17adj
