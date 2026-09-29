import Mathlib

/-!
# Definitions for the final assembly of the fine holonomy bound

`Work.Holonomy3.sieveErr` is the total error term produced by the four estimates of the proof of
the fine holonomy bound (`I ≤ A·(1/m)·rearr + errC` from the pointwise bound and
`integral_sup_bound`, `-(A(τ+η)) ≤ log β` from the denominator arithmetic, `errE` from the Abel
summation, and `-log u₀ ≤ errU` from the pole-clearing factor).  The parameter `D` is the one used
in `log_den_coeff_le`/`abel_sum_bound` (the sieve parameter `Ds` of `siegel` plus one), `ε` is the
sieve parameter, `η` the denominator slack, and `G₀ B C₀ M' U₀` are the constants of the problem.

The lemma `Work.Holonomy3.exists_sieve_params` then says that for every `η₁ > 0` one can choose
`ε ≤ ε₀` small, `d` a large multiple of `m` and `D` large (beyond `D₀ ε d` and `(m+Csh+1)/δ`), so
that `sieveErr ≤ η₁`.
-/

namespace Work.Holonomy3

noncomputable section

/-- The total error of the four estimates of the fine holonomy bound, multiplied by `m/A`
(`A = m·d·D/2`), i.e. the quantity that must be made smaller than a prescribed `η₁`. -/
def sieveErr (m l d D : ℕ) (G₀ B C₀ M' U₀ ε η : ℝ) : ℝ :=
  (2 / ((d : ℝ) * D)) *
    ( (ε * d * D + d * Real.log ((D : ℝ) + 1) + d * Real.log (m : ℝ) + d * Real.log M'
        + Real.log 2
        + (D / (2 * (d : ℝ))) * (8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) + d) * G₀
        + D * (ε + 2 / D + 1 / (d : ℝ)) * d * G₀)
      + ((m : ℝ) * d * D * B * (3 * ε + 1 / D + 16 * ((l : ℝ) + 1) / (d : ℝ)))
      + (d * C₀ + d * U₀)
      + (((m : ℝ) * d * D / 2) * η) )

end

end Work.Holonomy3
