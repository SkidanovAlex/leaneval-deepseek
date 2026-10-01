import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.SieveLocalOneOne
import Submission.Work.LinnikAreas.BGTZ.SumLcmPrimeFactorsNonneg

/-!
# `G(1,χ₀)` is a non-negative real: `0 ≤ Re G(1,χ₀)` and `G(1,χ₀) = ↑(Re G(1,χ₀))`

At `s = 1` and at the principal character `χ = χ₀ = 1` the local factor

`Gloc(p) = u(p)(1+χ₁(p)) - χ₁(p)u(p)²`, `u(p) = χ₀(p)p^{-s}`

becomes a *real* number in `[0,1]`: for `p | q` both `χ₀(p)` and `χ₁(p)` vanish (so `Gloc(p) = 0`),
and for `p ∤ q` it equals `(1+t)/p - t/p²` with `t = χ₁(p) ∈ {-1,1}`, which lies in `[0,1]`.

Writing `f(p) := Re Gloc(p) ∈ [0,1]` and `W(n) := ∏_{p | n} f(p)`, the sieve function is the real
number

`G(1,χ₀) = Σ_{d,e ≤ R} θ_d θ_e W([d,e])`,

and this double sum is `≥ 0`: the prime-wise identity `W([d,e]) W((d,e)) = W(d) W(e)`, together with
`1/f(p) = 1 + c(p)` (`c(p) := (1-f(p))/f(p) ≥ 0` when `f(p) ≠ 0`, and `c(p) := 0` when `f(p) = 0`),
turns it into a sum of squares

`G(1,χ₀) = Σ_{t ⊆ primes ≤ R} (∏_{p ∈ t} c(p)) (Σ_{d ≤ R, t ⊆ P(d)} θ_d W(d))² ≥ 0`.

`SieveLocalOneOne` supplies the pointwise realness and the bounds `0 ≤ f(p) ≤ 1`, and
`SumLcmPrimeFactorsNonneg` the positivity of the resulting double sum.
-/

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-- **`sieveG` at `s = 1` and `χ = χ₀` is the real number `Σ_{d,e ≤ R} θ_dθ_e ∏_{p | [d,e]} f(p)`,
with `f(p) = Re (sieveLocal χ₁ χ₀ 1 p)`.** -/
theorem sieveG_one_one_cast (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    (R : ℕ) (θw : ℕ → ℝ) :
    sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)
      = ((∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          θw d * θw e * ∏ p ∈ (Nat.lcm d e).primeFactors,
            (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p).re : ℝ) : ℂ) := by
  have hre : ∀ p, sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p
      = (((sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p).re : ℝ) : ℂ) :=
    fun p => (SieveLocalOneOne χ₁ hχ₁ p).2.2
  rw [sieveG, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_prod]
  congr 1
  exact Finset.prod_congr rfl (fun p _ => hre p)

theorem SieveGAtOneSq {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {R : ℕ} {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) :
    0 ≤ sieveGre χ₁ R θw 1 (1 : DirichletCharacter ℂ q) ∧
      sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)
        = ((sieveGre χ₁ R θw 1 (1 : DirichletCharacter ℂ q) : ℝ) : ℂ) := by
  have hcast := sieveG_one_one_cast χ₁ hχ₁ R θw
  have hnonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
      θw d * θw e * ∏ p ∈ (Nat.lcm d e).primeFactors,
        (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p).re :=
    SumLcmPrimeFactorsNonneg _ _ R
      (fun p => (SieveLocalOneOne χ₁ hχ₁ p).1)
      (fun p => (SieveLocalOneOne χ₁ hχ₁ p).2.1)
  have hgre : sieveGre χ₁ R θw 1 (1 : DirichletCharacter ℂ q)
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          θw d * θw e * ∏ p ∈ (Nat.lcm d e).primeFactors,
            (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) 1 p).re := by
    rw [sieveGre, hcast, Complex.ofReal_re]
  exact ⟨by rw [hgre]; exact hnonneg, by rw [hcast, hgre]⟩

end Work.LinnikAreas.BGTZ
