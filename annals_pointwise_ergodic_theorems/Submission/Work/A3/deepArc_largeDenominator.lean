import Mathlib
import Submission.Work.A3.majorArc_split

/-!
# The "deep arc, large denominator" power saving for the polynomial exponential sum

This is the pointwise Weyl-type saving on the *large-denominator* part
(`N^{ε₀} ≤ q ≤ N^{1/2}`) of the circles-method arcs: for `θ = a/q + β` with
`(a,q) = 1`, `N^{ε₀} ≤ q ≤ N^{1/2}` and `|β| ≤ 1/(q N^{d/2})` (`d = deg Q`),

  `‖expSum Q N θ‖ ≤ C · N^{1-θ₀}`

with `θ₀ > 0` depending only on `Q` and `ε₀`.

The proof instantiates the already established Weyl inequality `A3/weyl_poly`:

`‖S_N(θ)‖ ≤ C_w N^{1+ε} (1/q + 1/N + q N^{-d})^{1/2^{d-1}}`,

which applies because `q ≤ N^{1/2} ≤ N^{d/2}` validates the Dirichlet approximation
`|θ - a/q| ≤ 1/(q N^{d/2}) ≤ 1/q²`.  The bracket is at most `3 N^{-ε₀}`: indeed
`1/q ≤ N^{-ε₀}` by `q ≥ N^{ε₀}`, `1/N ≤ N^{-ε₀}` because `ε₀ ≤ 1`, and
`q N^{-d} ≤ N^{1/2-d} ≤ N^{-ε₀}` because `d ≥ 2` and `ε₀ ≤ 1/2`.  Hence

`‖S_N(θ)‖ ≤ C_w 3^{1/2^{d-1}} N^{1 + ε - ε₀/2^{d-1}}`,

and choosing `ε = θ₀ := ε₀/2^d` gives the claim.  The packaging of this computation
(the Dirichlet validation plus the bracket arithmetic) is `expSum_le_of_largeArc`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

theorem deepArc_largeDenominator (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1 / 2) :
    ∃ C θ₀ : ℝ, 0 < θ₀ ∧ 0 < C ∧
      ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
        (N : ℝ) ^ ε₀ ≤ (q : ℝ) → (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) →
        |β| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) / 2)) →
        ‖Work.A3.expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C * (N : ℝ) ^ (1 - θ₀) := by
  -- the available saving, and half of it as the exponent loss of Weyl's inequality
  set A : ℝ := ε₀ / (2 : ℝ) ^ (Polynomial.natDegree Q - 1) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  obtain ⟨C, hCpos, hC⟩ :=
    expSum_le_of_largeArc Q hd (γ := ε₀) (η := (1 / 2 : ℝ)) (ε := A / 2)
      (by linarith) (by norm_num)
  refine ⟨C, A / 2, by linarith, hCpos, ?_⟩
  intro N a q β hN hq hcop hNeps hqN hβ
  -- rewrite the integer denominator `q ≥ 1` as a natural number
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hqnat : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0
  have hqnatR : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by exact_mod_cast hqnat
  have hqnat1 : 1 ≤ q.toNat := by
    have := Int.toNat_of_nonneg hq0
    omega
  have hcop' : IsCoprime a ((q.toNat : ℕ) : ℤ) := by rw [hqnat]; exact hcop
  -- the point lies in the large-denominator arc set at level `γ = ε₀`, `η = 1/2`
  have hmem : (a : ℝ) / (q : ℝ) + β ∈ largeArcSet Q N (1 / 2 : ℝ) ε₀ := by
    refine ⟨q.toNat, a, hqnat1, hcop', ?_, ?_, ?_⟩
    · rw [hqnatR]; exact hNeps
    · rw [hqnatR]; exact hqN
    · have hdiff : (a : ℝ) / (q : ℝ) + β - (a : ℝ) / ((q.toNat : ℕ) : ℝ) = β := by
        rw [hqnatR]; ring
      rw [hdiff, hqnatR]
      exact hβ
  have hres := hC N ((a : ℝ) / (q : ℝ) + β) hN hmem
  -- the exponents agree: `1 + A/2 - ε₀/2^{d-1} = 1 - A/2`
  have hexp : (1 : ℝ) + A / 2 - ε₀ / (2 : ℝ) ^ (Polynomial.natDegree Q - 1) = 1 - A / 2 := by
    rw [hAdef]; ring
  rw [hexp] at hres
  exact hres

end

end Work.A3
