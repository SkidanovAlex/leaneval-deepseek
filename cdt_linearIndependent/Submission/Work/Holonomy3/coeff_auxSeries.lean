import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.ZeroEst.coeff_prod_embedVar

namespace Work.Holonomy3

open scoped BigOperators

/-- A multivariable polynomial, viewed as a power series, is the sum of its monomials. -/
private lemma coe_as_sum {d : ℕ} (P : MvPolynomial (Fin d) ℚ) :
    (P : MvPowerSeries (Fin d) ℚ) = ∑ c ∈ P.support, MvPowerSeries.monomial c (P.coeff c) := by
  ext e
  rw [MvPolynomial.coeff_coe, map_sum]
  simp only [MvPowerSeries.coeff_monomial]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact MvPolynomial.notMem_support_iff.mp h

/-- Coefficient extraction for the auxiliary series `Σ_i Q_i(x)·∏_s f_{i_s}(x_s)`: the
coefficient at the exponent `n'` is the sum over the species vector `i` and the monomials `k` of
`Q i` with `k ≤ n'` of `(Q i).coeff k · ∏_s (f (i s)).coeff (n' s - k s)`. -/
theorem coeff_auxSeries {m d : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) (n' : Fin d →₀ ℕ) :
    MvPowerSeries.coeff n' (Submission.CDTPlan.auxSeries f Q) =
      ∑ i : Fin d → Fin m, ∑ k ∈ (Q i).support,
        (if k ≤ n' then ((Q i).coeff k : ℚ) *
          ∏ s : Fin d, PowerSeries.coeff (n' s - k s) (f (i s)) else 0) := by
  classical
  rw [Submission.CDTPlan.auxSeries]
  -- coefficient of the finite sum over the species vectors `i`
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- expand `Q i` into its monomials
  rw [coe_as_sum (Q i), Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  -- coefficient of `monomial k a * (∏ s, f (i s)(x_s))`
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases h : k ≤ n'
  · rw [if_pos h, if_pos h]
    congr 1
    -- the product of one-variable embeddings has product coefficients
    rw [Work.ZeroEst.coeff_prod_embedVar]
    refine Finset.prod_congr rfl ?_
    intro s _
    rw [Finsupp.tsub_apply]
  · rw [if_neg h, if_neg h]

end Work.Holonomy3
