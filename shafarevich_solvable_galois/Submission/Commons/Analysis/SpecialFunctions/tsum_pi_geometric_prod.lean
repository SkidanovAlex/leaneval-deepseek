import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecificLimits.Normed
import Submission.Commons.Analysis.TSum.summable_mul_multiIndex_geometric
import Submission.Commons.Analysis.TSum.tsum_prod_fintype
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.SpecialFunctions

open scoped BigOperators

/-- The multivariate geometric series over a finite index type factors as the product of
one-variable geometric series: for `0 ≤ c i < 1`,
`∑' e : ι → ℕ, ∏ i, (c i) ^ (e i) = ∏ i, (1 - c i)⁻¹`. -/
theorem tsum_pi_geometric_prod {ι : Type*} [Fintype ι] {c : ι → ℝ} (h0 : ∀ i, 0 ≤ c i)
    (h1 : ∀ i, c i < 1) :
    ∑' e : ι → ℕ, ∏ i, (c i) ^ (e i) = ∏ i, (1 - c i)⁻¹ := by
  classical
  have hnorm : ∀ i, ‖(c i : ℂ)‖ < 1 := by
    intro i
    rw [show ‖(c i : ℂ)‖ = |c i| from by simp, abs_of_nonneg (h0 i)]
    exact h1 i
  have hsums : ∀ i, Summable (fun n : ℕ => (c i : ℂ) ^ n) := fun i =>
    summable_geometric_of_norm_lt_one (hnorm i)
  have hgeom : ∀ i, (∑' n : ℕ, (c i : ℂ) ^ n) = ((1 - c i)⁻¹ : ℂ) := fun i =>
    tsum_geometric_of_norm_lt_one (hnorm i)
  have hcongr : (∑' e : ι → ℕ, ((∏ i, (c i) ^ (e i) : ℝ) : ℂ))
      = (∑' e : ι → ℕ, ∏ i, (c i : ℂ) ^ (e i)) := by
    refine tsum_congr (fun e => ?_)
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun i _ => Complex.ofReal_pow (c i) (e i))
  have hprod : (∏ i, (∑' n : ℕ, (c i : ℂ) ^ n)) = (∏ i, ((1 - c i)⁻¹ : ℂ)) :=
    Finset.prod_congr rfl (fun i _ => hgeom i)
  refine Complex.ofReal_inj.mp ?_
  calc ((∑' e : ι → ℕ, ∏ i, (c i) ^ (e i) : ℝ) : ℂ)
      = ∑' e : ι → ℕ, ((∏ i, (c i) ^ (e i) : ℝ) : ℂ) := Complex.ofReal_tsum _
    _ = ∑' e : ι → ℕ, ∏ i, (c i : ℂ) ^ (e i) := hcongr
    _ = ∏ i, ∑' n : ℕ, (c i : ℂ) ^ n :=
          Commons.Analysis.TSum.tsum_prod_fintype (fun i n => (c i : ℂ) ^ n) hsums
    _ = ∏ i, ((1 - c i)⁻¹ : ℂ) := hprod
    _ = ((∏ i, (1 - c i)⁻¹ : ℝ) : ℂ) := by
          rw [Complex.ofReal_prod]
          exact Finset.prod_congr rfl (fun i _ => by
            rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one])

end Commons.Analysis.SpecialFunctions
