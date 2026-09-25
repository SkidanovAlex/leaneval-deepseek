import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

/-- Homogeneity of the `ℓᵖ`-(quasi)norm under a nonnegative scalar: scaling the
values of `f : ι → ℂ` by `c ≥ 0` scales the `q`-norm `(∑ ‖f i‖ ^ q) ^ (1/q)`
by the same factor `c`. -/
theorem lpn_smul_eq {ι : Type*} [Fintype ι] (f : ι → ℂ) {q : ℝ} (hq : 0 < q) (c : ℝ) (hc : 0 ≤ c) :
    (∑ i, ‖(c : ℂ) • f i‖ ^ q) ^ (1 / q) = c * (∑ i, ‖f i‖ ^ q) ^ (1 / q) := by
  have hq' : q ≠ 0 := ne_of_gt hq
  have hcnorm : ‖(c : ℂ)‖ = c := (RCLike.norm_ofReal c).trans (abs_of_nonneg hc)
  have hS : 0 ≤ ∑ i, ‖f i‖ ^ q :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) q)
  have hnorm : ∀ i, ‖(c : ℂ) • f i‖ = c * ‖f i‖ := fun i => by
    rw [norm_smul, hcnorm]
  have hterm : ∀ i, ‖(c : ℂ) • f i‖ ^ q = c ^ q * ‖f i‖ ^ q := by
    intro i
    rw [hnorm i, Real.mul_rpow hc (norm_nonneg _)]
  have hsum : ∑ i, ‖(c : ℂ) • f i‖ ^ q = c ^ q * ∑ i, ‖f i‖ ^ q := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    rw [Finset.mul_sum]
  have hcq : (c ^ q) ^ (1 / q) = c := by
    rw [← Real.rpow_mul hc q (1 / q), mul_one_div, div_self hq', Real.rpow_one]
  rw [hsum, Real.mul_rpow (Real.rpow_nonneg hc q) hS, hcq]

end Commons.Analysis.Real