import Mathlib
import Submission.Work.BourgainPlan.Maximal.rhoVariationDefs
import Submission.Work.BourgainPlan.Maximal.varSeminormDefs

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

/-- **`ℓ^ρ` ≤ `ℓ²` for `ρ ≥ 2`.**  For `ρ ≥ 2` the `ℓ^ρ`-length of the increments of a chain
(`chainLp`) is at most its `ℓ²`-length (`chainSq`).  This is the elementary comparison of `ℓ^p`
norms on a finite vector (`‖x‖_ρ ≤ ‖x‖_2` for `ρ ≥ 2`); it is what makes every `ρ`-variation with
`ρ ≥ 2` dominated by the `2`-variation, hence (through `varTwo_le_rmLevels`) by the
Rademacher–Menshov dyadic block square functions — KMSZ arXiv:2606.12663, Proposition 5.10 and the
remark after their (6.7). -/
theorem chainLp_le_chainSq {E : Type*} [SeminormedAddCommGroup E]
    (ρ : ℝ) (hρ : 2 ≤ ρ) (J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) :
    chainLp ρ J a t ≤ chainSq J a t := by
  have hρpos : 0 < ρ := by linarith
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hρ2 : 0 ≤ ρ - 2 := by linarith
  have htwo : (((2 : ℕ)) : ℝ) + (ρ - 2) = ρ := by push_cast; ring
  -- the lengths of the increments
  set x : ℕ → ℝ := fun j => ‖a (t (j + 1)) - a (t j)‖ with hx
  -- the `ℓ²`-length squared, and the `ℓ²`-length itself
  set C : ℝ := ∑ j ∈ Finset.range J, x j ^ 2 with hC
  set c : ℝ := Real.sqrt C with hc
  have hxnn : ∀ j, 0 ≤ x j := fun j => by rw [hx]; exact norm_nonneg _
  have hCnn : 0 ≤ C := by
    rw [hC]; exact Finset.sum_nonneg fun j _ => pow_nonneg (hxnn j) 2
  have hcnn : 0 ≤ c := by rw [hc]; exact Real.sqrt_nonneg _
  have hsq : chainSq J a t = c := by
    rw [chainSq, hc, hC]
  -- every increment is at most `c`
  have hle_c : ∀ j, j ∈ Finset.range J → x j ≤ c := by
    intro j hj
    have hxj2 : x j ^ 2 ≤ C := by
      rw [hC]
      exact Finset.single_le_sum (fun i _ => pow_nonneg (hxnn i) 2) hj
    have h := Real.sqrt_le_sqrt hxj2
    rw [Real.sqrt_sq (hxnn j)] at h
    rwa [← hc] at h
  -- termwise bound: `x_j ^ ρ ≤ x_j ^ 2 * c ^ (ρ - 2)`
  have hterm : ∀ j ∈ Finset.range J, x j ^ ρ ≤ x j ^ 2 * c ^ (ρ - 2) := by
    intro j hj
    have hpow : x j ^ (ρ - 2) ≤ c ^ (ρ - 2) := Real.rpow_le_rpow (hxnn j) (hle_c j hj) hρ2
    calc x j ^ ρ = x j ^ (((2 : ℕ)) + (ρ - 2)) := by rw [htwo]
      _ = x j ^ (((2 : ℕ)) : ℝ) * x j ^ (ρ - 2) :=
            Real.rpow_add' (hxnn j) (by rw [htwo]; exact hρne)
      _ = x j ^ 2 * x j ^ (ρ - 2) := by rw [Real.rpow_natCast]
      _ ≤ x j ^ 2 * c ^ (ρ - 2) := mul_le_mul_of_nonneg_left hpow (pow_nonneg (hxnn j) 2)
  have hsum : ∑ j ∈ Finset.range J, x j ^ ρ ≤ C * c ^ (ρ - 2) := by
    calc ∑ j ∈ Finset.range J, x j ^ ρ ≤ ∑ j ∈ Finset.range J, x j ^ 2 * c ^ (ρ - 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range J, x j ^ 2) * c ^ (ρ - 2) := (Finset.sum_mul _ _ _).symm
      _ = C * c ^ (ρ - 2) := by rw [hC]
  -- `C * c ^ (ρ - 2) = c ^ ρ`, since `C = c²`
  have hCmul : C * c ^ (ρ - 2) = c ^ ρ := by
    have hc2 : c ^ 2 = C := by rw [hc]; exact Real.sq_sqrt hCnn
    calc C * c ^ (ρ - 2) = c ^ 2 * c ^ (ρ - 2) := by rw [hc2]
      _ = c ^ (((2 : ℕ)) : ℝ) * c ^ (ρ - 2) := by rw [Real.rpow_natCast]
      _ = c ^ ((((2 : ℕ)) : ℝ) + (ρ - 2)) :=
            (Real.rpow_add' hcnn (by rw [htwo]; exact hρne)).symm
      _ = c ^ ρ := by rw [htwo]
  -- the `ℓ^ρ`-length, raised to the `ρ`-th power, is at most `c ^ ρ`
  have hkey : ∑ j ∈ Finset.range J, x j ^ ρ ≤ c ^ ρ := hsum.trans (le_of_eq hCmul)
  calc chainLp ρ J a t = (∑ j ∈ Finset.range J, x j ^ ρ) ^ (1 / ρ) := by rw [chainLp]
    _ ≤ (c ^ ρ) ^ (1 / ρ) :=
        Real.rpow_le_rpow
          (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hxnn j) _) hkey (by positivity)
    _ = c := by
        rw [← Real.rpow_mul hcnn ρ (1 / ρ), mul_one_div_cancel hρne, Real.rpow_one]
    _ = chainSq J a t := hsq.symm

end Work.BourgainPlan.Maximal
