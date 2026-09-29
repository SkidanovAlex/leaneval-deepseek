/-
`Sα α = Σ_k c_k αᵏ Xᵏ` with `c_k = C(2k,k)/4ᵏ` is the formal series of
`(1 - αX)^{-1/2}`; squaring gives `(1 - αX)^{-1} = Σ_n αⁿ Xⁿ`.
Equivalently `Σ_{i+j=n} c_i c_j = 1`, which is the central-binomial convolution
identity `Σ_{i+j=n} C(2i,i) C(2j,j) = 4ⁿ`
(`Commons.Data.Nat.Choose.centralBinom_convolution`).
-/
import Mathlib
import Submission.Work.C17.beukersUR_defs
import Submission.Commons.Data.Nat.Choose.centralBinom_convolution

namespace Work.C17

open PowerSeries
open scoped BigOperators

noncomputable section

/-- The convolution square of the coefficients of `Sα`: `Σ_{i+j=n} c_i c_j = 1`. -/
lemma cR_convolution (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), cR i * cR (n - i)) = 1 := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      cR i * cR (n - i)
        = ((Nat.centralBinom i : ℝ) * (Nat.centralBinom (n - i) : ℝ)) / (4 : ℝ) ^ n := by
    intro i hi
    have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have h4 : (4 : ℝ) ^ n = (4 : ℝ) ^ i * (4 : ℝ) ^ (n - i) := by
      rw [← pow_add, Nat.add_sub_of_le hi_le]
    rw [h4, cR, cR, div_mul_div_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hreal : (∑ i ∈ Finset.range (n + 1),
      (Nat.centralBinom i : ℝ) * (Nat.centralBinom (n - i) : ℝ)) = (4 : ℝ) ^ n := by
    have h := congrArg (fun x : ℚ => (x : ℝ))
      (Commons.Data.Nat.Choose.centralBinom_convolution n)
    push_cast at h
    exact h
  rw [hreal, div_self (by positivity : (4 : ℝ) ^ n ≠ 0)]

theorem Sseries_sq (α : ℝ) (n : ℕ) :
    PowerSeries.coeff n ((Work.C17.Sα α) ^ 2) = α ^ n := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (Sα α) * PowerSeries.coeff j (Sα α)) n]
  calc
    (∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i (Sα α) * PowerSeries.coeff (n - i) (Sα α))
        = ∑ i ∈ Finset.range (n + 1), (cR i * cR (n - i)) * α ^ n := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hpow : α ^ i * α ^ (n - i) = α ^ n := by
            rw [← pow_add, Nat.add_sub_of_le hi_le]
          rw [coeff_Sα, coeff_Sα]
          calc (cR i * α ^ i) * (cR (n - i) * α ^ (n - i))
              = (cR i * cR (n - i)) * (α ^ i * α ^ (n - i)) := by ring
            _ = (cR i * cR (n - i)) * α ^ n := by rw [hpow]
    _ = (∑ i ∈ Finset.range (n + 1), cR i * cR (n - i)) * α ^ n := by
          rw [Finset.sum_mul]
    _ = α ^ n := by rw [cR_convolution, one_mul]

end

end Work.C17
