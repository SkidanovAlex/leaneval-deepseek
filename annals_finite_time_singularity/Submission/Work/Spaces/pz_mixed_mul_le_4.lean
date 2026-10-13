/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Leibniz bound for `∂_z^k D_θ^j (f·g)` with an explicit constant, for `k,j ≤ 4`

`Work.Spaces.pz_mixed_mul_le` produces *some* constant `C` in the Leibniz bound.
For the `H^4`/`𝒲^{4,∞}` estimates of the paper one needs an explicit, uniform
constant for all pairs `k j ≤ 4`.  Since

`∑_{a≤j} C(j,a) = 2^j` and `∑_{c≤k} C(k,c) = 2^k`,

the constant produced by `abs_binom_double_sum_le`,

`1 + ∑_{a≤j} ∑_{c≤k} C(j,a) C(k,c) = 1 + 2^j 2^k`,

is at most `1 + 2^4·2^4 = 257` whenever `k,j ≤ 4`.  This file records that
specialisation: for `k,j ≤ 4`,

`|∂_z^k D_θ^j (f g)| ≤ 257 ∑_{c≤k} ∑_{a≤j} |∂_z^c D_θ^a f| · |∂_z^{k-c} D_θ^{j-a} g|`

at every point of `[0,∞) × [0,π/2]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.abs_binom_double_sum_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## The arithmetic of the explicit constant -/

/-- The binomial constant of the Leibniz rule is at most `257` as soon as `k,j ≤ 4`:
`1 + ∑_{a≤j} ∑_{c≤k} C(j,a) C(k,c) = 1 + 2^j·2^k ≤ 1 + 2^4·2^4 = 257`. -/
lemma one_add_choose_double_sum_le (k j : ℕ) (hk : k ≤ 4) (hj : j ≤ 4) :
    (1 : ℝ) + ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
      (j.choose a : ℝ) * (k.choose c : ℝ) ≤ 257 := by
  have h1 : (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose j, Nat.cast_pow]; norm_num
  have h2 : (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)) = (2 : ℝ) ^ k := by
    rw [← Nat.cast_sum, Nat.sum_range_choose k, Nat.cast_pow]; norm_num
  rw [← Finset.sum_mul_sum, h1, h2]
  have h2j : (2 : ℝ) ^ j ≤ 16 := by
    calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hj
      _ = 16 := by norm_num
  have h2k : (2 : ℝ) ^ k ≤ 16 := by
    calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      _ = 16 := by norm_num
  nlinarith [mul_le_mul h2j h2k (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
    (by norm_num : (0 : ℝ) ≤ 16)]

/-! ## The Leibniz bound with the explicit constant `257` -/

theorem pz_mixed_mul_le_4 (k j : ℕ) (hk : k ≤ 4) (hj : j ≤ 4)
    (f g : ℝ → ℝ → ℝ) (hf : Work.Spaces.SmoothInt f) (hg : Work.Spaces.SmoothInt g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ| ≤
        (257 : ℝ) * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
            |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| := by
  intro z hz θ hθ
  -- The Leibniz expansion is an exact identity for `SmoothInt` functions.
  rw [pz_DthIter_mul_eq k j f g hf hg z hz θ hθ]
  -- Bound the absolute value of the binomial double sum.
  have h1 := abs_binom_double_sum_le k j
    (fun a c => pzIter c (DthIter a f) z θ)
    (fun a c => pzIter (k - c) (DthIter (j - a) g) z θ)
  -- The summation factor is nonnegative.
  have hT : (0 : ℝ) ≤ ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
      |pzIter c (DthIter a f) z θ| * |pzIter (k - c) (DthIter (j - a) g) z θ| :=
    Finset.sum_nonneg fun c _ =>
      Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right (one_add_choose_double_sum_le k j hk hj) hT)

end Work.Spaces
