import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

/-- If `p * b i = q i * B` for all `i ∈ s`, with `B ≠ 0` and `p > 0`, then
`2 * d * p^2 < ∑ q^2` upgrades to `2 * d * B^2 < ∑ b^2`.

Indeed, squaring the relation and summing over `s` gives
`p^2 * ∑ b^2 = B^2 * ∑ q^2`; multiplying the hypothesis by `B^2 > 0` and
dividing out `p^2 > 0` finishes. -/
theorem arith_sum_sq_lt {ι : Type*} (s : Finset ι) (b q : ι → ℤ) (B p d : ℤ)
    (hp : 0 < p) (hd : 0 < d) (hB : B ≠ 0)
    (hrel : ∀ i ∈ s, p * b i = q i * B)
    (hineq : 2 * d * p ^ 2 < ∑ i ∈ s, (q i) ^ 2) :
    2 * d * B ^ 2 < ∑ i ∈ s, (b i) ^ 2 := by
  -- Square the relation `p * b i = q i * B` and sum over `s`.
  have h1 : ∑ i ∈ s, (p * b i) ^ 2 = ∑ i ∈ s, (q i * B) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrel i hi]
  have h2 : ∑ i ∈ s, (p * b i) ^ 2 = p ^ 2 * ∑ i ∈ s, (b i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h3 : ∑ i ∈ s, (q i * B) ^ 2 = B ^ 2 * ∑ i ∈ s, (q i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum : p ^ 2 * ∑ i ∈ s, (b i) ^ 2 = B ^ 2 * ∑ i ∈ s, (q i) ^ 2 := by
    linarith
  have hB2 : (0 : ℤ) < B ^ 2 := by positivity
  have hp2 : (0 : ℤ) < p ^ 2 := by positivity
  nlinarith [hsum, hineq, hB2, hp2]

end Work.FeitSibley.Coherence
