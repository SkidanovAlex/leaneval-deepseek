import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

/-- Integer arithmetic behind the two-block Bender–Suzuki estimate.

If `a ∣ c`, `a ≥ 2`, `n ≥ 2` and `(c - a)² + (n - 1)c² ≤ 1 + a²`, then `c = 0`, or
else `c = a` and `n = 2`.

Proof sketch: since `n - 1 ≥ 1` and `c² ≥ 0` we get `(c - a)² + c² ≤ 1 + a²`, i.e.
`2·c·(c - a) ≤ 1`; as `c·(c - a)` is an integer this gives `c·(c - a) ≤ 0`. Writing
`c = a·k`, this becomes `k·(k - 1) ≤ 0`, forcing `k = 0` or `k = 1`. In the second
case `c = a` and the inequality collapses to `(n - 2)·a² ≤ 1` with `a² ≥ 4`, whence
`n ≤ 2`, i.e. `n = 2`. -/
theorem int_two_block_arith {a c n : ℤ} (hn : 2 ≤ n) (ha : 2 ≤ a) (hdvd : a ∣ c)
    (hineq : (c - a) ^ 2 + (n - 1) * c ^ 2 ≤ 1 + a ^ 2) :
    c = 0 ∨ (c = a ∧ n = 2) := by
  -- Step 1: drop the factor `n - 1 ≥ 1` to obtain `(c - a)² + c² ≤ 1 + a²`.
  have hc2 : c ^ 2 ≤ (n - 1) * c ^ 2 := by nlinarith [hn, sq_nonneg c]
  have h1 : (c - a) ^ 2 + c ^ 2 ≤ 1 + a ^ 2 := by linarith
  -- Step 2: expanding gives `2·(c·(c - a)) ≤ 1`, and integrality gives `c·(c - a) ≤ 0`.
  have h2 : 2 * (c * (c - a)) ≤ 1 := by nlinarith [h1]
  have hquad : c * (c - a) ≤ 0 := by
    by_contra h
    push Not at h
    linarith
  -- Step 3: write `c = a * k` and deduce `k * (k - 1) ≤ 0`.
  obtain ⟨k, rfl⟩ := hdvd
  have hk : k * (k - 1) ≤ 0 := by
    by_contra h
    push Not at h
    have ha2 : 0 < a ^ 2 := by nlinarith
    nlinarith [hquad, h, ha2]
  -- Step 4: an integer `k` with `k * (k - 1) ≤ 0` satisfies `0 ≤ k ≤ 1`.
  have hk01 : k = 0 ∨ k = 1 := by
    have hk1 : k ≤ 1 := by
      by_contra hc
      push Not at hc
      have hpos : 0 < k * (k - 1) := by
        apply mul_pos <;> omega
      omega
    have hk0 : 0 ≤ k := by
      by_contra hc
      push Not at hc
      have hneg : 0 < k * (k - 1) := by
        apply mul_pos_of_neg_of_neg <;> omega
      omega
    omega
  rcases hk01 with hk0 | hk1
  · -- `k = 0`: then `c = a * 0 = 0`.
    left; rw [hk0]; ring
  · -- `k = 1`: then `c = a`, and the hypothesis forces `n = 2`.
    right
    refine ⟨by rw [hk1]; ring, ?_⟩
    have key : (n - 2) * a ^ 2 ≤ 1 := by
      rw [hk1] at hineq
      nlinarith [hineq]
    have ha4 : 4 ≤ a ^ 2 := by nlinarith
    by_contra hn2
    have hle : 1 ≤ n - 2 := by omega
    nlinarith [key, hle, ha4]

end Work.FeitSibley.Coherence
