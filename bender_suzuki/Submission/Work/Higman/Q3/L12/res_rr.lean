import Mathlib
import Submission.Work.Higman.Q3.L12.two_pow_congruence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

/-- **The `B(n,θ,ε)` two-term congruence of Higman's Lemma 12, with the common factor
`(1 + 2 ^ r)` still present.**

Given `0 < r < n`, `k, l < n`, `Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1)`, and
`2 ^ k * (1 + 2 ^ r) + 2 ^ l * (1 + 2 ^ r) ≡ (1 + 2 ^ r) * (1 + 2 ^ r) (mod 2 ^ n - 1)`,
the exponents are forced to be `{k, l} = {0, r}`.

The factor `(1 + 2 ^ r)` is a unit modulo `2 ^ n - 1` (the coprimality hypothesis), so it
cancels from the congruence, leaving the reduced two-term congruence
`2 ^ k + 2 ^ l ≡ 2 ^ 0 + 2 ^ r (mod 2 ^ n - 1)`, which is
`Work.Higman.Q3.L12.two_pow_congruence`. -/
theorem res_rr {n r k l : ℕ} (hn : 0 < n) (hr : r < n) (hr0 : r ≠ 0) (hk : k < n)
    (hl : l < n) (hcop : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1))
    (h : 2 ^ k * (1 + 2 ^ r) + 2 ^ l * (1 + 2 ^ r) ≡ (1 + 2 ^ r) * (1 + 2 ^ r)
      [MOD 2 ^ n - 1]) :
    (k = 0 ∧ l = r) ∨ (k = r ∧ l = 0) := by
  -- Factor the common `(1 + 2 ^ r)` out of the left-hand side of the congruence.
  have hL : 2 ^ k * (1 + 2 ^ r) + 2 ^ l * (1 + 2 ^ r) = (1 + 2 ^ r) * (2 ^ k + 2 ^ l) := by
    ring
  rw [hL] at h
  -- `1 + 2 ^ r` is invertible modulo `2 ^ n - 1`; cancel it.
  have h2 : 2 ^ k + 2 ^ l ≡ 1 + 2 ^ r [MOD 2 ^ n - 1] :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm h
  -- Reduce to the pure two-term congruence.
  exact two_pow_congruence hn hr hk hl hr0 (by simpa using h2)

end Work.Higman.Q3.L12
