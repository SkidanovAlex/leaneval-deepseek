import Mathlib
import Submission.Work.Haupt.thetaCore

/-!
# The functional equation of the two-variable theta series

`ThetaSum x z = ∑'_{n ∈ ℤ} x^{n²} z^n` satisfies, for `x ≠ 0`, `‖x‖ < 1` and `z ≠ 0`,

`ThetaSum x (x² z) = ThetaSum x z / (x z)`.

Multiplying by `x z`, the `n`-th summand of the left-hand side becomes

`x z · x^{n²} (x² z)^n = x^{n² + 2n + 1} z^{n + 1} = x^{(n+1)²} z^{n+1}`,

which is precisely the `(n+1)`-st summand of `ThetaSum x z`.  Summing over `n : ℤ` and shifting
the index by the bijection `n ↦ n + 1` of `ℤ` gives the identity.  Since `ℤ`-indexed `tsum` is
a genuine sum over a countable type, the reindexing is legitimate with no summability hypothesis
(at most both sides are `0` by the `tsum` convention).
-/

namespace Work.Haupt

open scoped BigOperators

noncomputable section

/-- The summand identity behind the functional equation: multiplying the `n`-th summand of
`ThetaSum x (x²z)` by `x z` gives the `(n+1)`-st summand of `ThetaSum x z`. -/
private lemma thetaSum_summand (x z : ℂ) (hx0 : x ≠ 0) (hz : z ≠ 0) (n : ℤ) :
    x * z * (x ^ (n ^ 2) * (x ^ 2 * z) ^ n) = x ^ ((n + 1) ^ 2) * z ^ (n + 1) := by
  have hcast : (x : ℂ) ^ 2 = x ^ (2 : ℤ) := (zpow_natCast x 2).symm
  have hA : (x ^ (2 : ℤ) * z) ^ n = x ^ (2 * n) * z ^ n := by
    rw [mul_zpow, ← zpow_mul x 2 n]
  have h1 : x ^ ((n + 1) ^ 2) = x ^ ((n ^ 2 + 2 * n) + 1) := by congr 1; ring
  have h2 : x ^ (n ^ 2 + 2 * n) = x ^ (n ^ 2) * x ^ (2 * n) := zpow_add₀ hx0 _ _
  have h3 : z ^ (n + 1) = z ^ n * z := zpow_add_one₀ hz n
  rw [hcast]
  calc x * z * (x ^ (n ^ 2) * (x ^ (2 : ℤ) * z) ^ n)
      = x * z * (x ^ (n ^ 2) * (x ^ (2 * n) * z ^ n)) := by rw [hA]
    _ = x ^ ((n + 1) ^ 2) * z ^ (n + 1) := by
          rw [h1, zpow_add_one₀ hx0, h2, h3]
          ring

theorem ThetaSum_functional (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    ∀ z : ℂ, z ≠ 0 → ThetaSum x (x ^ 2 * z) = ThetaSum x z / (x * z) := by
  intro z hz
  have hxz : x * z ≠ 0 := mul_ne_zero hx0 hz
  -- it suffices to show `x z · ThetaSum x (x²z) = ThetaSum x z`, since `x z ≠ 0`
  have key : x * z * ThetaSum x (x ^ 2 * z) = ThetaSum x z := by
    -- unfold both sides and pull the constant `x z` inside the sum
    rw [show ThetaSum x (x ^ 2 * z) = (∑' n : ℤ, x ^ (n ^ 2) * (x ^ 2 * z) ^ n) from rfl,
      ← tsum_mul_left]
    rw [show ThetaSum x z = (∑' m : ℤ, x ^ (m ^ 2) * z ^ m) from rfl]
    -- reindex the right-hand side by the shift `m ↦ m + 1`
    rw [← Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun m : ℤ => x ^ (m ^ 2) * z ^ m)]
    exact tsum_congr fun n => thetaSum_summand x z hx0 hz n
  rw [← key, mul_div_cancel_left₀ _ hxz]

end

end Work.Haupt
