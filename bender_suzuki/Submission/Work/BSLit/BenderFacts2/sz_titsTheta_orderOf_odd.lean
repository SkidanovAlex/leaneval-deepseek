import Mathlib
import Submission.Work.ZassenhausSuzuki.Tits
import Submission.Work.ZassenhausSuzuki.isTitsTheta_titsTheta
import Submission.Work.Higman.orderOf_frobeniusEquiv_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

/-- Auxiliary: `gcd (2n+1) (n+1) = 1`, since `2n+1 = n + (n+1)` and consecutive integers are
coprime. -/
theorem gcd_two_mul_add_one_add_one (n : ℕ) : Nat.gcd (2 * n + 1) (n + 1) = 1 := by
  have h : Nat.Coprime (2 * n + 1) (n + 1) := by
    rw [show 2 * n + 1 = n + (n + 1) by ring]
    rw [Nat.coprime_add_self_left]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)
  exact h.gcd_eq_one

/-- The **order of the Tits endomorphism** `θ : x ↦ x ^ 2 ^ (n+1)` of `GF(2 ^ (2n+1))` is
`2n+1` (Suzuki 1962; `θ` is the `(n+1)`-st power of the Frobenius `x ↦ x²`, whose order on
`GF(2 ^ (2n+1))` is `2n+1`, and `gcd (2n+1) (n+1) = 1`).  In particular the order is odd, and
`θ` generates `Aut(GF(2^(2n+1)))` together with `θ²` = Frobenius. -/
theorem orderOf_titsTheta (n : ℕ) :
    orderOf (Work.ZassenhausSuzuki.titsTheta n) = 2 * n + 1 := by
  rw [Work.ZassenhausSuzuki.titsTheta, iterateFrobeniusEquiv_eq_pow,
    Work.Higman.orderOf_frobeniusEquiv_pow (2 * n + 1) (n + 1) (by omega)]
  rw [gcd_two_mul_add_one_add_one, Nat.div_one]

theorem sz_titsTheta_orderOf_odd (n : ℕ) :
    Odd (orderOf (Work.ZassenhausSuzuki.titsTheta n)) := by
  rw [orderOf_titsTheta]
  exact ⟨n, rfl⟩

end Work.BSLit.BenderFacts2
