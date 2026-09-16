import Submission.ZagierHoffmanProof.StepA
import Submission.ZagierHoffmanProof.Valuation
import Submission.Commons.Algebra.Binomial.trunc_inv_add_one
import Submission.Commons.FieldTheory.Finite.sum_pow_eq

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step M1: Thakur's degree formula for the depth-one power sums

For a finite field `F` of cardinality `q` and an integer `k ≥ 1`, Thakur (Power sums
with applications to multizeta values, 3.1) computes the degree at infinity of the
depth-one power sum
  `S_1(k) = ∑_{c : F} (X + c)^{-k} ∈ K = F(X)`
as `deg S_1(k) = −(k + j_min(k))`, where `j_min(k)` is the least positive integer `j`
with `(q − 1) ∣ j` and `binom(k + j − 1, j) ≠ 0` in `F`.

The key point is the truncated binomial expansion of the summands:
`(X + c)^{-k} = X^{-k} ∑_{j ≤ N} binom(-k, j) (c/X)^j + O(X^{-k-N-1})`,
together with the power sum `∑_{c : F} c^j` which vanishes unless `(q − 1) ∣ j`.
The remainder is a genuine `O(X^{-k-N-1})` because it is an *algebraic* identity
for `(1+Y)^{-k}` truncated at `Y^{N+1}` (`Commons.Algebra.Binomial.trunc_inv_add_one`).

The companion results give the completed valuation `v (P_1 k) = exp(−(k + j_min k))`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section PowerSum

/-- `psumF j = ∑_{c : F} c^j`, the power sum over the finite field. -/
noncomputable def psumF (j : ℕ) : F :=
  letI : Fintype F := Fintype.ofFinite F
  ∑ c : F, c ^ j

lemma psumF_zero : psumF F 0 = 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [psumF]
  simp only [pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact FiniteField.cast_card_eq_zero F

/-- `psumF j = ∑_{c : F} c^j` equals `−1` when `(q − 1) ∣ j` and `j ≠ 0`, and `0`
otherwise. -/
lemma psumF_eq (j : ℕ) (hj : 1 ≤ j) :
    psumF F j = if (Nat.card F - 1) ∣ j then (-1 : F) else 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [psumF, Commons.FieldTheory.Finite.sum_pow_eq (K := F) (i := j) (by omega : 0 < j)]
  rw [show Fintype.card F - 1 = Nat.card F - 1 by rw [Fintype.card_eq_nat_card]]

/-- The binomial coefficient `C(−k, j) = (−1)^j C(k + j − 1, j)` reduced to `F`. -/
def binF (k j : ℕ) : F := (-1) ^ j * ((Nat.choose (k + j - 1) j : ℕ) : F)

lemma binF_ne_zero_iff (k j : ℕ) :
    binF F k j ≠ 0 ↔ ((Nat.choose (k + j - 1) j : ℕ) : F) ≠ 0 := by
  rw [binF, mul_ne_zero_iff]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨by simp, h⟩

end PowerSum

end ZagierHoffmanPositiveChar
