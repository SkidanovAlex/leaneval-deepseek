/-
The `(1 + 2^n)`-th root used in the Bruhat decomposition of `Sz(2^(2n+1))`.

The form `a^(2 + 2^(n+1)) + a*b + b^(2^(n+1))` is anisotropic
(`Commons.FieldTheory.FiniteField.suzuki_form_ne_zero`), and since
`gcd(1 + 2^n, 2^(2n+1) - 1) = 1`
(`Commons.NumberTheory.coprime_one_add_two_pow_two_mul_succ_sub_one`), every nonzero value has a
unique `(1 + 2^n)`-th root in `GF(2^(2n+1))`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.TwoGroup
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.suzuki_form_ne_zero
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.exists_pow_eq_of_coprime_card_sub_one
import Submission.Work.Models.Port.Commons.NumberTheory.coprime_one_add_two_pow_two_mul_succ_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000


open Matrix LeanEval.GroupTheory.Defs

namespace Submission.Sz

/-- If `(a,b) ≠ (0,0)` then `a^(2 + 2^(n+1)) + a*b + b^(2^(n+1))` is a nonzero `(1 + 2^n)`-th
power in `GF(2^(2n+1))`. -/
theorem sz_exists_root (n : ℕ) (a b : SzField n) (hab : ¬ (a = 0 ∧ b = 0)) :
    ∃ z : SzField n, z ≠ 0 ∧
      z ^ (1 + 2 ^ n) = a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)) := by
  haveI : Fintype (SzField n) := Fintype.ofFinite _
  have hA : a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)) ≠ 0 := by
    intro h
    exact hab (Commons.FieldTheory.FiniteField.suzuki_form_ne_zero n a b h)
  have hcop : Nat.Coprime (1 + 2 ^ n) (Nat.card (SzField n) - 1) := by
    rw [card_szField]
    exact Commons.NumberTheory.coprime_one_add_two_pow_two_mul_succ_sub_one n
  obtain ⟨z, hz⟩ := Commons.FieldTheory.FiniteField.exists_pow_eq_of_coprime_card_sub_one hcop
    (a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1))) hA
  refine ⟨z, ?_, hz⟩
  intro h0
  exact hA (by rw [← hz, h0, zero_pow (by positivity : 1 + 2 ^ n ≠ 0)])

end Submission.Sz
