import Mathlib
import Submission.Work.PSU3.StageB.Omega.Seq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageB.Omega

/-- The elementary field identity behind the recursion (11) of Peterfalvi Ch. VII §2, valid in
any commutative field of characteristic two.  Writing `a = β ^ i` (so that `β ^ (i+1) = a * β`,
`β ^ (i+1) / β = a` and `β / β ^ (i+1) = a⁻¹`) it says
`u_{i+1} · (α + u_i) = 1` for `α = β + β⁻¹`, in the cleared-denominator form
`(D_{i+1} D_i)`-free packaging: the two factors are exactly `D_i / D_{i+1}` and
`D_{i+1} / D_i` for `D_j = β ^ j + (β ^ j)⁻¹`, so the product is `1`.

In characteristic two `(β + β⁻¹)(a + a⁻¹) + (a/β + β/a) = a β + (a β)⁻¹`: the two cross terms
`β a⁻¹` and `β⁻¹ a` occur twice and cancel. -/
lemma uSeq_step_mul {K : Type*} [Field K] [CharP K 2] (a β : K) (ha : a ≠ 0)
    (hβ : β ≠ 0) (hD1 : a + a⁻¹ ≠ 0) (hD2 : a * β + (a * β)⁻¹ ≠ 0) :
    ((a * β) / β + β / (a * β)) / (a * β + (a * β)⁻¹) *
      ((β + β⁻¹) + (a / β + β / a) / (a + a⁻¹)) = 1 := by
  have key : (β + β⁻¹) * (a + a⁻¹) + (a / β + β / a) = a * β + (a * β)⁻¹ := by
    field_simp
    ring_nf
    simp [CharTwo.two_eq_zero]
  have step1 : (a * β) / β + β / (a * β) = a + a⁻¹ := by field_simp
  have step2 : (β + β⁻¹) + (a / β + β / a) / (a + a⁻¹) =
      (a * β + (a * β)⁻¹) / (a + a⁻¹) := by
    rw [eq_div_iff hD1, add_mul, div_mul_cancel₀ _ hD1, key]
  rw [step1, step2, div_mul_div_comm, mul_comm (a * β + (a * β)⁻¹) (a + a⁻¹)]
  exact div_self (mul_ne_zero hD1 hD2)

theorem uSeq_rec {n : ℕ} (α β : Work.PSU3.E n) (hα : β + β⁻¹ = α) (hβ : β ≠ 0)
    {i : ℕ} (hi : 1 ≤ i) (h₁ : β ^ i + (β ^ i)⁻¹ ≠ 0)
    (h₂ : β ^ (i + 1) + (β ^ (i + 1))⁻¹ ≠ 0) :
    Work.PSU3.StageB.Omega.uSeq β (i + 1) *
      (α + Work.PSU3.StageB.Omega.uSeq β i) = 1 := by
  rw [uSeq, uSeq, ← hα]
  set a := β ^ i with ha_def
  have ha : a ≠ 0 := by rw [ha_def]; exact pow_ne_zero _ hβ
  have hsucc : β ^ (i + 1) = a * β := by rw [ha_def, pow_succ]
  have hD1 : a + a⁻¹ ≠ 0 := by rw [ha_def] at h₁; exact h₁
  have hD2 : a * β + (a * β)⁻¹ ≠ 0 := by rw [hsucc] at h₂; exact h₂
  rw [hsucc]
  exact uSeq_step_mul a β ha hβ hD1 hD2

end Work.PSU3.StageB.Omega
