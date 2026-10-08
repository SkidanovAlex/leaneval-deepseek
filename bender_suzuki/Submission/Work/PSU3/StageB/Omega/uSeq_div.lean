import Mathlib
import Submission.Work.PSU3.StageB.Omega.Seq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.PSU3.StageB.Omega

/-- Peterfalvi Ch. VII §2 (13)/(14): with `β·β + 1 = α·β` (i.e. `α = β + β⁻¹`) the
closed forms `uSeq` and `wSeq` satisfy `u_i / u_{i+1} = 1 + 1 / w_i`.

The proof unwinds the definitions, writes `β^i` as `β^{i-1}·β` and evaluates the
resulting rational identity in characteristic two. -/
theorem uSeq_div {n : ℕ} (α β : Work.PSU3.E n) (hα : β + β⁻¹ = α) (hβ : β ≠ 0)
    (hα0 : α ≠ 0) {i : ℕ} (hi : 1 ≤ i) (h₁ : β ^ i + (β ^ i)⁻¹ ≠ 0)
    (h₂ : β ^ (i + 1) + (β ^ (i + 1))⁻¹ ≠ 0) :
    Work.PSU3.StageB.Omega.uSeq β i / Work.PSU3.StageB.Omega.uSeq β (i + 1) =
      1 + 1 / Work.PSU3.StageB.Omega.wSeq α β i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [uSeq, wSeq]
  have hA : β ^ j.succ = β ^ j * β := pow_succ β j
  have hB : β ^ (j.succ + 1) = β ^ j * β ^ 2 := by rw [pow_succ, hA]; ring
  rw [hA, hB]
  have hp1 : β ^ j * β + (β ^ j * β)⁻¹ ≠ 0 := by rw [← hA]; exact h₁
  have hp2 : β ^ j * β ^ 2 + (β ^ j * β ^ 2)⁻¹ ≠ 0 := by rw [← hB]; exact h₂
  have hq : (β ^ j) ^ 2 * β ^ 2 + 1 ≠ 0 := by
    have hx : β ^ j * β ≠ 0 := mul_ne_zero (pow_ne_zero j hβ) hβ
    have hfac : β ^ j * β + (β ^ j * β)⁻¹ = ((β ^ j) ^ 2 * β ^ 2 + 1) * (β ^ j * β)⁻¹ := by
      rw [show (β ^ j) ^ 2 * β ^ 2 + 1 = (β ^ j * β) ^ 2 + 1 by ring]
      rw [add_mul, one_mul, pow_two, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    rw [hfac] at hp1
    exact fun h => hp1 (by rw [h, zero_mul])
  field_simp
  rw [← hα]
  ring_nf
  field_simp
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  ring

end Work.PSU3.StageB.Omega
