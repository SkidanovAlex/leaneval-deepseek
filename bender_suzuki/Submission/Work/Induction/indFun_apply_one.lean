import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- Value at the identity: `x * 1 * x⁻¹ = 1 ∈ H` for all `x`, so the defining sum of
-- `indFun H φ 1` has `|G|` equal terms `φ 1`, and `|H|⁻¹ * |G| = H.index`
-- (`Subgroup.card_mul_index`).
theorem indFun_apply_one {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ) :
    Work.Induction.indFun H φ 1 = (H.index : ℂ) * φ 1 := by
  rw [indFun_apply_def]
  -- Each summand is `φ 1`.
  have h1 : ∀ x : G, (if hx : x * 1 * x⁻¹ ∈ H then φ ⟨x * 1 * x⁻¹, hx⟩ else 0) = φ 1 := by
    intro x
    split_ifs with hx
    · congr 1; simp
    · simp only [mul_one, mul_inv_cancel, one_mem, not_true_eq_false] at hx
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    simp [Nat.card_eq_fintype_card]
  have hidx : (Nat.card G : ℂ) = (Nat.card H : ℂ) * (H.index : ℂ) := by
    rw [← Subgroup.card_mul_index H, Nat.cast_mul]
  have hsc : (Nat.card H : ℂ)⁻¹ * (Nat.card G : ℂ) = (H.index : ℂ) := by
    rw [hidx, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  rw [← mul_assoc, hsc]

end Work.Induction
