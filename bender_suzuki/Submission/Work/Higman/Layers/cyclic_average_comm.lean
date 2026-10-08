import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Layers

/-- The cyclic averaging operator commutes with the generator: if `a ^ D = 1`, `b ^ D = 1` and
`b * a = 1` (so `b` is the inverse of `a` and both have order dividing `D`), then the
"averaged" element `∑ k < D, a ^ k * (p * b ^ k)` commutes with `a`. -/
theorem cyclic_average_comm {A : Type*} [Semiring A] {a b p : A} {D : ℕ} (hDpos : 0 < D)
    (ha : a ^ D = 1) (hb : b ^ D = 1) (hba : b * a = 1) :
    (∑ k ∈ Finset.range D, a ^ k * (p * b ^ k)) * a =
      a * (∑ k ∈ Finset.range D, a ^ k * (p * b ^ k)) := by
  -- Since `b * a = 1` and `b ^ D = 1`, we get `b ^ (D - 1) = b ^ D * a = a`.
  have hD_eq : D = (D - 1) + 1 := by omega
  have hpow : b ^ D = b ^ (D - 1) * b := by
    conv_lhs => rw [hD_eq]
    rw [pow_succ]
  have hbDa : b ^ (D - 1) = a := by
    calc b ^ (D - 1) = b ^ (D - 1) * 1 := (mul_one _).symm
      _ = b ^ (D - 1) * (b * a) := by rw [hba]
      _ = (b ^ (D - 1) * b) * a := (mul_assoc _ _ _).symm
      _ = b ^ D * a := by rw [← hpow]
      _ = 1 * a := by rw [hb]
      _ = a := one_mul a
  -- `b ^ (k + 1) * a = b ^ k`.
  have hbsa : ∀ k, b ^ (k + 1) * a = b ^ k := by
    intro k; rw [pow_succ, mul_assoc, hba, mul_one]
  have h1 : ∀ k, (a ^ (k + 1) * (p * b ^ (k + 1))) * a = a ^ (k + 1) * (p * b ^ k) := by
    intro k; rw [mul_assoc, mul_assoc, hbsa k]
  have h2 : (a ^ 0 * (p * b ^ 0)) * a = p * a := by simp
  have h3 : ∀ k, a * (a ^ k * (p * b ^ k)) = a ^ (k + 1) * (p * b ^ k) := by
    intro k; rw [← mul_assoc, ← pow_succ']
  have hstep : a * a ^ (D - 1) = a ^ D := by
    calc a * a ^ (D - 1) = a ^ ((D - 1) + 1) := (pow_succ' a (D - 1)).symm
      _ = a ^ D := by rw [← hD_eq]
  have h4 : a * (a ^ (D - 1) * (p * b ^ (D - 1))) = p * a := by
    rw [← mul_assoc, hstep, ha, one_mul, hbDa]
  -- Both sides reduce to the same sum, via the reindexing `k ↦ k + 1`.
  have hL : (∑ k ∈ Finset.range D, a ^ k * (p * b ^ k)) * a
      = (∑ k ∈ Finset.range (D - 1), a ^ (k + 1) * (p * b ^ k)) + p * a := by
    rw [Finset.sum_mul]
    conv_lhs => rw [hD_eq]
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl (fun k _ => h1 k), h2]
  have hR : a * (∑ k ∈ Finset.range D, a ^ k * (p * b ^ k))
      = (∑ k ∈ Finset.range (D - 1), a ^ (k + 1) * (p * b ^ k)) + p * a := by
    rw [Finset.mul_sum]
    conv_lhs => rw [hD_eq]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_congr rfl (fun k _ => h3 k), h4]
  rw [hL, hR]

end Work.Higman.Layers
