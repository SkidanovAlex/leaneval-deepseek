import Mathlib
import Submission.Work.Higman.Q3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- Multiplication by a nonzero scalar of a field, as an additive equivalence. -/
private def mulAddEquiv {F : Type*} [Field F] (c : F) (hc : c ≠ 0) : F ≃+ F where
  toFun := fun x => c * x
  invFun := fun x => c⁻¹ * x
  left_inv := fun x => by show c⁻¹ * (c * x) = x; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv := fun x => by show c * (c⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  map_add' := fun a b => mul_add c a b

/-- `(x, y) ↦ (x, b * y)` as an additive equivalence of `K × K`, for `b ≠ 0`. -/
private def prodMulEquiv {K : Type*} [Field K] (b : K) (hb : b ≠ 0) : K × K ≃+ K × K where
  toFun := fun v => (v.1, b * v.2)
  invFun := fun v => (v.1, b⁻¹ * v.2)
  left_inv := fun v => by show (v.1, b⁻¹ * (b * v.2)) = v; rw [show b⁻¹ * (b * v.2) = v.2 by rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]]
  right_inv := fun v => by show (v.1, b * (b⁻¹ * v.2)) = v; rw [show b * (b⁻¹ * v.2) = v.2 by rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]]
  map_add' := fun a c => by ext <;> simp [mul_add]

theorem reduce_ab_r {n : ℕ} (hn : 1 ≤ n) {r : ℕ} (h2r : 2 * r + 1 = n)
    {C C' f : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0) :
    ∃ (Φ : (GaloisField 2 n × GaloisField 2 n) ≃+ (GaloisField 2 n × GaloisField 2 n))
      (Ψ : GaloisField 2 n ≃+ GaloisField 2 n) (ε : GaloisField 2 n),
      ∀ v : GaloisField 2 n × GaloisField 2 n,
        Ψ (C * (Φ v).1 ^ (1 + 2 ^ r) + C' * (Φ v).2 ^ 2 +
            f * (Φ v).1 ^ (2 ^ (n - 1)) * (Φ v).2 ^ (2 ^ (r + 1)))
          = v.1 ^ (1 + 2 ^ r) + ε * v.1 ^ (2 ^ (n - 1)) * v.2 ^ (2 ^ (r + 1)) + v.2 ^ 2 := by
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  -- The rescaling `b` of the second coordinate makes the `v.2 ^ 2` coefficient equal to `1`.
  set b : GaloisField 2 n := (C * C'⁻¹) ^ (2 ^ (n - 1)) with hbdef
  have hbne : b ≠ 0 := by
    rw [hbdef]
    exact pow_ne_zero _ (mul_ne_zero hC (inv_ne_zero hC'))
  have hb2 : b ^ 2 = C * C'⁻¹ := by
    rw [hbdef, ← pow_mul,
      show 2 ^ (n - 1) * 2 = 2 ^ n by rw [← pow_succ, Nat.sub_add_cancel hn],
      ← hcard, FiniteField.pow_card]
  -- `Φ = (x, y) ↦ (x, b * y)`, `Ψ = z ↦ C⁻¹ * z`, `ε = C⁻¹ * f * b ^ (2 ^ (r + 1))`.
  refine ⟨prodMulEquiv b hbne, mulAddEquiv C⁻¹ (inv_ne_zero hC),
    C⁻¹ * f * b ^ (2 ^ (r + 1)), ?_⟩
  intro v
  show C⁻¹ * (C * v.1 ^ (1 + 2 ^ r) + C' * (b * v.2) ^ 2 +
        f * v.1 ^ (2 ^ (n - 1)) * (b * v.2) ^ (2 ^ (r + 1)))
      = v.1 ^ (1 + 2 ^ r) + (C⁻¹ * f * b ^ (2 ^ (r + 1))) *
          v.1 ^ (2 ^ (n - 1)) * v.2 ^ (2 ^ (r + 1)) + v.2 ^ 2
  rw [mul_pow, mul_pow, hb2]
  field_simp
  ring

end Work.Higman.Q3
