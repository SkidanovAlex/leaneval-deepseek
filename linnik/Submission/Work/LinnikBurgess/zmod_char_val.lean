import Mathlib

/-!
# The additive character `w ↦ θ ^ w.val` of `ZMod N`

For a root of unity `θ` (with `θ ^ N = 1`) the map `w ↦ θ ^ w.val` is an additive character of
`ZMod N`; these are the three evaluations of it used by the quadratic Gauss-sum estimates: its
additivity, its value at a negative, and its behaviour under complex conjugation.
-/

namespace Work.LinnikBurgess

/-- `w ↦ θ ^ w.val` is an additive character of `ZMod N` when `θ ^ N = 1`. -/
lemma zmod_pow_val_add {N : ℕ} [NeZero N] {θ : ℂ} (hθ : IsPrimitiveRoot θ N) (x y : ZMod N) :
    θ ^ ((x + y).val) = θ ^ x.val * θ ^ y.val := by
  rw [ZMod.val_add, pow_eq_pow_of_modEq (Nat.mod_modEq (x.val + y.val) N) hθ.pow_eq_one,
    pow_add]

/-- Evaluation at the negative is inversion. -/
lemma zmod_pow_val_neg {N : ℕ} [NeZero N] {θ : ℂ} (hθ : IsPrimitiveRoot θ N) (x : ZMod N) :
    θ ^ ((-x).val) = (θ ^ x.val)⁻¹ := by
  have h := zmod_pow_val_add hθ x (-x)
  rw [add_neg_cancel, ZMod.val_zero, pow_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- Conjugation of the character values, using `‖θ‖ = 1`. -/
lemma zmod_pow_val_star {N : ℕ} [NeZero N] {θ : ℂ} (hN : N ≠ 0) (hθ : IsPrimitiveRoot θ N)
    (x : ZMod N) : star (θ ^ x.val) = θ ^ ((-x).val) := by
  have hn : ‖θ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hθ.pow_eq_one hN
  have hstar : star θ = θ⁻¹ := by rw [Complex.star_def, ← Complex.inv_eq_conj hn]
  rw [star_pow, hstar, inv_pow]
  exact (zmod_pow_val_neg hθ x).symm

end Work.LinnikBurgess
