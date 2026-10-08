import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- The power of an `R`-linear equivalence, viewed as an endomorphism of `V`, evaluated at a
vector, agrees with the iterated action of the equivalence. -/
lemma linearEquiv_coe_pow_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ξ : V ≃ₗ[ZMod 2] V) (k : ℕ) (u : V) :
    ((ξ : V →ₗ[ZMod 2] V) ^ k) u = (ξ ^ k) u := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, LinearEquiv.mul_apply, ih]; rfl

/-- Let `V` be a `ZMod 2`-module with `ξ` permuting the nonzero vectors transitively. Then a nonzero vector generates `V` as a `Polynomial (ZMod 2)`-module (via `ξ`), so a polynomial in `ξ` that annihilates one nonzero vector annihilates all of `V`. -/
theorem aeval_annihilates_module {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ξ : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ ^ k) a = b)
    {u : V} (hu : u ≠ 0) (p : Polynomial (ZMod 2)) :
    (Polynomial.aeval (ξ : V →ₗ[ZMod 2] V)) p u = 0 →
    (Polynomial.aeval (ξ : V →ₗ[ZMod 2] V)) p = 0 := by
  intro hp
  apply LinearMap.ext
  intro v
  rw [LinearMap.zero_apply]
  by_cases hv : v = 0
  · rw [hv, map_zero]
  · -- `v` is a nonzero vector, so it is in the `ξ`-orbit of `u`.
    obtain ⟨k, hk⟩ := htrans u v hu hv
    have hcoe : ((ξ : V →ₗ[ZMod 2] V) ^ k) u = v := by
      rw [linearEquiv_coe_pow_apply]; exact hk
    rw [← hcoe, ← Module.End.mul_apply]
    -- `aeval ξ p` commutes with every power of the endomorphism `ξ`.
    have h1 : (Polynomial.aeval (ξ : V →ₗ[ZMod 2] V)) p * ((ξ : V →ₗ[ZMod 2] V) ^ k)
        = (Polynomial.aeval (ξ : V →ₗ[ZMod 2] V)) (p * Polynomial.X ^ k) := by
      rw [Polynomial.aeval_mul, Polynomial.aeval_X_pow]
    have h2 : ((ξ : V →ₗ[ZMod 2] V) ^ k) * (Polynomial.aeval (ξ : V →ₗ[ZMod 2] V)) p
        = (Polynomial.aeval (ξ : V →ₗ[ZMod 2] V)) (Polynomial.X ^ k * p) := by
      rw [Polynomial.aeval_mul, Polynomial.aeval_X_pow]
    have heq : (Polynomial.aeval (ξ : V →ₗ[ZMod 2] V)) p * ((ξ : V →ₗ[ZMod 2] V) ^ k)
        = ((ξ : V →ₗ[ZMod 2] V) ^ k) * (Polynomial.aeval (ξ : V →ₗ[ZMod 2] V)) p := by
      rw [h1, h2, mul_comm p (Polynomial.X ^ k)]
    rw [heq, Module.End.mul_apply, hp, map_zero]

end Work.Higman
