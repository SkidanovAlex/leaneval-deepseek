import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTCore

/-- If `M` is a module over the prime field `ZMod p` and every pair of elements of `M` is
linearly dependent, then `M` is nontrivial only when it is one-dimensional, in which case
it has exactly `p` elements. -/
theorem card_eq_prime_of_pairwise_dependent {M : Type} [AddCommGroup M] (p : ℕ) [Fact p.Prime]
    [Module (ZMod p) M]
    (hdep : ∀ x y : M, ∃ c d : ZMod p, (c, d) ≠ 0 ∧ c • x + d • y = 0)
    (hne : ∃ x : M, x ≠ 0) :
    Nat.card M = p := by
  obtain ⟨x, hx⟩ := hne
  -- `x` spans all of `M`: pairwise dependence forces the coefficient of `y` to be nonzero,
  -- and then `y` is a scalar multiple of `x`.
  have hspan : Submodule.span (ZMod p) {x} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    rw [Submodule.mem_span_singleton]
    obtain ⟨c, d, hcd, hcdxy⟩ := hdep x y
    by_cases hd : d = 0
    · -- the coefficient of `y` cannot vanish, since then `c • x = 0` with `c ≠ 0`.
      rw [hd, zero_smul, add_zero] at hcdxy
      have hc : c ≠ 0 := by
        intro hc0
        exact hcd (by simp [hc0, hd])
      rcases smul_eq_zero.mp hcdxy with h | h
      · exact absurd h hc
      · exact absurd h hx
    · -- `d • y = -(c • x)`, so `y = -(d⁻¹ * c) • x`.
      refine ⟨-(d⁻¹ * c), ?_⟩
      have hdy : d • y = -(c • x) := eq_neg_of_add_eq_zero_right hcdxy
      have h1 : d⁻¹ • (d • y) = d⁻¹ • (-(c • x)) := by rw [hdy]
      rw [← mul_smul, inv_mul_cancel₀ hd, one_smul, smul_neg, ← mul_smul] at h1
      rw [neg_smul]
      exact h1.symm
  -- The map `a ↦ a • x` is an equivalence `ZMod p ≃ M`.
  let f : ZMod p →ₗ[ZMod p] M := LinearMap.toSpanSingleton (ZMod p) M x
  have hf_inj : Function.Injective f := by
    intro a b hab
    rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply] at hab
    have : (a - b) • x = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : y ∈ Submodule.span (ZMod p) {x} := by rw [hspan]; exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨a, ha⟩ := hy
    refine ⟨a, ?_⟩
    rw [LinearMap.toSpanSingleton_apply]
    exact ha
  have e : ZMod p ≃ₗ[ZMod p] M := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  calc Nat.card M = Nat.card (ZMod p) := (Nat.card_congr e.toEquiv).symm
    _ = Fintype.card (ZMod p) := Nat.card_eq_fintype_card
    _ = p := ZMod.card p

end Work.SSGRoute.PTCore
