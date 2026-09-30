import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.SpecLin.Alt

/-- If an injective ring map `alg : S →+* K` into a field `K` has the property that the sets of
elements of `K` of the form `alg a / alg b` with `b ∉ m` (resp. `b ∉ m'`) coincide, then the
ideals `m` and `m'` coincide.

The key point: for `s ∉ m` the element `(alg s)⁻¹` is such a quotient, so it is also one for `m'`,
say `(alg s)⁻¹ * alg b = alg a` with `b ∉ m'`; multiplying by `alg s` and using injectivity gives
`b = s * a`, hence `s ∉ m'` (otherwise `s * a ∈ m'`, i.e. `b ∈ m'`). -/
theorem recover_prime_of_exists_mul_eq {S : Type*} [CommRing S] {K : Type*} [Field K]
    (alg : S →+* K) (hinj : Function.Injective alg) {m m' : Ideal S}
    (h : ∀ x : K, (∃ a b : S, b ∉ m ∧ x * alg b = alg a) ↔
                  (∃ a b : S, b ∉ m' ∧ x * alg b = alg a)) :
    m = m' := by
  have key : ∀ {n₁ n₂ : Ideal S},
      (∀ x : K, (∃ a b : S, b ∉ n₁ ∧ x * alg b = alg a) ↔
                (∃ a b : S, b ∉ n₂ ∧ x * alg b = alg a)) →
      ∀ s : S, s ∉ n₁ → s ∉ n₂ := by
    intro n₁ n₂ hh s hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hs (Ideal.zero_mem n₁)
    have halg : alg s ≠ 0 := fun h0 => hs0 (hinj (by rw [h0, map_zero]))
    -- `(alg s)⁻¹` lies in the set attached to `n₁`
    have hmem : ∃ a b : S, b ∉ n₁ ∧ (alg s)⁻¹ * alg b = alg a :=
      ⟨1, s, hs, by rw [inv_mul_cancel₀ halg, map_one]⟩
    obtain ⟨a, b, hb₂, heq⟩ := (hh ((alg s)⁻¹)).1 hmem
    intro hs₂
    apply hb₂
    have hbsa : b = s * a := by
      apply hinj
      have h1 : alg s * ((alg s)⁻¹ * alg b) = alg s * alg a := by rw [heq]
      rw [← mul_assoc, mul_inv_cancel₀ halg, one_mul, ← map_mul] at h1
      exact h1
    rw [hbsa]
    exact Ideal.IsTwoSided.mul_mem_of_left a hs₂
  apply le_antisymm
  · intro s hs
    by_contra hc
    exact key (fun x => (h x).symm) s hc hs
  · intro s hs
    by_contra hc
    exact key h s hc hs

end Work.SpecLin.Alt
