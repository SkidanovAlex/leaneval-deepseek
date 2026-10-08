import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

/-- **Additive monomials over `𝔽_{2ⁿ}` are Frobenius powers.**

If `x ↦ x ^ a` is additive on the field `𝔽_{2ⁿ}` then `a` is congruent to a power of `2` modulo
`2 ^ n - 1` (so the map is the `k`-th Frobenius `x ↦ x ^ (2 ^ k)`).

Used in Higman's Lemma 12 for the "abelian" constituent: the diagonal term `C' β ^ a'` of the
pinned squaring form has vanishing polar form exactly when `β ↦ β ^ a'` is additive.

Proof: `f x = x ^ a` is additive (hypothesis) and multiplicative (`(xy)^a = x^a y^a`) with
`f 1 = 1`, so `f` is an injective ring endomorphism of the field; the ring endomorphisms of
`𝔽_{2ⁿ}` are the Frobenius powers, so `x ^ a = x ^ (2 ^ k)` for all `x`, hence
`a ≡ 2 ^ k (mod 2 ^ n - 1)`.  (`a = 0` is excluded by the hypothesis at `x = y = 1`, since
`0 ^ 0 = 1 ≠ 1 + 1 = 0`; exhaustively verified for `n ≤ 5`.) -/
theorem pow_eq_frobenius_of_additive {n a : ℕ} (hn : 0 < n)
    (h : ∀ x y : GaloisField 2 n, (x + y) ^ a = x ^ a + y ^ a) :
    ∃ k : ℕ, a ≡ 2 ^ k [MOD 2 ^ n - 1] := by
  classical
  -- `a = 0` is impossible: the hypothesis at `x = 0`, `y = 1` gives `0 ^ a = 0`.
  have hz : (0 : GaloisField 2 n) ^ a = 0 := by
    have h1 := h 0 1
    simp only [zero_add, one_pow] at h1
    exact add_right_cancel (by rw [← h1, zero_add])
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, pow_zero] at hz
    exact one_ne_zero hz
  -- The additive monomial is a ring endomorphism of the field.
  let f : GaloisField 2 n →+* GaloisField 2 n :=
    { toFun := fun x => x ^ a
      map_one' := by simp
      map_mul' := by intro x y; rw [mul_pow]
      map_zero' := hz
      map_add' := fun x y => h x y }
  have hf_inj : Function.Injective f := RingHom.injective f
  have hf_bij : Function.Bijective f :=
    ⟨hf_inj, (Finite.injective_iff_surjective (f := f)).mp hf_inj⟩
  -- It is `𝔽₂`-linear, since any two ring homomorphisms out of `ZMod 2` agree.
  have hcomm : ∀ r : ZMod 2,
      (RingEquiv.ofBijective f hf_bij) (algebraMap (ZMod 2) (GaloisField 2 n) r)
        = algebraMap (ZMod 2) (GaloisField 2 n) r := by
    intro r
    have hcomp : f.comp (algebraMap (ZMod 2) (GaloisField 2 n))
        = algebraMap (ZMod 2) (GaloisField 2 n) := Subsingleton.elim _ _
    have hval := RingHom.congr_fun hcomp r
    rw [RingEquiv.ofBijective_apply]
    simpa using hval
  let g : GaloisField 2 n ≃ₐ[ZMod 2] GaloisField 2 n := AlgEquiv.ofRingEquiv hcomm
  have hg_apply : ∀ x : GaloisField 2 n, g x = x ^ a := by
    intro x
    change (AlgEquiv.ofRingEquiv hcomm) x = x ^ a
    rw [AlgEquiv.ofRingEquiv_apply, RingEquiv.ofBijective_apply]
    rfl
  -- Every `𝔽₂`-algebra automorphism of `𝔽_{2ⁿ}` is a power of Frobenius.
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 (GaloisField 2 n) g
  have hcard2 : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hpow : ∀ x : GaloisField 2 n, x ^ a = x ^ (2 ^ i) := by
    intro x
    have h2 := hi x
    rw [hg_apply x, hcard2] at h2
    exact h2
  -- Evaluate at a generator of the cyclic group of units.
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (GaloisField 2 n)ˣ)
  have horder : orderOf u = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units,
      GaloisField.card 2 n (Nat.pos_iff_ne_zero.mp hn)]
  have hupow : u ^ a = u ^ (2 ^ i) := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    exact hpow (u : GaloisField 2 n)
  exact ⟨i, by rw [← horder]; exact pow_eq_pow_iff_modEq.mp hupow⟩

end Work.Higman.Q3.L12
