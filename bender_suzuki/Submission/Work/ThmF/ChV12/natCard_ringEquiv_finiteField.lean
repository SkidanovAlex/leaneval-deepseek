import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.natCard_ringEquiv_finiteField`

The automorphism group of a finite field `F` of characteristic `2` with `|F| = 2 ^ n` has exactly
`n` elements.

Every ring automorphism of a field fixes `1`, hence the prime field `𝔽₂ = ZMod 2`, so it is
automatically an `𝔽₂`-algebra automorphism.  Thus `F ≃+* F` is in bijection with `Gal(F/𝔽₂)`,
whose cardinality is `finrank (𝔽₂) F` by `IsGalois.card_aut_eq_finrank`.  Finally
`FiniteField.pow_finrank_eq_natCard` gives `2 ^ finrank (𝔽₂) F = |F| = 2 ^ n`, whence the
`𝔽₂`-dimension -- and with it the number of automorphisms -- equals `n`.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

theorem natCard_ringEquiv_finiteField {F : Type*} [Field F] [Finite F] [CharP F 2] (n : ℕ)
    (h : Nat.card F = 2 ^ n) : Nat.card (F ≃+* F) = n := by
  -- view `F` as an algebra over its prime field `𝔽₂ = ZMod 2`
  haveI : Algebra (ZMod 2) F := ZMod.algebra F 2
  -- every ring automorphism of `F` fixes `1`, hence `𝔽₂`, hence is `𝔽₂`-linear: `F ≃+* F ≃ Gal(F/𝔽₂)`
  have hbij : Nat.card (F ≃+* F) = Nat.card (F ≃ₐ[ZMod 2] F) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun σ =>
          { toRingEquiv := σ
            commutes' := fun a => by
              obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
              simp }
        invFun := fun e => AlgEquiv.toRingEquiv e
        left_inv := fun σ => by ext x; rfl
        right_inv := fun e => by ext x; rfl }
  rw [hbij, IsGalois.card_aut_eq_finrank]
  -- the `𝔽₂`-dimension of `F` is `n`, since `|F| = 2 ^ n`
  have h2 : (2 : ℕ) ^ Module.finrank (ZMod 2) F = 2 ^ n := by
    rw [FiniteField.pow_finrank_eq_natCard]
    exact h
  exact Nat.pow_right_injective (a := 2) (by norm_num) h2

end Work.ThmF.ChV12
