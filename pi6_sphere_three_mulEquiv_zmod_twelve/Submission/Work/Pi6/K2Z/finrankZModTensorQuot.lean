import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.style.haveILetI false

/-!
# `ZMod p ⊗[ℤ] (ℤ ⧸ (q))` when `q` is a multiple of the prime `p`

If the prime `p` divides `q`, then `p` acts trivially on `ZMod p`, hence the ideal `(q) ⊆ ℤ`
maps to `0` under `algebraMap ℤ (ZMod p)`.  By the base-change isomorphism
`Ideal.qoutMapEquivTensorQout` (`S ⧸ I·S ≃ₗ[S] S ⊗[R] R ⧸ I`) this says that
`ZMod p ⊗[ℤ] (ℤ ⧸ (q))` is the zero quotient of `ZMod p`, i.e. `ZMod p` itself, which is
one-dimensional over the field `ZMod p`.

This is the coefficient computation used in the mod-`p` base-change/forcing arguments
(`K2Z`/`EMM2`) of the `π₆(S³) = ℤ/12` computation.
-/

namespace Work.Pi6.K2Z

theorem finrankZModTensorQuot (p : ℕ) (hp : p.Prime) (q : ℤ) (hq : (p : ℤ) ∣ q) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (ℤ ⧸ Ideal.span ({q} : Set ℤ))) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p` acts trivially on `ZMod p`, so the ideal `(q)` maps to `⊥`.
  have hmap : (Ideal.span ({q} : Set ℤ)).map (algebraMap ℤ (ZMod p)) = ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_bot]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd q p).mpr hq
  -- Base change: `ZMod p ⊗[ℤ] (ℤ ⧸ (q)) ≃ₗ[ZMod p] ZMod p ⧸ (q).map (algebraMap ℤ (ZMod p))`.
  rw [← (Ideal.qoutMapEquivTensorQout (R := ℤ) (S := ZMod p)
        (I := Ideal.span ({q} : Set ℤ))).finrank_eq, hmap]
  rw [LinearEquiv.finrank_eq (Submodule.quotEquivOfEqBot (⊥ : Submodule (ZMod p) (ZMod p)) rfl),
    Module.finrank_self]

end Work.Pi6.K2Z
