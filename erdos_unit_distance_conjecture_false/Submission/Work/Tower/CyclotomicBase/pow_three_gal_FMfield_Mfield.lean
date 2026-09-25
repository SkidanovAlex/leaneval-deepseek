import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.exists_mulEquiv_Mfield_gal

namespace Work.Tower.CyclotomicBase

/-- The Galois group of `M/F` has exponent `3`: every element of `Gal(M/F)` is annihilated by `3`.

Indeed `Gal(M/ℚ) ≃* (ℤ/3)^ℓ` (`exists_mulEquiv_Mfield_gal`), and any automorphism of `M` fixing
`F` is in particular a `ℚ`-algebra automorphism (the forgetful map
`AlgEquiv.restrictScalarsHom ℚ : Gal(M/F) →* Gal(M/ℚ)` is injective, being the identity on
underlying maps).  Since every element of the target group `(Fin ℓ → Multiplicative (ZMod 3))`
is annihilated by `3`, so is every element of `Gal(M/F)`. -/
theorem pow_three_gal_FMfield_Mfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)]
    (σ : Gal(↥(Mfield r hr hr3)/↥(FMfield r hr hr3))) : σ ^ 3 = 1 := by
  obtain ⟨e⟩ := exists_mulEquiv_Mfield_gal r hr hr3 hrinj
  -- An `F`-automorphism of `M` is a fortiori a `ℚ`-automorphism; this map is injective.
  apply AlgEquiv.restrictScalarsHom_injective (R := ℚ) (S := ↥(FMfield r hr hr3))
    (A := ↥(Mfield r hr hr3))
  -- Transport to `Gal(M/ℚ) ≃* (ℤ/3)^ℓ`, where every element has order dividing `3`.
  apply e.injective
  simp only [map_pow, map_one]
  funext i
  simp only [Pi.pow_apply, Pi.one_apply]
  have h := pow_card_eq_one (x := e (AlgEquiv.restrictScalarsHom ℚ σ) i)
  rwa [Fintype.card_multiplicative, ZMod.card 3] at h

end Work.Tower.CyclotomicBase
