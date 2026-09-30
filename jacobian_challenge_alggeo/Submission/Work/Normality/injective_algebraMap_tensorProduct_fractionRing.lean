import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normality

/-- If `A` is a flat `P`-algebra over a domain `P`, then `A` embeds into its base change to
the fraction field of `P`.

Proof sketch: the map in question is `Module.Flat.lTensor_preserves_injective_linearMap`
applied to the injective map `algebraMap P (FractionRing P)` (injective because `P` is a
domain), using `Module.Flat P A`, together with the identification
`A ⊗[P] P ≃ A`. -/
theorem injective_algebraMap_tensorProduct_fractionRing {P : Type*} [CommRing P]
    [IsDomain P] {A : Type*} [CommRing A] [Algebra P A] [Module.Flat P A] :
    Function.Injective (algebraMap A (TensorProduct P A (FractionRing P))) := by
  have hb : Function.Injective (algebraMap P (FractionRing P)) :=
    IsFractionRing.injective P (FractionRing P)
  have h := Algebra.TensorProduct.includeLeft_injective (R := P) (S := A) (A := A)
    (B := FractionRing P) hb
  have hmap : ⇑(algebraMap A (TensorProduct P A (FractionRing P))) =
      ⇑(Algebra.TensorProduct.includeLeft (R := P) (S := A) (A := A)
        (B := FractionRing P)) := by
    funext a
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.algebraMap_self_apply]
  rw [hmap]
  exact h

end Work.Normality
