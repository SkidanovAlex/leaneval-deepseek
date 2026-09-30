import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Packaging.Trivial

universe u

open CategoryTheory AlgebraicGeometry

/-- `Spec k` is geometrically irreducible over `k` for a field `k`: the identity morphism
`𝟙 (Spec k)` is geometrically irreducible, because pulling back along an identity is an isomorphism,
so for every field `K` and every `x : Spec K ⟶ Spec k` the base change `pullback (𝟙 _) x` is
isomorphic to `Spec K`, which is irreducible. This is the trivial-branch instance needed for the
Jacobian packaging. A proof along these lines (which also works for `𝟙 S` for any scheme `S`):

```lean
rw [GeometricallyIrreducible.eq_geometrically, geometrically_iff_of_isClosedUnderIsomorphisms]
intro K _ y
exact ObjectProperty.prop_of_iso (fun X : Scheme => IrreducibleSpace X)
  (IsPullback.of_id_snd (f := y)).isoPullback
  (inferInstance : IrreducibleSpace (Spec (.of K)))
```
-/
theorem geometricallyIrreducible_one {k : Type u} [Field k] :
    GeometricallyIrreducible (𝟙 (Spec (.of k))) := by
  rw [GeometricallyIrreducible.eq_geometrically, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  exact ObjectProperty.prop_of_iso (fun X : Scheme => IrreducibleSpace X)
    (IsPullback.of_id_snd (f := y)).isoPullback
    (inferInstance : IrreducibleSpace (Spec (.of K)))

end Work.Packaging.Trivial
