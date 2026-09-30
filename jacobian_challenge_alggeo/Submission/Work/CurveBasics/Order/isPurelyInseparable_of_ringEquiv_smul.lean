import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

/-- Purely inseparability of an algebra extension is invariant under a compatible isomorphism of
the base ring: if `F` and `F'` are isomorphic commutative rings acting on the field `E` in the
same way (i.e. the structure maps agree along the isomorphism `e`), then `IsPurelyInseparable F E`
implies `IsPurelyInseparable F' E`. -/
theorem isPurelyInseparable_of_ringEquiv_smul {F F' E : Type*} [Field F] [Field F'] [Field E]
    [Algebra F E] [Algebra F' E] (e : F ≃+* F')
    (h : (algebraMap F' E).comp e.toRingHom = algebraMap F E) :
    IsPurelyInseparable F E → IsPurelyInseparable F' E := by
  -- Turn the ring isomorphism `e` into an `F`-algebra structure on `F'`.
  intro hpi
  let _ : Algebra F F' := e.toRingHom.toAlgebra
  -- The compatibility hypothesis `h` is exactly the scalar tower condition.
  have _ : IsScalarTower F F' E := IsScalarTower.of_algebraMap_eq fun x => by
    simpa [RingHom.algebraMap_toAlgebra] using (DFunLike.congr_fun h x).symm
  have _ : IsPurelyInseparable F E := hpi
  exact IsPurelyInseparable.tower_top F F' E

end Work.CurveBasics.Order
