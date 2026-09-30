import Mathlib
import Submission.Work.BridgeSquare.Explicit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Composition of homotopy-equivalence-induced homology isomorphisms

`Work.BridgeSquare.intHomologyIsoOfHomotopyEquiv` sends a homotopy equivalence
`e : X ≃ₕ Y` to the isomorphism `H_k(X) ≅ H_k(Y)` induced on integral homology by the
*forward* map of `e`.  Because the construction is definitionally the map induced by a chain
map, it is functorial: the isomorphism attached to a composite homotopy equivalence is the
composite of the isomorphisms attached to the factors.

That is the content of `intHomologyIsoOfHomotopyEquiv_trans` below.  It is what makes the
identifications of `BridgeSquare/Explicit.lean` usable *as identifications*: an isomorphism
built out of the pieces can be compared with the isomorphism of an assembled homotopy
equivalence, because both are recognised by their forward maps
(`intHomologyIsoOfHomotopyEquiv_hom`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.BridgeSquare

/-- The forward map of `intHomologyIsoOfHomotopyEquiv e k` is the map induced on homology by the
chain map of the forward map of `e`. -/
theorem intHomologyIsoOfHomotopyEquiv_hom {X Y : TopCat}
    (e : ContinuousMap.HomotopyEquiv ↥X ↥Y) (k : ℕ) :
    (intHomologyIsoOfHomotopyEquiv e k).hom =
      HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y (TopCat.ofHom e.toFun)) k :=
  rfl

/-- **Functoriality of the homology isomorphism attached to a homotopy equivalence**: the
isomorphism of a composite homotopy equivalence `e ≃ₕ f` is the composite of the isomorphisms of
`e` and `f`.  Both sides are compared through their forward maps, which are the homology maps of
the chain maps of `e.toFun`, `f.toFun` and `(e.trans f).toFun`. -/
theorem intHomologyIsoOfHomotopyEquiv_trans {X Y Z : TopCat}
    (e : ContinuousMap.HomotopyEquiv ↥X ↥Y) (f : ContinuousMap.HomotopyEquiv ↥Y ↥Z) (k : ℕ) :
    Work.BridgeSquare.intHomologyIsoOfHomotopyEquiv (e.trans f) k
      = Work.BridgeSquare.intHomologyIsoOfHomotopyEquivComp e f k := by
  -- Compare the two isomorphisms through their forward maps.
  apply CategoryTheory.Iso.ext
  simp only [Work.BridgeSquare.intHomologyIsoOfHomotopyEquiv,
    Work.BridgeSquare.intHomologyIsoOfHomotopyEquivComp, CategoryTheory.Iso.trans_hom,
    CategoryTheory.asIso_hom]
  -- Functoriality of `homologyMap`, then functoriality of the induced chain maps.
  rw [← HomologicalComplex.homologyMap_comp]
  simp only [Work.Cohomology.chainMap, ← CategoryTheory.Functor.map_comp, ← TopCat.ofHom_comp]
  rfl

end Work.BridgeSquare
