/-
# `BridgeSquare/compatA.lean` — the `A`-side of the bridge square

`Work.BridgeSquare.mvA` and `Work.BridgeSquare.cuspA` are the two composites
`H_k(A ∩ B) → H_k(M̄)` of the bridge square (see `Submission/Work/BridgeSquare/Spaces.lean`):

* `mvA` is the map induced by the inclusion `A ∩ B ↪ A` followed by the retraction
  `H_k(A) ≅ H_k(M̄)` of the explicit homotopy equivalence `Work.Space.Split.eACompat`;
* `cuspA` is the radial rescaling `H_k(A ∩ B) ≅ H_k(⊔_v ∂[-1,1]² × T²_v)` of
  `Work.Space.Split.eABACompat` followed by the cusp parametrisation `H_k(τ)`.

They are equal because the two underlying maps of spaces are *equal* (not merely homotopic) for the
natural retractions: `Work.Space.Split.eACompat_comp_inclAB_A_eq` states
`eACompat ∘ inclAB_A = tauBdry ∘ eABACompat` as continuous maps.  Transporting this equality
through the singular chain functor and the homology functor gives the statement.
-/
import Mathlib
import Submission.Work.BridgeSquare.Spaces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory HomologicalComplex

namespace Work.BridgeSquare

/-- The equality `Work.Space.Split.eACompat_comp_inclAB_A_eq` of continuous maps, read as an
equality of the corresponding morphisms of `TopCat`: the inclusion `A ∩ B ↪ A` followed by the
retraction `A ≃ₕ M̄` agrees with the cusp parametrisation `τ` preceded by the radial rescaling
`A ∩ B ≃ₕ ⊔_v ∂[-1,1]² × T²_v`. -/
theorem inclA_comp_eACompat_eq_tauBdry_comp_eABACompat [rt : Work.Space.RTData] :
    inclA (rt := rt) ≫ (TopCat.ofHom (Work.Space.Split.eACompat rt.core).toFun) =
      (TopCat.ofHom (Work.Space.Split.eABACompat rt.core).toFun) ≫
        (TopCat.ofHom rt.core.tauBdry) :=
  congrArg TopCat.ofHom (Work.Space.Split.eACompat_comp_inclAB_A_eq rt.core)

theorem compatA [rt : Work.Space.RTData] (k : ℕ) :
    Work.BridgeSquare.mvA (rt := rt) k = Work.BridgeSquare.cuspA (rt := rt) k := by
  -- the two composites of spaces agree, so the two composites of chain maps do, too
  have hcomp : inclA (rt := rt) ≫ (TopCat.ofHom (Work.Space.Split.eACompat rt.core).toFun) =
      (TopCat.ofHom (Work.Space.Split.eABACompat rt.core).toFun) ≫
        (TopCat.ofHom rt.core.tauBdry) :=
    inclA_comp_eACompat_eq_tauBdry_comp_eABACompat (rt := rt)
  -- unfold the two sides: both are composites of `homologyMap`s of `chainMap`s
  simp only [mvA, cuspA, isoA, isoABA, intHomologyIsoOfHomotopyEquiv, CategoryTheory.asIso]
  -- reassemble each composite into the single induced map of the composite of chain maps
  set_option backward.isDefEq.respectTransparency false in
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  -- and each composite of chain maps as the chain map induced by the composite of maps
  simp only [Work.Cohomology.chainMap, ← Functor.map_comp]
  rw [hcomp]

end Work.BridgeSquare
