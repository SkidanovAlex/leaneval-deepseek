import Mathlib
import Submission.Work.BridgeSquare.Spaces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false



open LeanEval.Topology CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology
namespace Work.BridgeSquare

/-- The two composites `B`-side agree at the level of topological morphisms: the inclusion
`A ∩ B ↪ B` followed by the collar retraction `eBCompat : B ≃ₕ ⊔_v T²_v` equals the annulus
rescaling `eABCompat : A ∩ B ≃ₕ ⊔_v (∂[-1,1]² × T²_v)` followed by the projection `projBdry`
forgetting the boundary coordinate.  This is `Work.Space.Split.eBCompat_comp_inclAB_B_eq`
transposed to `TopCat`. -/
theorem compatB_mor [rt : Work.Space.RTData] :
    TopCat.ofHom (Work.Space.Assembly.inclAB_B rt.core) ≫
        TopCat.ofHom (Work.Space.Split.eBCompat rt.core).toFun
      = TopCat.ofHom (Work.Space.Split.eABCompat rt.core).toFun ≫
        TopCat.ofHom (Work.Space.Assembly.projBdry rt.core) := by
  rw [← TopCat.ofHom_comp, ← TopCat.ofHom_comp, Work.Space.Split.eBCompat_comp_inclAB_B_eq]

/-- **The `B`-side of the bridge square.**  In the explicit identifications of the pieces, the
`B`-component of the Mayer--Vietoris map equals the cusp map obtained by rescaling the collar
annulus onto the boundary of the square and then projecting away the boundary coordinate.  Both
sides are the map induced on homology by `(v, t) ↦ (v, t)` on the five cusps. -/
theorem compatB [rt : Work.Space.RTData] (k : ℕ) :
    Work.BridgeSquare.mvB (rt := rt) k = Work.BridgeSquare.cuspB (rt := rt) k := by
  -- The chain-level compatibility of the two composites.
  have hchain : Work.Cohomology.chainMap ℤ (Iop (rt := rt)) (Bop (rt := rt))
        (TopCat.ofHom (Work.Space.Assembly.inclAB_B rt.core))
      ≫ Work.Cohomology.chainMap ℤ (Bop (rt := rt)) (Top (rt := rt))
        (TopCat.ofHom (Work.Space.Split.eBCompat rt.core).toFun)
      = Work.Cohomology.chainMap ℤ (Iop (rt := rt)) (Cop (rt := rt))
        (TopCat.ofHom (Work.Space.Split.eABCompat rt.core).toFun)
      ≫ Work.Cohomology.chainMap ℤ (Cop (rt := rt)) (Top (rt := rt))
        (TopCat.ofHom (Work.Space.Assembly.projBdry rt.core)) := by
    simp only [Work.Cohomology.chainMap, ← Functor.map_comp]
    rw [compatB_mor]
  -- The two identifications are induced by the forward maps of the homotopy equivalences.
  have h1 : (Work.BridgeSquare.isoB (rt := rt) k).hom =
      HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (Bop (rt := rt)) (Top (rt := rt))
        (TopCat.ofHom (Work.Space.Split.eBCompat rt.core).toFun)) k := rfl
  have h2 : (Work.BridgeSquare.isoInter (rt := rt) k).hom =
      HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (Iop (rt := rt)) (Cop (rt := rt))
        (TopCat.ofHom (Work.Space.Split.eABCompat rt.core).toFun)) k := rfl
  rw [Work.BridgeSquare.mvB, Work.BridgeSquare.cuspB, h1, h2,
      Work.BridgeSquare.inclB, Work.BridgeSquare.projMap]
  -- Functoriality of `homologyMap`, then the chain-level compatibility.
  erw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  rw [hchain]

end Work.BridgeSquare
