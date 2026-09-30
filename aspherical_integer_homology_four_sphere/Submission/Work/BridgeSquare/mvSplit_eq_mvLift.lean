/-
# `BridgeSquare/mvSplit_eq_mvLift.lean` — the two descriptions of the first Mayer–Vietoris map

`Work.BridgeSquare.mvSplit k` is the *left* half of the Mayer–Vietoris map of the cover
`M̂ = A ∪ B`, written through the explicit additivity isomorphism of homology
(`Work.BridgeSquare.biprodHomology`):

`mvSplit k = mvFhat k ≫ (biprodHomology K_A K_B k).hom`,

while `Work.BridgeSquare.mvLift k` is the same map written directly as the pair of the two maps
induced by the inclusions `A ∩ B ↪ A` and `A ∩ B ↪ B` (`biprod.lift`).

The two descriptions agree: `(biprodHomology K_A K_B k).hom` is, by construction, the map
`biprod.lift (H_k(biprod.fst)) (H_k(biprod.snd))`, so the composite with `H_k(mvLeft)` is
`biprod.lift (H_k(mvLeft ≫ biprod.fst)) (H_k(mvLeft ≫ biprod.snd))` (`homologyMap_comp`), and the
two components are the inclusions by definition of `mvLeft` (`biprod.lift_fst`, `biprod.lift_snd`).

The proof is pure bookkeeping in the category of `ℤ`-modules; the only care needed is that the
singular chain complex of a topological space has two definitionally equal presentations
(`SSet.chainComplexMap (TopCat.toSSet.map f) ℤ` versus `Work.Cohomology.chainMap ℤ X Y f`), so the
`rfl`-lemma `mvLeft_eq_biprod_lift` below rewrites `mvLeft` into the presentation of its *declared*
type before the abstract manipulations are performed.
-/
import Mathlib
import Submission.Work.BridgeSquare.Spaces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open LeanEval.Topology

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  A presentation lemma for `mvLeft` -/

/-- **`mvLeft` in the presentation of its declared type.**  The body of `Work.Cohomology.mvLeft`
uses `SSet.chainComplexMap (TopCat.toSSet.map ·) ℤ`, while its declared type is stated with
`Work.Cohomology.chainMap`; this `rfl`-lemma rewrites the definition to the latter form, so that the
subsequent abstract manipulations see a term that is syntactically a morphism between the modules
named in the type. -/
lemma mvLeft_eq_biprod_lift {X : TopCat} (U V : Set X) :
    Work.Cohomology.mvLeft U V
      = (biprod.lift
          (Work.Cohomology.chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (Work.Cohomology.inclUVU U V))
          (Work.Cohomology.chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V) (Work.Cohomology.inclUVV U V))
        : Work.Cohomology.singularChains ℤ (TopCat.of ↥(U ∩ V)) ⟶
            (Work.Cohomology.singularChains ℤ (TopCat.of U)) ⊞
              (Work.Cohomology.singularChains ℤ (TopCat.of V))) := rfl

/-! ## §2  The identity, for an arbitrary cover `U, V` -/

/-- **The composite `H_k(mvLeft) ≫ (biprodHomology _ _ k).hom` is `biprod.lift` of the two
components of `mvLeft`.**  This is the abstract content of `mvSplit_eq_mvLift`, stated for an
arbitrary pair of subsets so that no identification of spaces enters the proof. -/
theorem homologyMap_mvLeft_comp_biprodHomology {X : TopCat} (U V : Set X) (k : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.mvLeft U V) k
      ≫ (biprodHomology (Work.Homology.singChain Work.Homology.ZMod (TopCat.of U))
          (Work.Homology.singChain Work.Homology.ZMod (TopCat.of V)) k).hom
    = biprod.lift
        (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U)
            (Work.Cohomology.inclUVU U V)) k)
        (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V)
            (Work.Cohomology.inclUVV U V)) k) := by
  rw [mvLeft_eq_biprod_lift]
  rw [show (biprodHomology (Work.Homology.singChain Work.Homology.ZMod (TopCat.of U))
          (Work.Homology.singChain Work.Homology.ZMod (TopCat.of V)) k).hom
        = biprod.lift (homologyMap (biprod.fst) k) (homologyMap (biprod.snd) k) from rfl]
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, biprod.lift_fst, ← HomologicalComplex.homologyMap_comp,
      biprod.lift_fst]
  · rw [Category.assoc, biprod.lift_snd, biprod.lift_snd, ← HomologicalComplex.homologyMap_comp,
      biprod.lift_snd]

/-! ## §3  The lemma requested by the bridge -/

theorem mvSplit_eq_mvLift [rt : Work.Space.RTData] (k : ℕ) :
    Work.BridgeSquare.mvSplit (rt := rt) k = Work.BridgeSquare.mvLift (rt := rt) k := by
  rw [mvSplit, mvLift, Work.HomologyIso.mvFhat, Work.Final.mvF]
  exact homologyMap_mvLeft_comp_biprodHomology (X := Work.HomologyIso.Xhat (rt := rt))
    (Work.HomologyIso.Aset (rt := rt)) (Work.HomologyIso.Bset (rt := rt)) k

end

end Work.BridgeSquare
