/-
# `BridgeSquare/cuspPair_P_surjective.lean` — surjectivity of the second component `P_k = H_k(π)`

`Work.BridgeSquare.cuspPair` is `biprod.lift (H_k τ) (H_k π)`, and this file proves that its second
component `Work.BridgeSquare.homMap projMap k` is **surjective**, for every degree `k`.

The proof is the section of `CuspPair.lean` §2: choose a basepoint `p₀` of the square boundary and
let `secMap p₀ : ⊔_v T²_v → ⊔_v (∂[-1,1]² × T²_v)` be `⟨v, y⟩ ↦ ⟨v, (p₀, y)⟩`.  Then

```
projMap ∘ secMap = id
```

(definitionally: `π ⟨v,(p₀,y)⟩ = ⟨v,y⟩`), hence on homology

`H_k(π) ∘ H_k(secMap) = H_k(id) = id`,

so `H_k(π)` is a split epimorphism and therefore surjective.  This is the "`B`-half is formal" part
of the residual of the bridge (see `Submission/Work/BridgeSquare/NOTES.md` §4): with it, the
`B`-block of the cusp square can be normalised by choosing the `λ`-part of the cusp bases.
-/
import Mathlib
import Submission.Work.BridgeSquare.CuspPair

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  A basepoint of the square boundary -/

/-- The corner `(1,1)` of `[-1,1]²`, as a point of the boundary `∂[-1,1]²` (whence of
`Work.Space.Split.BdryPt`): a basepoint for the section `secMap`. -/
def cornerBdryPt : Work.Space.Split.BdryPt :=
  ⟨⟨Work.Space.Assembly.sqCorner, Work.Space.Assembly.sqCorner_mem⟩,
    Work.Space.Assembly.sqNorm_sqCorner⟩

/-! ## §2  The section is a section of the projection -/

/-- **`π ∘ secMap = id`** on `⊔_v T²_v`: the projection forgetting the boundary coordinate is a
retraction of the section at the corner `p₀`. -/
theorem secMap_comp_projMap [rt : Work.Space.RTData] :
    secMap (rt := rt) cornerBdryPt ≫ projMap (rt := rt) = 𝟙 (Top (rt := rt)) := by
  rw [projMap, secMap, ← TopCat.ofHom_comp]
  congr 1

/-- The same equality at the level of the induced chain maps. -/
theorem chainMap_secMap_comp_projMap [rt : Work.Space.RTData] :
    Work.Cohomology.chainMap ℤ (Top (rt := rt)) (Cop (rt := rt))
        (secMap (rt := rt) cornerBdryPt)
      ≫ Work.Cohomology.chainMap ℤ (Cop (rt := rt)) (Top (rt := rt)) (projMap (rt := rt))
      = 𝟙 _ := by
  simp only [Work.Cohomology.chainMap, ← Functor.map_comp]
  rw [secMap_comp_projMap]
  simp

/-- **The induced map on integral homology is a split epimorphism**: `H_k(π) ∘ H_k(secMap) = id`
for every `k`. -/
theorem homMap_secMap_comp_projMap [rt : Work.Space.RTData] (k : ℕ) :
    homMap (secMap (rt := rt) cornerBdryPt) k ≫ homMap (projMap (rt := rt)) k = 𝟙 _ := by
  simp only [homMap]
  erw [← HomologicalComplex.homologyMap_comp]
  rw [chainMap_secMap_comp_projMap]
  exact HomologicalComplex.homologyMap_id _ k

/-! ## §3  The surjectivity -/

/-- **`P_k = H_k(π)` is surjective**: the `B`-component of the cusp pair `F_k = (H_k τ, H_k π)` has
the section `H_k(secMap p₀)` of `P_k`. -/
theorem cuspPair_P_surjective [rt : Work.Space.RTData] (k : ℕ) :
    Function.Surjective
      (Work.BridgeSquare.homMap (Work.BridgeSquare.projMap (rt := rt)) k).hom := by
  intro y
  refine ⟨(homMap (secMap (rt := rt) cornerBdryPt) k).hom y, ?_⟩
  have hfun := ConcreteCategory.congr_hom (homMap_secMap_comp_projMap (rt := rt) k) y
  simp only [ModuleCat.comp_apply] at hfun
  simpa using hfun

end

end Work.BridgeSquare
