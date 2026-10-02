import Submission.Work.PTGeometric.localLevelPreimageTheorem
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.ThomBordism.Interface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the endgame in the local level-set formulation

The preimage theorem produces the null-bordism from a **closed** subset `W` of the source which is
locally cut out by smooth submersions (`Work.PTGeometric.LocalLevelData`), together with an
orientation datum of the situation.  This is the level-set form of
`Work.PTGeometric.exists_nullBordismFamily_of_genuineData`: the manifold structure of the preimage
comes from the *local* preimage theorem (`Work.PTGeometric.localLevelPreimageTheorem`) rather than from
a global defining function, which is what the genuine (non-trivial normal bundle) Pontryagin–Thom
construction needs.

## The model of `W`

The preimage theorem builds the manifold **explicitly** from the local data: the underlying type is
`↥W` and the charts are the submersion normal forms (`Submission/Work/PTGeometric/Lvl/`).  This file
uses that canonical model (`Work.PTGeometric.levelModel`), so the orientation datum it consumes is a
statement about *one* explicit manifold, not about every smooth model of the space `W` — see
`Work.PTGeometric.LevelOrientationData` for why that distinction is essential.

## Main result

* `Work.PTGeometric.exists_nullBordismFamily_of_levelData`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-- **The endgame in the local level-set formulation.**

A closed subset `W` of a compact `T2` smooth `(8 + k + 1)`-manifold with boundary carrying local
level-set data, whose boundary part is identified with the disjoint union of the pieces of a finite
family, and which carries the orientation datum of the situation on its **canonical model**
(`Work.PTGeometric.LevelOrientationData`: a relative fundamental class of the canonical model which is
a local generator at every interior point and whose boundary is the sum of the pieces' fundamental
classes), is a null-bordism of the family. -/
theorem exists_nullBordismFamily_of_levelData {k : ℕ} (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt))
    (orient : let S : Lvl.Setup k := levelSetup W hWcl L
      letI := Lvl.Setup.instChartedSpace S
      letI := Lvl.Setup.instIsManifold S
      letI := Lvl.Setup.instCompactSpace S
      ∃ (bdryPreimage : ((𝓡∂ 9).boundary S.Pre) ≃ₜ
            ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M))
        (w : (Work.Cohomology.relChains (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre)).homology 9),
        (∀ (x : S.Pre) (hx : x ∉ (𝓡∂ 9).boundary S.Pre),
          Submodule.span ℤ {(HomologicalComplex.homologyMap
            (Work.ThomBordism.relChainsInclPunct (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre) x hx)
            9 w)} = ⊤) ∧
        (Work.Cohomology.hPairδ (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre) 8 w
          = ∑ i, HomologicalComplex.homologyMap
              (Work.Cohomology.chainMap ℤ (Fam i).X
                (TopCat.of ((𝓡∂ 9).boundary S.Pre))
                (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
                  (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c)) :
    Nonempty (NullBordismFamily ι Fam) := by
  classical
  let S : Lvl.Setup k := levelSetup W hWcl L
  letI := Lvl.Setup.instChartedSpace S
  letI := Lvl.Setup.instIsManifold S
  letI := Lvl.Setup.instCompactSpace S
  haveI : IsManifold (𝓡∂ 9) 1 S.Pre := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨bdryPreimage, w, hwf, hwh⟩ := orient
  exact ⟨{ W := S.Pre, bdry := bdryPreimage.trans e, w := w, hw := hwh, w_fund := hwf }⟩

end

end Work.PTGeometric
