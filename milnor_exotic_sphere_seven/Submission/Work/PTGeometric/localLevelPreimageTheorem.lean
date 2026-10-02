import Mathlib
import Submission.Work.PTGeometric.LocalLevel
import Submission.Work.PTGeometric.Lvl.Manifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

/-- **G4 of the PTGEOMETRIC blueprint: the local level-set preimage theorem.**

`Work.PTGeometric.LocalLevelPreimageTheorem k` says: a **closed** subset `W` of a compact `T2` smooth
`(9+k)`-manifold `M` with boundary (modelled on the half-space `𝓡∂ ((8+k)+1)`) which is *locally* the
zero set of a smooth submersion to `ℝ^k` (`LocalLevelData k M W`: at every `x ∈ W` there is an open
`U x ∋ x` and a smooth `g x : M → ℝ^k` with `W ∩ U x = (g x)⁻¹' {0}`, `g x` a submersion at `x`, and
the restriction of `g x` to `∂M` a submersion at every boundary point of `W`) is a compact `T2` smooth
`9`-manifold with boundary whose boundary is `W ∩ ∂M`.

The closedness hypothesis is *not* redundant: the local data alone only make `W` locally a level set,
so for `k = 0` an open subset of a compact boundaryless `9`-manifold (e.g. `W = S⁹ ∖ {pt} ⊆ M = S⁹`)
satisfies them without being compact.  In the application `W = F ⁻¹' X.core` is closed because the
core of a `LocalCoreTarget` is closed (`LocalCoreTarget.isClosed_core`) and `F` is continuous
(`Work.PTGeometric.localPreimageTheorem_of_level`).

The *global* form of this theorem (one `g : M → ℝ^k` with `W = g ⁻¹' {0}`, which is a stronger
hypothesis: it forces the normal bundle of `W` to be trivial) is already **proved** in the workspace:
`Work.ThomBordism.Transversality.Preimage.exists_preimage_structure`, whose proof (in
`Submission/Work/ThomBordism/Transversality/Preimage/`: `Setup.lean`, `Chart.lean`, `Transition.lean`,
`KeyLemma.lean`, `Manifold.lean`, `exists_preimage_structure.lean`) builds the charts of `W` from the
submersion normal form of `g` at each point and proves that they are compatible.  The task here is to
obtain the **local** form by the same argument with the global `g` replaced by the local `g x` at each
point: the chart at `x ∈ W` uses the submersion normal form of `g x` at `x` (submersivity is open, so
the chart domain may be shrunk to where `g x` is submersive), and the transition function between the
charts at two points `x, x'` is smooth because both use submersions with the same zero set near a
common point of `W`.  A good route is to copy the files listed above into your own directory
(`Submission/Work/PTGeometric/`, namespace `Work.PTGeometric`) and replace the single global `coreMap`
by the point-dependent `g x` of `LocalLevelData` (the dimension bookkeeping is unchanged: `M` is
modelled on `𝓡∂ ((8+k)+1)` and `W` is `9`-dimensional, exactly as in those files, and the boundary
condition `bndSubmersion` is the same one as the chapter's `CoreSetup.bndSubmersion`). -/
theorem localLevelPreimageTheorem (k : ℕ) : Work.PTGeometric.LocalLevelPreimageTheorem k := by
  intro M _ _ _ _ _ W hcl D
  let S : Lvl.Setup k :=
    { M := M, W := W, compactSpace := inferInstance, t2Space := inferInstance,
      isClosed_W := hcl, data := D }
  refine ⟨S.Pre, inferInstance, Lvl.Setup.instChartedSpace S, Lvl.Setup.instIsManifold S,
    Lvl.Setup.instCompactSpace S, inferInstance, Homeomorph.refl S.Pre, ?_⟩
  intro w
  rw [Lvl.Setup.mem_boundary_iff S w, Set.mem_inter_iff]
  exact ⟨fun h => ⟨h, w.2⟩, fun h => h.1⟩

end Work.PTGeometric
