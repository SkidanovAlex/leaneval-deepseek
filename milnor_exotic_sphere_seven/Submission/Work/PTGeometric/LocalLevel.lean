import Submission.Work.PTGeometric.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the local level-set form of the preimage theorem

The geometric theorem that the transverse preimage of a codimension-`k` submanifold is a manifold with
boundary is, in the form actually used, only a statement about a **set** `W ⊆ M`:

> if `W` is locally the zero set of a smooth submersion to `ℝ^k` (and the boundary restriction is
> submersive at the boundary points of `W`), then `W` is a compact smooth `(9)`-manifold with boundary
> whose boundary is `W ∩ ∂M`.

This is the honest local form of
`Work.ThomBordism.Transversality.Preimage.exists_preimage_structure` (which is *proved*, but for a
*global* defining function `Φ : E → ℝ^k` — i.e. for a target whose normal bundle is trivial).  For the
genuine Grassmannian bundle there is no global defining function, so the local form is what the
Pontryagin–Thom construction consumes; the two files split the work:

* `Work.PTGeometric.localLevelData_of_coreTransverse` — *proved here*: a smooth map transverse to the
  core of a `LocalCoreTarget`, with boundary transversality, gives the local level-set data of its
  preimage (this is the extraction of the chart-by-chart data from the chart-by-chart definition);
* `Work.PTGeometric.LocalLevelPreimageTheorem` — the geometric gluing theorem (delegated): the local
  level-set data give the manifold structure;
* `Work.PTGeometric.localPreimageTheorem` — the local preimage theorem `LocalPreimageTheorem` of
  `Defs.lean`, from the two.

## Main definitions

* `Work.PTGeometric.LocalLevelData`
* `Work.PTGeometric.LocalLevelPreimageTheorem`

## Main results

* `Work.PTGeometric.localLevelData_of_coreTransverse`
* `Work.PTGeometric.localPreimageTheorem`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-- **Local level-set data for a codimension-`k` subset of a compact `(9+k)`-manifold with
boundary.**

`W` is a subset of `M` such that every point `x` of `W` has an open neighbourhood `U x ∋ x` on which
`W` is the zero set of a smooth `g x : M → ℝ^k` which is a submersion at `x`; and at the boundary
points of `W` the restriction of `g x` to `∂M` is a submersion at `x` as well.

This is exactly the local data a transverse map `F : M → E` into a `LocalCoreTarget` produces for its
preimage (`localLevelData_of_coreTransverse`), and exactly what the preimage theorem needs
(`LocalLevelPreimageTheorem`). -/
structure LocalLevelData (k : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (W : Set M) where
  /-- the neighbourhood of the point of `W` on which `W` is cut out -/
  U : W → Set M
  /-- it is open -/
  isOpen_U : ∀ x : W, IsOpen (U x)
  /-- it contains its centre -/
  mem_U : ∀ x : W, (x : M) ∈ U x
  /-- the local defining function -/
  g : W → M → EuclideanSpace ℝ (Fin k)
  /-- smoothness -/
  contMDiff_g : ∀ x : W, ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (g x)
  /-- on `U x`, the zero set of `g x` is exactly `W` -/
  zero_iff : ∀ (x : W) (y : M), y ∈ U x → (g x y = 0 ↔ y ∈ W)
  /-- `g x` is a submersion at its own centre -/
  isSubmersion_g : ∀ x : W, IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (g x) (x : M)
  /-- at a boundary point of `W`, the restriction of `g x` to `∂M` is a submersion there -/
  bndSubmersion : ∀ (x : W) (hx : (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M),
    IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
      (fun z : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => g x (z : M)) ⟨x, hx⟩

/-- **The local level-set preimage theorem** (the geometric gluing theorem, as a named `Prop`).

A **closed** subset `W` of a compact `T2` smooth `(9+k)`-manifold `M` with boundary which carries
local level-set data (`LocalLevelData k M W`) is a compact `T2` smooth `9`-manifold with boundary,
whose boundary is `W ∩ ∂M`.

(The closedness hypothesis is not redundant: local level-set data alone only makes `W` *locally* a
level set, so an open subset of `M` with `∂M = ∅` satisfies it without being compact — e.g.
`S⁹ ∖ {pt} ⊂ S¹⁰`.  In the application `W = F ⁻¹' X.core` is closed because the core of a
`LocalCoreTarget` is closed, `LocalCoreTarget.isClosed_core`.)

This is `Work.ThomBordism.Transversality.Preimage.exists_preimage_structure` with the *global*
defining function `Φ ∘ F` replaced by the local defining functions of `LocalLevelData`: the charts at
a point `x ∈ W` are built from the submersion normal form of `g x` (`Preimage/Chart.lean`), and the
transition functions are smooth because two local defining functions with the same zero set are
related by a local diffeomorphism along it (`Preimage/Transition.lean`). -/
def LocalLevelPreimageTheorem (k : ℕ) : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M] (W : Set M),
    IsClosed W → LocalLevelData k M W →
    ∃ (W' : Type) (_ : TopologicalSpace W') (_ : ChartedSpace (EuclideanHalfSpace 9) W')
      (_ : IsManifold (𝓡∂ 9) ∞ W') (_ : CompactSpace W') (_ : T2Space W')
      (e : W' ≃ₜ ↥W),
      (∀ w : W', w ∈ (𝓡∂ 9).boundary W' ↔
        (e w : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M ∩ W)

/-! ## From the chart-by-chart transverse map to the local level-set data -/

/-- **The local level-set data of a transverse preimage.**

A smooth map `F : M → X.E` into a `LocalCoreTarget`, transverse to the core (`IsCoreTransverse`) with
boundary transversality (`IsCoreTransverseOnBoundary`), has its core preimage `F ⁻¹' X.core` carrying
local level-set data: at each point `x` of the preimage, `F x` lies in some `locU i`, and the local
defining function is `X.Phi i ∘ F` on the neighbourhood `F ⁻¹' (locU i)`.

Together with `LocalLevelPreimageTheorem` this gives `LocalPreimageTheorem`
(`localPreimageTheorem`). -/
def localLevelData_of_coreTransverse {n k : ℕ} (X : LocalCoreTarget n k) {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X.E)
    (hF : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 n) ∞ F)
    (htr : IsCoreTransverse X (𝓡∂ ((8 + k) + 1)) F)
    (hbnd : IsCoreTransverseOnBoundary X F) :
    LocalLevelData k M (CorePreimage X F) := by
  classical
  -- at a boundary point of the preimage the boundary hypothesis supplies one trivialisation in which
  -- both the map and its boundary restriction are submersions; elsewhere transversality does
  have hchoice : ∀ x : ↥(CorePreimage X F), ∃ (U : Set M) (g : M → EuclideanSpace ℝ (Fin k)),
      IsOpen U ∧ (x : M) ∈ U ∧
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ g ∧
      (∀ y : M, y ∈ U → (g y = 0 ↔ y ∈ CorePreimage X F)) ∧
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ g (x : M) ∧
      (∀ hx : (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M,
        IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
          (fun z : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => g (z : M)) ⟨x, hx⟩) := by
    intro x
    by_cases hx : (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M
    · obtain ⟨i, hiU, hsub1, hsub2⟩ := hbnd x hx x.2
      exact ⟨F ⁻¹' (X.locU i), fun y => X.Phi i (F y),
        (X.isOpen_locU i).preimage hF.continuous, hiU, (X.contMDiff_Phi i).comp hF,
        fun y hy => X.mem_core_iff i (F y) hy, hsub1, fun hy => by
          have h : (⟨x, hy⟩ : ↥((𝓡∂ ((8 + k) + 1)).boundary M)) = ⟨x, hx⟩ := Subtype.ext rfl
          rwa [h]⟩
    · obtain ⟨i, hiU, hsub⟩ := htr x x.2
      exact ⟨F ⁻¹' (X.locU i), fun y => X.Phi i (F y),
        (X.isOpen_locU i).preimage hF.continuous, hiU, (X.contMDiff_Phi i).comp hF,
        fun y hy => X.mem_core_iff i (F y) hy, hsub, fun hy => absurd hy hx⟩
  choose U g hUopen hxU hg_sm hg0 hg_sub hg_bnd using hchoice
  exact { U := U, isOpen_U := hUopen, mem_U := hxU, g := g, contMDiff_g := hg_sm,
          zero_iff := hg0, isSubmersion_g := hg_sub, bndSubmersion := hg_bnd }

/-- **The local preimage theorem** (`Defs.lean`), from the local level-set preimage theorem.

The transverse preimage of the core of a `LocalCoreTarget` is a compact smooth `9`-manifold with
boundary, with boundary the end preimage of the core — obtained by extracting the local level-set data
from the chart-by-chart transversality (`localLevelData_of_coreTransverse`) and applying the geometric
gluing theorem (`LocalLevelPreimageTheorem`). -/
theorem localPreimageTheorem_of_level (h : ∀ k, LocalLevelPreimageTheorem k) :
    LocalPreimageTheorem := by
  intro n k X M _ _ _ _ _ F hF htr hbnd
  have hcl : IsClosed (CorePreimage X F) := X.isClosed_core.preimage hF.continuous
  obtain ⟨W, tW, cW, mW, compW, t2W, e, he⟩ :=
    h k M (CorePreimage X F) hcl (localLevelData_of_coreTransverse X F hF htr hbnd)
  exact ⟨W, tW, cW, mW, compW, t2W, e, fun w => by
    rw [he w, mem_EndPreimage, Set.mem_inter_iff, mem_CorePreimage]⟩

end

end Work.PTGeometric
